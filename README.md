# certified-nft

Formally verifying nftables. Two layers live here:

- **`proof/`** — the verification effort itself: a **Rocq-verified, semantics-preserving
  compiler** from the declarative nftables DSL to the control-plane (netlink) bytecode
  `nft` emits, plus a verified DSL optimizer. Extracted to OCaml and differential-tested
  against the **upstream nftables test corpus** — it reproduces the real tool's bytecode
  on 50% of the corpus's rule-blocks with zero mismatches. Start at
  [proof/DEVELOPMENT.md](proof/DEVELOPMENT.md); build with `cd proof && make corpus`.
- **kernel-dev environment** (below) — the reproducible VM/kernel sandbox for the later
  data-plane (VST) work described in `instructions.org`.

---

# kernel-dev-stub

A reproducible Linux **kernel development environment**: download an upstream
kernel from kernel.org, compile it, and boot it in a lightweight VM where you
can iterate on **out-of-tree modules** *and* **direct kernel patches**.

It is the general-purpose successor to the `certified-nftables` VM setup. That
one avoided a full kernel build by matching the host and guest distro kernel
exactly and compiling modules against `linux-headers` — fast, but it can only
build modules, never a *changed* kernel, and it breaks whenever the host kernel
is upgraded out from under the guest. Here we own the whole kernel instead:

| | certified-nftables | kernel-dev-stub (this) |
|---|---|---|
| Kernel | host distro `linux-lts` | upstream, compiled here |
| Build modules | yes (vs host headers) | yes (vs our tree) |
| Patch the kernel | no | **yes** |
| Survives host kernel upgrade | no (must match) | **yes** (self-contained) |

## What you get

- `kernel/build.sh` — fetches the latest stable kernel from kernel.org (or a
  version you pin), configures it for the VM, builds `bzImage` + modules, and
  stages them for the image. Config in `kernel/config.fragment`.
- `vm/` — an [mkosi](https://github.com/systemd/mkosi) image that boots **our
  compiled kernel** under qemu+KVM, with the repo bind-mounted at `/root/dev`
  and a root shell over vsock via `mkosi ssh` (`vm/run.sh`, `vm/ssh.sh`). The
  image distro follows the host (Arch on Arch, Debian on Debian) — see
  `vm/mkosi.conf.d/`.
- `module/` — a hello-world out-of-tree module proving the build/load loop.
- `patches/` — how to patch the kernel source and rebuild ([patches/README.md](patches/README.md)).

## Quick start

Install host dependencies first — see **[SETUP.md](SETUP.md)** for the full
Arch and Debian/Ubuntu package lists (`make deps` prints them). Then:

```sh
make kernel     # download + compile the kernel (~minutes; incremental after)
make image      # bake the VM image (UKI built from our kernel)
make vm         # boot it — leave running; `poweroff` inside to stop
```

In a second terminal:

```sh
make module     # build module/hello.ko against the compiled kernel
make ssh        # root shell in the VM (over vsock)
#   inside the VM:
insmod /root/dev/module/hello.ko name=world && dmesg | tail -2 && rmmod hello
```

`make test` does that load/unload smoke check non-interactively against a
running VM.

## The two workflows

**Out-of-tree module** — edit `module/`, `make module`, re-`insmod` in the VM.
No image rebuild, no reboot (the repo is bind-mounted). See
[module/README.md](module/README.md).

**Patch the kernel** — edit the source under `kernel/src/linux-*/`,
`make kernel && make image && make vm`. `make kernel` is incremental so a small
change rebuilds fast. Keep edits as patch files in `patches/`. See
[patches/README.md](patches/README.md).

## Layout

```
kernel/   build.sh, config.fragment, build.env (generated), src/ (downloaded)
module/   hello.c + Makefile — out-of-tree module example
patches/  kernel-patch workflow + your *.patch files
vm/       mkosi.conf, run.sh, ssh.sh, mkosi.extra/ (staged kernel+modules)
Makefile  deps / kernel / module / image / vm / ssh / test / clean
SETUP.md  from-scratch recipe + package lists (Arch + Debian/Ubuntu)
```

See **[SETUP.md](SETUP.md)** to stand this up on a fresh machine.
