# SETUP — standing up the kernel-dev environment from scratch

This is the reproducible recipe a future agent (or human) can follow on a clean
machine. It covers host packages for **Arch** (the reference host) and the
**Debian/Ubuntu** equivalents, then the build/boot/test loop.

The design in one sentence: we compile an upstream kernel ourselves and boot it
in an mkosi-built VM under qemu+KVM, so we can build out-of-tree modules **and**
patch the kernel — without the host/guest kernel having to match (the limitation
of the older `linux-headers`-based setup).

> This whole recipe was validated end-to-end on **both** an Arch host and a
> fresh **Debian 13 (trixie)** VM (under nested KVM). The notes below call out
> every Debian/Arch difference found while doing that.

---

## 1. Host packages

You need: a C toolchain + the kernel's build-time helpers, and the VM tooling
(mkosi, qemu, virtiofsd, ukify, socat). `make deps` prints these.

### Arch

```sh
sudo pacman -S --needed \
    base-devel bc flex bison openssl libelf pahole cpio perl zstd git curl \
    mkosi qemu-base virtiofsd systemd-ukify python-pefile socat
sudo modprobe vhost_vsock      # vsock for 'mkosi ssh' (add to /etc/modules-load.d to persist)
```

- `base-devel` provides gcc/make/etc. `bc flex bison openssl libelf pahole cpio
  perl` are the kernel's documented build dependencies (`Documentation/process/changes.rst`).
  **`bc` in particular is easy to miss and the build fails without it.**
- `pahole` is only needed if you enable `CONFIG_DEBUG_INFO_BTF`; our
  `kernel/config.fragment` turns BTF **off**, so you can skip it if you keep
  that default.
- `qemu-base` includes `qemu-system-x86_64` (the VM backend); `virtiofsd` backs
  the `/root/dev` bind mount; `systemd-ukify` + `python-pefile` build the UKI;
  `socat` is what `mkosi ssh` uses to reach the VM over vsock.
- We use the **qemu** VM backend, not `systemd-vmspawn`, so vmspawn is not
  required (and notably is not packaged on Debian — see below).

### Debian / Ubuntu

(The eventual deployment target. Validated on Debian 13 **trixie**; package
names below are the ones that actually worked.)

```sh
sudo apt update
sudo apt install \
    build-essential bc flex bison libssl-dev libelf-dev pahole cpio perl \
    zstd git curl \
    mkosi mmdebstrap qemu-system-x86 virtiofsd systemd-ukify python3-pefile socat
sudo modprobe vhost_vsock
```

Notes for Debian/Ubuntu (each one was a real difference hit during validation):
- Kernel build deps map: `openssl`→`libssl-dev`, `libelf`→`libelf-dev`,
  `base-devel`→`build-essential`. `pahole` exists as a real package on trixie
  (no need for `dwarves`); it's optional anyway (BTF off by default).
- **`mmdebstrap`** is required: it's the backend mkosi uses to bootstrap a
  Debian/Ubuntu image. Without it `make image` can't build the rootfs.
- **`socat`** is required for `mkosi ssh` (the vsock transport). On Debian it may
  come in via dependencies, but install it explicitly to be safe.
- `virtiofsd` is a separate package (the Rust daemon); the binary lives at
  `/usr/libexec/virtiofsd` (off `$PATH`) — mkosi finds it itself.
- **`systemd-vmspawn` is NOT packaged on Debian trixie** (it's not in
  `systemd-container`). This is exactly why the VM backend here is qemu, not
  vmspawn — so nothing extra is needed.
- Building a **Debian image** needs no edits: mkosi defaults the image
  distribution to the host, and `vm/mkosi.conf.d/debian.conf` supplies the
  Debian package list automatically. (To cross-build a Debian image on an Arch
  host, run `mkosi -d debian -r trixie ...` and install `mmdebstrap`.)

### Verify the host is ready

```sh
make deps          # prints the package lines above
for t in gcc make bc flex bison mkosi qemu-system-x86_64 ukify socat; do command -v $t; done
which virtiofsd || ls /usr/lib/virtiofsd /usr/libexec/virtiofsd   # off-PATH; mkosi finds it
lsmod | grep vhost_vsock
```

---

## 2. Build the kernel

```sh
make kernel                 # latest stable from kernel.org
#   or pin a version (e.g. an LTS that matches your host closely):
make kernel KVER=6.18.35
```

`kernel/build.sh`:
1. resolves the version (arg / `$KVER` / kernel.org `latest_stable`),
2. downloads + sha256-verifies the tarball into `kernel/src/` (cached),
3. configures: `defconfig` + `kvm_guest.config` + `kernel/config.fragment`,
4. builds `bzImage` + modules across all cores,
5. stages `vmlinuz` + modules into `vm/mkosi.extra/usr/lib/modules/<release>/`,
6. writes `kernel/build.env` (consumed by the Makefile, the module build, vm).

First build is the slow one (minutes). It is incremental afterward: editing the
source and re-running `make kernel` recompiles only what changed.

**Choosing a version.** `make kernel` defaults to the latest *stable*. For a
stable dev base, pin an **LTS** (`make kernel KVER=6.18.35`) — longterm kernels
get fixes for years and tend to be less surprising than a brand-new `.0`.

**What the config does.** `config.fragment` forces the virtio devices, virtiofs,
9p, vsock, ext4/overlay and the consoles to be **built in** (`=y`) so the kernel
boots with a trivial initrd and no out-of-tree drivers, while keeping
`CONFIG_MODULES=y` so you can still `insmod` your own modules. Add any subsystem
you want to hack on there.

---

## 3. Build the VM image

```sh
make image
```

mkosi builds a runtime-only rootfs (no kernel package, no toolchain), copies in
the staged `vmlinuz` + modules, and turns them into a UKI (`Bootloader=uki`)
that qemu direct-boots. The image distribution defaults to the **host** distro;
the package list comes from `vm/mkosi.conf.d/{arch,debian}.conf`. Re-run after
`make kernel` (new vmlinuz) or after editing the mkosi config. **Not** needed
for module-only changes.

`make image` also runs `mkosi genkey` on first use to create the SSH key pair
(`vm/mkosi.key` / `.crt`, git-ignored) that `mkosi ssh` uses, and two image
tweaks that make `mkosi ssh` work across distros (see §5): `vm/mkosi.postinst`
bakes SSH host keys, and `vm/mkosi.extra/.../sshd-vsock.socket` masks the
distro's own vsock-ssh socket so it doesn't collide with mkosi's.

---

## 4. Boot + the dev loop

```sh
make vm        # terminal A: boots the VM; `poweroff` inside to stop
```

```sh
make ssh             # terminal B: root shell over vsock (wraps `mkosi ssh`)
#   or one-shot:
make ssh uname -a    #   -> Linux devkernel 7.1.0 ...   (our compiled kernel)
```

`make vm` uses qemu's native console, so run it in a real terminal (it needs a
tty). `poweroff` inside to stop it; `Ctrl-A X` kills qemu.

### Out-of-tree module

```sh
make module                                 # build module/hello.ko vs our tree
make ssh                                     # in the VM:
insmod /root/dev/module/hello.ko name=world  #   repo is bind-mounted at /root/dev
dmesg | tail -2
rmmod hello
```

No reboot, no image rebuild — `/root/dev` is the live repo over virtiofs.
`make test` runs this load/dmesg/unload check non-interactively.

### Patch the kernel

Edit the source under `kernel/src/linux-*/`, then:

```sh
make kernel && make image && make vm
```

Keep edits as patch files in `patches/` so the (git-ignored, re-downloadable)
source tree stays reproducible — see [patches/README.md](patches/README.md).

---

## 5. How the pieces fit (and why)

```
  kernel/build.sh ──► kernel/src/linux-X.Y/  ──►  bzImage + modules
        │                                              │
        │ writes kernel/build.env (KERNEL_SRC,         │ staged into
        │ KERNEL_RELEASE, BZIMAGE)                     ▼
        │                              vm/mkosi.extra/usr/lib/modules/<rel>/
        ▼                                              │  vmlinuz + *.ko
  module/  ── built against KERNEL_SRC ──► hello.ko    │
        │   (vermagic matches the booted kernel)       ▼
        │                                  mkosi build ──► UKI ──► qemu+KVM
        └──────────── bind-mounted at /root/dev ───────────────►  VM (kernel 7.1.0)
```

Key invariant: the module is built against the **same tree** that produced the
booted kernel, so vermagic matches and it loads. That is what frees us from the
"host headers must match the guest kernel" constraint of the old setup.

### Why qemu + `mkosi ssh`, and the two cross-distro fixes

The older setup used `systemd-vmspawn`. We switched to mkosi's **qemu** backend
because vmspawn isn't packaged on Debian. `mkosi ssh` then connects over vsock
using a key from `mkosi genkey`. Two things were needed to make that reliable on
**both** distros (both committed in the repo, no user action):

1. **SSH host keys** (`vm/mkosi.postinst` runs `ssh-keygen -A` in the image).
   mkosi's socket-activated sshd wires host-key generation to
   `sshd-keygen.target`, which Debian's `openssh-server` provides but Arch's
   `openssh` does not — so on Arch, sshd would start with no host keys and every
   connection died with `sshd: no hostkeys available -- exiting`.
2. **A socket mask** (`vm/mkosi.extra/etc/systemd/system/sshd-vsock.socket` → 
   `/dev/null`). Arch's openssh ships a `systemd-ssh-generator` that creates its
   own `sshd-vsock.socket` on vsock:22, colliding with mkosi's `ssh.socket`; the
   failure cascaded to tear down mkosi's working socket. Masking the distro one
   leaves mkosi's in sole charge. (Harmless on Debian, which has no such unit.)

---

## 6. Troubleshooting

- **`bc: command not found` during `make kernel`** — install `bc` (Arch:
  `sudo pacman -S bc`; Debian: `sudo apt install bc`). It's a kernel build dep.
- **VM stops at "Please configure the system!"** — first-boot prompt; the image
  pre-seeds `Locale`/`Timezone`/`Hostname` in `vm/mkosi.conf` to avoid it. If
  you removed those, add them back and `make image`.
- **`make ssh` returns nothing / hangs** — the VM must be running (`make vm` in
  another terminal), the host needs `vhost_vsock` (`sudo modprobe vhost_vsock`)
  and `socat` installed. If you see `sshd: no hostkeys available` in the VM's
  journal, the host-key bake (`vm/mkosi.postinst`) didn't run — rebuild the image.
- **`exec: socat: not found`** — install `socat`; `mkosi ssh` shells out to it
  for the vsock proxy.
- **`mkosi ssh`: `No such file … /run/user/<uid>/mkosi/machine`** — `mkosi vm`
  and `mkosi ssh` must run in the **same login session**: `mkosi vm` stores the
  machine state under `$XDG_RUNTIME_DIR` (`/run/user/<uid>`), which systemd tears
  down when your last session for that user ends. Normal desktop terminals share
  one session, so this is a non-issue there. On a headless box where you SSH in
  twice, either keep both in one session (tmux) or run
  `loginctl enable-linger <user>` so the runtime dir persists.
- **`make image` fails on Debian with "Cannot find ... mmdebstrap"** — install
  `mmdebstrap` (mkosi's Debian bootstrap backend).
- **`make image` fails: "systemd-stub not found … linuxx64.efi.stub"** (Debian)
  — the EFI stub is split out; `vm/mkosi.conf.d/debian.conf` pulls in
  `systemd-boot-efi` + `systemd-ukify`. Make sure that drop-in applied (`mkosi
  summary | grep -i systemd-boot-efi`).
- **`Could not find 'systemd-vmspawn'`** — you're on a config that still selects
  the vmspawn backend. This setup uses `VirtualMachineMonitor=qemu`; vmspawn is
  not needed (and not on Debian).
- **`mkosi vm` errors about `systemd-pty-forward`** — that's only needed by the
  `interactive`/`read-only` consoles; the config uses `Console=native`, which
  works everywhere. Run `make vm` in a real terminal (native console needs a tty).
- **VM stops at "Please configure the system!"** — first-boot prompt; the image
  pre-seeds `Locale`/`Timezone`/`Hostname` in `vm/mkosi.conf`. Also requires the
  kernel's `CONFIG_DMI_SYSFS`/`CONFIG_FW_CFG_SYSFS` (in `config.fragment`) so the
  guest can read the injected credentials.
- **Module won't load (`version magic` mismatch)** — you rebuilt the kernel but
  loaded an old `.ko` (or vice versa). Rebuild both: `make kernel module`, and
  make sure the running VM is the freshly imaged one.
- **`mkosi` can't find the kernel** — confirm `make kernel` populated
  `vm/mkosi.extra/usr/lib/modules/<rel>/vmlinuz`; mkosi discovers the kernel
  from that path.
- **No virtiofsd** — install it; the binary is `/usr/lib/virtiofsd` (Arch) or
  `/usr/libexec/virtiofsd` (Debian), off `$PATH`; mkosi finds it itself.
