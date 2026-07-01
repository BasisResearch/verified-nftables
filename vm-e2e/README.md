# vm-e2e — end-to-end test of the verified `nftc` CLI against a real kernel

This is a **separate** mkosi setup from `vm/`. `vm/` direct-boots a *custom,
hand-compiled* kernel (for kernel hacking). This one boots a **packaged, stock
distro kernel** so we can drive the verified `nftc` CLI end-to-end against a
real Linux netfilter stack — no kernel build involved.

## Run it

```
make vmtest          # from the repo root
```

That runs `vm-e2e/vmtest.sh`, which:

1. builds the host CLI (`make -C proof cli`),
2. bakes the CLI + rulesets + the battery into `mkosi.extra/`,
3. builds a rootless mkosi image (`mkosi -f build`),
4. boots it under qemu+KVM and runs `e2e-battery.sh` inside over `mkosi ssh`,
5. powers the VM down. Exit 0 iff every check passed.

`make vmtest-clean` drops the image to force a fresh build.

## What the battery checks (`e2e-battery.sh`)

For a battery of rulesets (`rules/*.nft` plus the repo's `router.nft`,
`ruleset.nft`, `optiplex.nft`) it runs `nftc compile`, `nftc optimize` and
`nftc send --commit`, then reads the result back with `nft list ruleset` to
confirm the kernel *accepted* the batch. It also confirms real packets *match*
(runtime counters: a loopback ping and an established loopback TCP connection),
checks the exit-code + atomicity contract (a kernel-rejected batch exits
non-zero and rolls back), and probes CLI robustness (missing/empty/garbage file,
a directory, an unsupported construct, `--help`, stdin `-`, bad flags).

## Rootless / host-environment engineering

The host has no passwordless sudo and is missing some tooling; the config is
shaped to boot anyway, entirely unprivileged:

- **Rootless build.** `mkosi build` runs in a user namespace using the host's
  `/etc/subuid`+`/etc/subgid` ranges; `mkosi vm` uses KVM via a world-rw
  `/dev/kvm`. No root.
- **`Format=disk`, not `directory`.** A `mkosi vm` *directory* boot presents the
  rootfs with **virtiofsd**, which is not installed. A GPT disk is a plain
  virtio-blk device — no virtiofsd.
- **Direct kernel boot (`Firmware=linux`), no ESP.** An ESP/UKI boot needs
  `mkfs.vfat` (dosfstools), which is absent and can't be sudo-installed. `mkosi
  vm` instead boots the packaged `vmlinuz` + its initrd directly via qemu
  `-kernel`; `systemd-gpt-auto` finds the `Type=root` partition. (An earlier
  UEFI attempt also tripped over mkosi auto-selecting the *secure-boot* OVMF,
  which rejects our unsigned UKI — direct boot sidesteps that too.)
- **Baked-in artifacts, no bind mount.** With virtiofsd gone there is no
  `RuntimeTrees` bind mount, so the host-built `nftc` binary, the rulesets and
  the battery are staged into `mkosi.extra/` and baked into the image. The image
  is Arch (host-distro default), so the native OCaml binary's libc matches.
