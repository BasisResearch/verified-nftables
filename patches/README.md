# `patches/` — patching the kernel itself

The other half of the workflow: changing the kernel source directly (a new
syscall, a netfilter tweak, an exported symbol, a printk) and booting the
result. Unlike an out-of-tree module, this rebuilds and reboots the kernel.

## Quick loop

The kernel source lives at the path in `kernel/build.env` (`KERNEL_SRC`,
e.g. `kernel/src/linux-7.1/`). Edit it directly, then:

```sh
make kernel     # incremental: only changed objects recompile, re-stages vmlinuz
make image      # re-bake the VM image (re-builds the UKI from the new kernel)
make vm         # boot the patched kernel
```

`make kernel` is incremental, so after the first full build a one-line change
recompiles in seconds.

## Keeping changes as patch files

So the tree stays reproducible (it is git-ignored and re-downloaded by
`build.sh`), capture your edits as patches and keep them here:

```sh
cd kernel/src/linux-7.1
git init -q && git add -A && git commit -qm base    # snapshot the pristine tree
#   ... make your edits ...
git diff > ../../../patches/0001-my-change.patch
```

To re-apply after a fresh `make kernel` (or on another machine):

```sh
cd kernel/src/linux-7.1
patch -p1 < ../../../patches/0001-my-change.patch
```

You can also automate this: drop `*.patch` files here and they will be applied
in order if you uncomment the patch-application block in `kernel/build.sh`
(search for "patches/"), or apply them by hand as above.

## Verifying a patch took effect

Boot the VM and check from inside (`make ssh`):

```sh
uname -a                 # confirms the release string / build date
dmesg | grep <your printk>
cat /proc/version
```
