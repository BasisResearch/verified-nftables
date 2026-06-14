# `module/` — out-of-tree kernel module

A hello-world external module that proves the development loop: build on the
host against the **custom** kernel tree, load against the running custom kernel
in the VM.

```sh
make kernel                 # once: build the kernel (writes kernel/build.env)
make module                 # build hello.ko against that exact tree
make vm                     # boot the VM (another terminal)
make ssh                    # root shell in the VM
#   inside the VM:
insmod /root/dev/module/hello.ko name=world
dmesg | tail
rmmod hello
```

Because the repo is bind-mounted at `/root/dev` in the VM, the `.ko` you build
on the host appears inside the VM with no copy step.

`make module` targets the kernel source tree recorded in `kernel/build.env`
(`KERNEL_SRC`). The module's vermagic therefore matches the booted kernel and it
loads cleanly — this is the whole reason we build the kernel ourselves instead
of relying on `linux-headers` matching the host.

To start your own module, copy `hello.c`, add it to `obj-m` in the `Makefile`,
and rebuild.
