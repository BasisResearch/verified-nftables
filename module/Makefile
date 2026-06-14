# Out-of-tree kernel module build.
#
# Built on the HOST against the kernel source tree compiled by kernel/build.sh
# (NOT against the host's /lib/modules — that is the whole point: we target the
# custom kernel, not the distro one). KDIR is read from kernel/build.env, which
# build.sh writes; override it to build against any other prepared tree:
#
#   make                              # uses kernel/build.env
#   make KDIR=/path/to/linux-x.y.z    # explicit tree
#
# The resulting hello.ko is loaded inside the VM (the repo is bind-mounted), so
# no copy step is needed:  insmod /root/dev/module/hello.ko

obj-m := hello.o

# Pull KERNEL_SRC from kernel/build.env if present; allow KDIR to override.
BUILD_ENV := $(wildcard $(CURDIR)/../kernel/build.env)
ifneq ($(BUILD_ENV),)
  include $(BUILD_ENV)
endif
KDIR ?= $(KERNEL_SRC)

# Fall back to the running kernel's build tree only if nothing else is set, so
# `make` still does something sane outside this repo.
ifeq ($(strip $(KDIR)),)
  KDIR := /lib/modules/$(shell uname -r)/build
endif

PWD := $(CURDIR)

.PHONY: all clean
all:
	@test -d "$(KDIR)" || { echo "KDIR '$(KDIR)' not found — run 'make kernel' first"; exit 1; }
	$(MAKE) -C "$(KDIR)" M=$(PWD) modules

clean:
	-$(MAKE) -C "$(KDIR)" M=$(PWD) clean 2>/dev/null || rm -f *.o *.ko *.mod *.mod.c .*.cmd modules.order Module.symvers
