# kernel-dev-stub — convenience wrapper. See README.md / SETUP.md for details.
#
# Typical loops (two terminals):
#
#   External module:                Patching the kernel:
#     make kernel    # once           make kernel    # rebuild (incremental)
#     make image     # once           make image
#     make vm        # terminal A      make vm
#     make module    # terminal B      (reboot picks up the new kernel)
#     make ssh       # load & test
#
# All artifacts build on the HOST; the VM is runtime-only and bind-mounts this
# repo at /root/dev, so host-built outputs appear inside with no copy step.

.PHONY: all deps kernel module image vm ssh test clean clean-image distclean

all: kernel module

# Print the host packages you need (kernel build + mkosi VM). Installation needs
# root, so we don't run it for you — copy the line for your distro.
deps:
	@echo "Arch:"
	@echo "  sudo pacman -S --needed base-devel bc flex bison openssl libelf \\"
	@echo "      pahole cpio perl zstd git curl mkosi qemu-base virtiofsd \\"
	@echo "      systemd-ukify python-pefile socat"
	@echo "  sudo modprobe vhost_vsock      # vsock for 'mkosi ssh' into the VM"
	@echo
	@echo "Debian/Ubuntu:"
	@echo "  sudo apt install build-essential bc flex bison libssl-dev libelf-dev \\"
	@echo "      pahole cpio perl zstd git curl mkosi mmdebstrap qemu-system-x86 \\"
	@echo "      virtiofsd systemd-ukify python3-pefile socat"
	@echo "  sudo modprobe vhost_vsock"
	@echo
	@echo "  (socat = 'mkosi ssh' transport; mmdebstrap = mkosi's Debian image"
	@echo "   bootstrap. qemu+KVM is the VM backend, so systemd-vmspawn is NOT needed"
	@echo "   — which is good, since Debian trixie doesn't package it.)"

# Download + configure + build the upstream kernel; stage vmlinuz+modules into
# the image tree and write kernel/build.env.  KVER=x.y.z to pin a version.
kernel:
	./kernel/build.sh $(KVER)

# Build the out-of-tree example module against the kernel tree from build.env.
module:
	$(MAKE) -C module

# (Re)build the VM image with mkosi. Run after `make kernel` (new vmlinuz) or
# after editing mkosi.conf. NOT needed for module-only changes (bind-mounted).
image:
	cd vm && { [ -f mkosi.key ] || { echo ">> generating mkosi ssh key (one-time)"; mkosi genkey; }; } && mkosi -f build

# Boot the VM (takes over this terminal; `poweroff` inside to exit).
vm:
	./vm/run.sh

# Open a root shell in the already-running VM (boot it with `make vm` first).
ssh:
	./vm/ssh.sh

# Smoke test: build the module, then (VM must be running) load it and show dmesg.
test: module
	./vm/ssh.sh 'insmod /root/dev/module/hello.ko name=ci; dmesg | tail -3; rmmod hello'

# Remove host build artifacts (kernel objects + module). Keeps the downloaded
# source tree and the VM image.
clean:
	$(MAKE) -C module clean
	-[ -f kernel/build.env ] && . ./kernel/build.env && $(MAKE) -C "$$KERNEL_SRC" clean || true

# Drop the built VM image (force a fresh `make image`).
clean-image:
	rm -rf vm/mkosi.output vm/.mkosi-private

# Nuke everything regenerable: kernel source/build, staged modules, image.
distclean: clean-image
	rm -rf kernel/src kernel/build.env vm/mkosi.extra/usr
