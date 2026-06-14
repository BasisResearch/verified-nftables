The goal is for you to set up a Linux kernel development environment that allows you to quickly compile and test kernel patches or modules.

You should base off of the setup in ~/Experiments/certified-nftables but make it more general, as described below.

First, the certified-nftables development relies on a hack to avoid building the entire kernel from scratch by matching the host and guest OS exactly and compiling modules from linux-headers. This is not flexible enough when you genuinely want a patched kernel. You should download the latest release from kernel.org, compile the entire kernel, and be able to boot from that using mkosi or vmspawn. This lets you both write external kernel modules and directly patch the kernel.

Second, you should closely document the steps. The goal is not for you to create an ad-hoc environment but to produce a recipe that future agents can read and set up a new development environment from scratch. Ideally, you should document the packages that need to be installed. My host system is Arch Linux, but consider figuring out the equivalent packages for Ubuntu or Debian, which is where I eventually plan to run this whole setup.
