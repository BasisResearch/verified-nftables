// SPDX-License-Identifier: GPL-2.0
/*
 * hello.c — minimal external (out-of-tree) kernel module.
 *
 * Proves the dev loop end to end: it is built on the HOST against the exact
 * kernel source tree we compiled (so its vermagic matches), bind-mounted into
 * the VM, and loaded against the running custom kernel. Replace this with your
 * own module; the Makefile next to it is all you need.
 *
 *   insmod  hello.ko name=world   # -> dmesg: "hello: hello, world ..."
 *   rmmod   hello                 # -> dmesg: "hello: goodbye"
 */
#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/utsname.h>

static char *name = "kernel-dev-stub";
module_param(name, charp, 0444);
MODULE_PARM_DESC(name, "who to greet");

static int __init hello_init(void)
{
	pr_info("hello: hello, %s -- running on kernel %s\n", name, init_utsname()->release);
	return 0;
}

static void __exit hello_exit(void)
{
	pr_info("hello: goodbye\n");
}

module_init(hello_init);
module_exit(hello_exit);

MODULE_LICENSE("GPL");
MODULE_AUTHOR("kernel-dev-stub");
MODULE_DESCRIPTION("Hello-world module proving the out-of-tree build/load loop");
