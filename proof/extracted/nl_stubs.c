/* nl_stubs.c — the one piece of C the netlink sender needs: open an
   AF_NETLINK / NETLINK_NETFILTER (nfnetlink) socket, which OCaml's Unix
   module cannot create itself.  Everything else (the byte encoding, the
   write/read, the ACK parsing) lives in untrusted OCaml (nl_send.ml).

   This is transport glue, NOT part of the verified TCB. */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/fail.h>

#include <sys/socket.h>
#include <linux/netlink.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>

#ifndef NETLINK_NETFILTER
#define NETLINK_NETFILTER 12
#endif

/* nl_open : unit -> Unix.file_descr
   socket(AF_NETLINK, SOCK_RAW, NETLINK_NETFILTER) + bind(nl_pid=0 => kernel
   auto-assigns a unique portid, nl_groups=0).  Unix.file_descr is an immediate
   int on Unix, so we hand back the raw fd via Val_int. */
CAMLprim value caml_nl_open(value unit)
{
  CAMLparam1(unit);
  int fd = socket(AF_NETLINK, SOCK_RAW, NETLINK_NETFILTER);
  if (fd < 0)
    caml_failwith(strerror(errno));

  struct sockaddr_nl addr;
  memset(&addr, 0, sizeof(addr));
  addr.nl_family = AF_NETLINK;
  addr.nl_pid    = 0;   /* let the kernel pick the portid */
  addr.nl_groups = 0;

  if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    int e = errno;
    close(fd);
    caml_failwith(strerror(e));
  }

  /* Ask the kernel for extended ACKs: on rejection it then appends a
     human-readable NLMSGERR_ATTR_MSG (and the offending attribute offset),
     which nl_send.ml surfaces to the user.  Best-effort: ignore failure on
     kernels too old to support it. */
#ifndef NETLINK_EXT_ACK
#define NETLINK_EXT_ACK 11
#endif
  {
    int on = 1;
    (void)setsockopt(fd, SOL_NETLINK, NETLINK_EXT_ACK, &on, sizeof(on));
  }
  CAMLreturn(Val_int(fd));
}
