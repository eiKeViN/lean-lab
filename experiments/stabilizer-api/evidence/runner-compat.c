#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

/* The managed executor can expose a /proc PID namespace different from getpid().
 * Resolve only this process's executable query through /proc/self/exe. */
ssize_t readlink(const char *path, char *buf, size_t len) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char current[64];
  snprintf(current, sizeof(current), "/proc/%ld/exe", (long)getpid());
  if (!strcmp(path, current)) return original("/proc/self/exe", buf, len);
  return original(path, buf, len);
}
