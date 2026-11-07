#ifndef FASTMUL_BOUNDED_CHIRP_PROCESS_LIMITS_HPP
#define FASTMUL_BOUNDED_CHIRP_PROCESS_LIMITS_HPP
// AUDIT-SIDE SUBSTITUTION (not the author's file).
// The shipped guard installs a Windows job object (64 MiB + 10 CPU-seconds) and
// is a no-op off Windows, so the probe refuses to run on POSIX (exit 2).
// This replacement installs the same CPU-seconds limit via POSIX rlimits and
// returns true. macOS rejects both RLIMIT_AS and RLIMIT_DATA with EINVAL
// (measured), so the memory limit is not reproducible off Windows; the probe
// uses fixed-size static arrays and is run under a 5-second wall timeout
// instead, exactly as CERTIFICATES.txt prescribes.
#include <sys/resource.h>
inline bool install_chirp_process_limits(){
  struct rlimit cpu;
  cpu.rlim_cur = 10; cpu.rlim_max = 10;
  return setrlimit(RLIMIT_CPU, &cpu) == 0;
}
#endif
