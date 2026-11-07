# Disclosed substitutions for the author's Windows-only certificate probes

These files are **audit-authored, not the author's**, and they are the only reason
the two finite certificate probes can run on a non-Windows machine. No certificate
logic is changed: every substitution touches process-limit setup only.

| File | Replaces | Why |
|---|---|---|
| `bounded_chirp_process_limits.hpp` | `checks/bounded_chirp_process_limits.hpp` | The shipped guard creates a Win32 job object (64 MiB, 10 CPU-seconds) and returns `false` off Windows. Both probes **fail closed** on `false`: probe 1 `main()` returns 2 (`REFUSED: required job unavailable`), probe 2's static `EarlyGuard` calls `ExitProcess(2)`. The replacement installs `RLIMIT_CPU = 10 s` and returns `true`. |
| `windows.h`, `psapi.h` | `<windows.h>`, `<psapi.h>` | Probe 2 transitively includes `four_bank_five_stage_word_bounded_20261030.cpp`, which does `#include <windows.h>` / `<psapi.h>` unconditionally (line 5-6) for a `guard()` function probe 2 explicitly never calls (`(void)&guard;`). Declarations only; no Windows call is ever executed. |
| (one-line edit) | `checks/probes/frozen_rectangles.cpp` | Its static `EarlyGuard` calls `ExitProcess(2)`; replaced by `std::_Exit(2)`, the POSIX equivalent from a constructor (no unwinding). Applied by `reproduce_probes.sh`, not carried as a file. |

**Memory limit, honestly.** macOS rejects both `RLIMIT_AS` and `RLIMIT_DATA` with
`EINVAL` (measured on this machine), so the 64 MiB address-space cap is **not**
reproduced here. The probes use fixed-size static arrays, and `reproduce_probes.sh`
runs each under the 5-second wall timeout that `CERTIFICATES.txt` prescribes, so the
practical guard against a runaway is retained but it is *not* the author's guard.

**Result.** With these substitutions both probes reproduce their published expected
outputs byte-for-byte — 2012 bytes and 65933 bytes — on macOS/arm64 with Apple clang
21. That is the strongest check available without Windows, and it also shows the
published numbers are compiler- and platform-independent. It is **not** a proof that
the probes' internal algebra is the right model of the construction, and it is not a
reproduction of the author's guard, which remains Windows-only as shipped.
