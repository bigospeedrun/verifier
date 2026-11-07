// AUDIT-SIDE DECLARATIONS-ONLY SHIM. Not part of the author's package.
// frozen_rectangles.cpp -> four_bank_five_stage_word_bounded_20261030.cpp
// #includes <windows.h>/<psapi.h> unconditionally for a guard() function that
// probe 2 explicitly never calls ((void)&guard). These declarations let the
// translation unit compile on POSIX; no Windows runtime call is ever executed.
#pragma once
#include <cstddef>
typedef void* HANDLE;
typedef unsigned long DWORD;
typedef long long LONGLONG;
union LARGE_INTEGER { struct { DWORD LowPart; long HighPart; } u; LONGLONG QuadPart; };
struct JOBOBJECT_BASIC_LIMIT_INFORMATION {
  LARGE_INTEGER PerProcessUserTimeLimit;
  LARGE_INTEGER PerJobUserTimeLimit;
  DWORD LimitFlags;
  std::size_t MinimumWorkingSetSize, MaximumWorkingSetSize;
  DWORD ActiveProcessLimit;
  std::size_t Affinity;
  DWORD PriorityClass, SchedulingClass;
};
struct IO_COUNTERS { unsigned long long a,b,c,d,e,f; };
struct JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
  JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
  IO_COUNTERS IoInfo;
  std::size_t ProcessMemoryLimit, JobMemoryLimit, PeakProcessMemoryUsed, PeakJobMemoryUsed;
};
enum { JOB_OBJECT_LIMIT_PROCESS_TIME = 0x2, JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x100,
       JobObjectExtendedLimitInformation = 9 };
inline HANDLE CreateJobObjectW(void*, const wchar_t*) { return nullptr; }
inline bool SetInformationJobObject(HANDLE, int, void*, unsigned long) { return false; }
inline bool AssignProcessToJobObject(HANDLE, HANDLE) { return false; }
inline HANDLE GetCurrentProcess() { return nullptr; }
