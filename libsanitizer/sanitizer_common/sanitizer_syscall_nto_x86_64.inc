//===-- sanitizer_syscall_nto_x86_64.inc ----------------------*- C++ -*-===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Implementation of internal_syscall for nto/x86_64.
// Copyright (c) 2021, QNX Software Systems. All Rights Reserved.
//===----------------------------------------------------------------------===//

#if SANITIZER_QNX

#define __NR_SCHED_YIELD			 90	/* 0x5a */

static uptr internal_syscall(u64 nr) {
	u64 retval;
	asm volatile( "syscall;" /* invoke the syscall */
			"ret;"
			: "=a"(retval)   /* return value goes from RAX to retval */
			: "a"(nr)        /* the argument list and mapping */
			: "rcx", "r11", "memory", "cc");
                             /* clobbered data */
	return retval;
}
#endif // SANITIZER_QNX
