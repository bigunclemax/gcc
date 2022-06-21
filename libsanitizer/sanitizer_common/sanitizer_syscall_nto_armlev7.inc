//===-- sanitizer_syscall_nto_x86_64.inc ----------------------*- C++ -*-===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Implementation of internal_syscall for nto/armlev7.
// Copyright (c) 2021, QNX Software Systems. All Rights Reserved.
//===----------------------------------------------------------------------===//

#if SANITIZER_QNX

#define __NR_SCHED_YIELD			 90	/* 0x5a */

static uptr internal_syscall(u64 nr) {
	u64 retval;
	asm volatile(
			"stmdb	sp!, {lr};"
			"mov	r12, %1;"
			"swi	#0x51;"
			"ldmia	sp!, {pc};"
			"ldmia	sp!, {pc};"
			: "=g"(retval)
			: "g"(nr) );
	return retval;
}
#endif // SANITIZER_QNX
