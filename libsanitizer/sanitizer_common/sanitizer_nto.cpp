//===-- sanitizer_nto.cc ------------------------------------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is shared between AddressSanitizer and ThreadSanitizer
// run-time libraries and implements Neutrino-specific functions from
// sanitizer_libc.h.
// Copyright (c) 2021, QNX Software Systems. All Rights Reserved.
//===----------------------------------------------------------------------===//

#include "sanitizer_platform.h"

#if SANITIZER_QNX

#include "sanitizer_common.h"
#include "sanitizer_flags.h"
#include "sanitizer_internal_defs.h"
#include "sanitizer_libc.h"
#include "sanitizer_linux.h"
#include "sanitizer_mutex.h"
#include "sanitizer_placement_new.h"
#include "sanitizer_procmaps.h"
#include "sanitizer_stacktrace.h"
#include "sanitizer_symbolizer.h"

#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <ucontext.h>
#include <unistd.h>

#include <sys/debug.h>
#include <sys/iomsg.h>
#include <sys/memmsg.h>
#include <sys/procfs.h>
#include <sys/procmsg.h>
#include <sys/netmgr.h>
#include <sys/pathmsg.h>
#include <devctl.h>
#include <stdarg.h>
#include <stdlib.h>
#include <share.h>
#include <cstdio>

/* fetch the NTO internal TLS */
#if defined(__X86_64__)
static __inline__ struct _thread_local_storage * __attribute__((__unused__,__const__)) LIBC_TLS(void) {
	register struct _thread_local_storage		*__p;
	__asm__ (
			"movq %%fs:56,%0"
			: "=r" (__p):);
	return __p;
}
#elif defined(__ARM__)
static __inline__ struct _thread_local_storage * __attribute__((__unused__,__const__)) LIBC_TLS(void) {
	struct _thread_local_storage		*__p;
	__asm__ __volatile__("mrc		p15, 0, %0, c13, c0, 3" : "=r"(__p));
	return __p;
}
#elif defined(__aarch64__)
static __inline__ struct _thread_local_storage * __attribute__((__unused__,__const__)) LIBC_TLS(void) {
	struct _thread_local_storage		*__p;
	__asm__ __volatile__("mrs	%0, tpidrro_el0" : "=r"(__p));
	return __p;
}
#else
#error Unsupported architecture!
#endif

#if __SIZEOF_SIZE_T__ > 4
#define SIZET_VAL_GET_HI32(t) (uint32_t)((t) >> 32)
#else
#define SIZET_VAL_GET_HI32(t) 0
#endif

/**
 * prototypes for the connect_attach functions
 */
static int _connect_ctrl(struct _connect_ctrl *ctrl, const char *path,
		unsigned response_len, void *response);

#define MIN_FILLER_SIZE (sizeof(struct _io_connect_entry) * 3 * SYMLOOP_MAX + PATH_MAX + 1)
/* Flags used in the connect_ctrl structure */

struct _connect_ctrl {
	int base;
	struct _io_connect *msg;
	union _io_connect_reply_type {
		struct _io_connect_link_reply link;
		struct _io_connect_ftype_reply ftype;
	} *reply;
	struct _io_connect_entry *entry;
	const void *extra;
	int status;
	void *response;
	long (*send)(int coid, const iov_t *smsg, _Sizet sparts,
			const iov_t *rmsg, _Sizet rparts);
	int flags;
	char *path;
	int pathsize;
	int pathlen;
	int prefix_len;

	uint16_t fds_len;
	uint16_t fds_index;
	int *fds;
	int response_len;
	uint32_t nd;
	size_t chroot_len;
};

static int _errno = 0;
struct _cl_buffer {
	struct _io_connect_link_reply reply;
	char filler[MIN_FILLER_SIZE];
};

#ifndef max
# define max(a,b) (((a) < (b))?(b):(a))
#endif
#ifndef min
# define min(a,b) (((a)<(b)) ? (a) : (b))
#endif

#if SANITIZER_USE_GETAUXVAL
#include <sys/auxv.h>
#endif

#if defined(__x86_64__)
extern "C" {
extern void internal_sigreturn();
}
#endif

static debug_thread_t *__procinfo = NULL;

#define OFLAG (O_NONBLOCK | O_NOCTTY | O_LARGEFILE)

/**
 * Common implementation for the various forms of stat().
 * @param   path        The path to query
 * @param   statp       Structure to populate
 * @param   stat_size   Structure size
 * @param   mode        0 or S_IFLNK to query the destination file or source
 *                      file, respectively, in case of a symbolic link
 * @param   dirfd       AT_FDCWD or a file descriptor for a directory opened
 *                      with O_DIRECTORY
 * @return  0 if successful, -1 otherwise
 */
static int _stat(char const *const path, struct stat *const statp,
		size_t const stat_size, int const mode, int const dirfd) {
	const struct _io_stat iostat = { _IO_STAT, sizeof(struct _io_stat),
			_STAT_FORM_PREFERRED };

	struct _connect_ctrl ctrl;
	struct _io_connect msg;
	int fd;

	memset(&ctrl, 0x00, sizeof(ctrl));
	ctrl.base = _NTO_SIDE_CHANNEL;
	ctrl.extra = &iostat;
	ctrl.send = MsgSendvnc;
	ctrl.msg = &msg;

	memset(&msg, 0x00, sizeof(msg));
	msg.subtype = _IO_CONNECT_COMBINE_CLOSE;
	msg.sflag = SH_DENYNO;
	msg.ioflag = OFLAG;
	msg.mode = mode;
	msg.extra_len = sizeof(iostat);
	if (dirfd != AT_FDCWD) {
		msg.dirfd = (uint16_t) dirfd;
		msg.ioflag |= O_DIRFD;
	}

	fd = _connect_ctrl(&ctrl, path, (unsigned) stat_size, statp);
	if (fd == -1) {
		return -1;
	}
	ConnectDetach(fd);

	return 0;
}

namespace __sanitizer {

#if defined(__x86_64__)
#  include "sanitizer_syscall_nto_x86_64.inc"
#elif defined(__aarch64__)
#  include "sanitizer_syscall_nto_aarch64.inc"
#elif defined(__arm__)
#  include "sanitizer_syscall_nto_armlev7.inc"
#else
#  error "Unsupported architecture!"
#endif


/* check return value from syscall for errors, we are using the _r syscall
   variants, so a failed call will return -errno */
bool internal_iserror(uptr retval, int *rverrno) {
	if ((long) retval < 0) {
		if (rverrno)
			*rverrno = -retval;
		return true;
	}
	return false;
}

typedef _Uint64t Addr;

// --------------- sanitizer_libc.h
uptr internal_mmap(void *addr, uptr length, int prot, int flags, int fd,
		OFF_T offset) {
	return (uptr) _mmap2(addr, length, prot, flags, fd, offset, 0, 0, NULL,
			NULL);
}

uptr internal_munmap(void *addr, uptr length) {
	mem_ctrl_t msg;

	internal_memset(&msg, 0, sizeof(msg));
	msg.i.type = _MEM_CTRL;
	msg.i.subtype = _MEM_CTRL_UNMAP;
	msg.i.addr = (Addr) addr;
	msg.i.len = length;

	return MsgSendnc(MEMMGR_COID, &msg.i, sizeof(msg.i), NULL, 0);
}

uptr internal_close(fd_t fd) {
	io_close_t msg;

	internal_memset(&msg, 0, sizeof(msg));
	msg.i.type = _IO_CLOSE;
	msg.i.combine_len = sizeof(msg.i);

	if ((int) MsgSend_r(fd, &msg.i, sizeof msg.i, NULL, 0) == -EINTR)
		return -1;

	return ConnectDetach_r(fd);
}

uptr internal_sched_yield() {
	return internal_syscall(__NR_SCHED_YIELD);
}

/**
 * There must be a better way...
 */
uptr ReadBinaryName(/*out*/char *buf, uptr buf_len) {
#if 1
	char *tmpbuf;
	uptr tmpsize;
	uptr tmplen;
	if (ReadFileToBuffer("/proc/self/exefile", &tmpbuf, &tmpsize, &tmplen,
			1024 * 1024)) {
		internal_strncpy(buf, tmpbuf, buf_len);
		UnmapOrDie(tmpbuf, tmpsize);
		return internal_strlen(buf);
	}
	return 0;
#else
	bool IsErr = false;
	const char *default_module_name = "/proc/self/exefile";
	uptr module_name_len;
	int readlink_error=0;
	int fd = internal_open( default_module_name, O_RDONLY );
	if (fd > 0) {
		module_name_len = internal_read( fd, buf, buf_len );
		internal_close(fd);
	} else {
		module_name_len=-ENOENT;
	}
	IsErr = internal_iserror(module_name_len, &readlink_error);
	if (IsErr) {
		// We can't read binary name for some reason, assume it's unknown.
		Report("WARNING: reading executable name failed with errno %d, "
				"some stack frames may not be symbolized\n", readlink_error);
		module_name_len = internal_snprintf(buf, buf_len, "%s",
				default_module_name);
		CHECK_LT(module_name_len, buf_len);
	}
	return module_name_len;
#endif
}

int internal_mprotect(void *addr, uptr length, int prot) {
	mem_ctrl_t msg;
	internal_memset(&msg, 0, sizeof(msg));

	msg.i.type = _MEM_CTRL;
	msg.i.subtype = _MEM_CTRL_PROTECT;
	msg.i.addr = (uintptr_t) addr;
	msg.i.len = length;
	msg.i.flags = (uint32_t) prot;

	return MsgSendnc_r(MEMMGR_COID, &msg.i, sizeof(msg.i), NULL, 0);
}

/* todo: side effects!! */
int internal_fork() {
	return fork();
}

/* we're touching errno here - probably this is a bad idea... */
uptr internal_ftruncate(fd_t fd, uptr length) {
	io_space_t msg;
	off64_t size;
	long errstate = 0;

	msg.i.type = _IO_SPACE;
	msg.i.combine_len = sizeof msg.i;
	msg.i.subtype = F_FREESP64;
	msg.i.whence = SEEK_SET;
	msg.i.start = (uint64_t) length;
	msg.i.len = 0;		// to end of file

	if (MsgSendnc_r(fd, &msg.i, sizeof msg.i, &size, sizeof size) < 0) {
		return -1;
	}

	if ((uptr) size >= length) {
		return 0;
	}

	/*
	 * Try to grow using the new space-can-be-sparse/ftruncate
	 * subtype; most non-filesystem resmgr will either not recognise
	 * this subtype (in which case re-issue with the old subtype
	 * whose semantics now mean cannot-be-sparse/posix_fallocate),
	 * or will recognise and treat both subtypes as the same
	 * operation (and do the work on the first msg).
	 */
	msg.i.type = _IO_SPACE;
	msg.i.combine_len = sizeof msg.i;
	msg.i.subtype = F_GROWSP64;
	msg.i.whence = SEEK_SET;
	msg.i.start = (uint64_t) size;
	msg.i.len = (uint64_t)(length - size);

	errstate = MsgSendnc_r(fd, &msg.i, sizeof msg.i, NULL, 0);
	if (errstate < 0) {
		if (errstate == EINVAL) {
			msg.i.type = _IO_SPACE;
			msg.i.combine_len = sizeof msg.i;
			msg.i.subtype = F_ALLOCSP64;
			msg.i.whence = SEEK_SET;
			msg.i.start = (uint64_t) size;
			msg.i.len = (uint64_t)(length - size);

			if (MsgSendnc(fd, &msg.i, sizeof msg.i, NULL, 0) != -1) {
				return 0;
			}
		}
		return -1;
	}

	return 0;
}

enum MutexState {
	MtxUnlocked = 0, MtxLocked = 1, MtxSleeping = 2
};

BlockingMutex::BlockingMutex() {
	internal_memset(this, 0, sizeof(*this));
}

void BlockingMutex::Lock() {
	CHECK_EQ(owner_, 0);
	atomic_uint32_t *m = reinterpret_cast<atomic_uint32_t*>(&opaque_storage_);
	if (atomic_exchange(m, MtxLocked, memory_order_acquire) == MtxUnlocked)
		return;
	while (atomic_exchange(m, MtxSleeping, memory_order_acquire) != MtxUnlocked) {
		sched_yield(); /* No userspace futex-like synchronization */
	}
}

void BlockingMutex::Unlock() {
	atomic_uint32_t *m = reinterpret_cast<atomic_uint32_t*>(&opaque_storage_);
	u32 v = atomic_exchange(m, MtxUnlocked, memory_order_release);
	CHECK_NE(v, MtxUnlocked);
	if (v == MtxSleeping) {
		/* No userspace futex-like synchronization */
	}
}

void BlockingMutex::CheckLocked() {
	atomic_uint32_t *m = reinterpret_cast<atomic_uint32_t*>(&opaque_storage_);
	CHECK_NE(MtxUnlocked, atomic_load(m, memory_order_relaxed));
}

SignalContext::WriteFlag SignalContext::GetWriteFlag() const {
#if defined(__x86_64__) || defined(__i386__)
	static const uptr PF_WRITE = 1U << 1;
	ucontext_t *ucontext = (ucontext_t*) context;
	uptr err = ucontext->uc_mcontext.cpu.rflags;
	return err & PF_WRITE ? WRITE : READ;
#elif defined(__arm__)
	static const uptr FSR_WRITE = 1U << 11;
	ucontext_t *ucontext = (ucontext_t*) context;
	uptr fsr;
	// Read the data fault register
	__asm__ __volatile__ ("mrc p15, 0, %0, c5, c0, 0" : "=r"(fsr));
	return fsr & FSR_WRITE ? WRITE : READ;
#elif defined(__aarch64__)
	static const u64 ESR_ELx_WNR = 1U << 6;
	u64 esr;
	__asm__ __volatile__("mrs	%0, esr_el1" : "=r"(esr));
	return esr & ESR_ELx_WNR ? WRITE : READ;
#else
	(void) ucontext;
	return UNKNOWN;  // FIXME: Implement.
#endif
}

void SignalContext::DumpAllRegisters(void *context) {
	// FIXME: Implement this.
}

static void GetPcSpBp(void *context, uptr *pc, uptr *sp, uptr *bp) {
#if defined(__arm__)
# define	ARM_REG_FP		11
# define	ARM_REG_IP		12
# define	ARM_REG_SP		13
# define	ARM_REG_LR		14
# define	ARM_REG_PC		15
	ucontext_t *ucontext = (ucontext_t*)context;
	*pc = ucontext->uc_mcontext.cpu.gpr[ARM_REG_PC];
	*bp = ucontext->uc_mcontext.cpu.gpr[ARM_REG_FP];
	*sp = ucontext->uc_mcontext.cpu.gpr[ARM_REG_SP];
#elif defined(__aarch64__)
# define	AARCH64_REG_LR		30
# define	AARCH64_REG_SP		31
	ucontext_t *ucontext = (ucontext_t*)context;
	*pc = ucontext->uc_mcontext.cpu.elr;
	*bp = ucontext->uc_mcontext.cpu.gpr[29];
	*sp = ucontext->uc_mcontext.cpu.gpr[AARCH64_REG_SP];
#elif defined(__x86_64__)
	ucontext_t *ucontext = (ucontext_t*)context;
	*pc = ucontext->uc_mcontext.cpu.rip;
	*bp = ucontext->uc_mcontext.cpu.rbp;
	*sp = ucontext->uc_mcontext.cpu.rsp;
#else
# error "Unsupported arch"
#endif
}

void SignalContext::InitPcSpBp() {
	GetPcSpBp(context, &pc, &sp, &bp);
}

// todo Side effects here?!
uptr internal_rename(const char *oldpath, const char *newpath) {
	return rename(oldpath, newpath);
}

uptr internal__open(const char *const path, const int oflag, ...) {

	va_list ap;
	unsigned fd;

	va_start(ap, oflag);
	fd = _vopen(path, oflag, SH_DENYNO, ap);
	va_end(ap);

	return (uptr) fd;

} /* open */

uptr internal_open(char const *path, int flags, unsigned int mode) {
	return internal__open(path, flags, mode);
}

uptr internal_open(char const *path, int flags) {
	return internal__open(path, flags);
}

void internal__exit(int exitcode) {
	__exit(exitcode);
	Die();  // Unreachable.
}

uptr internal_read(fd_t fd, void *buf, uptr count) {
	io_read_t msg;

	msg.i.combine_len = sizeof msg.i;
	msg.i.nbytes = (uint32_t) count;
	msg.i64.nbytes_hi = SIZET_VAL_GET_HI32(count);
	if (msg.i64.nbytes_hi == 0) {
		msg.i.type = _IO_READ;
	} else {
		msg.i.type = _IO_READ64;
	}
	msg.i.xtype = _IO_XTYPE_NONE;
	return (uptr) MsgSend(fd, &msg.i, sizeof msg.i, buf, count);
}

uptr internal_getpid() {
	return (uptr) LIBC_TLS()->__pid;
}

uptr ReadLongProcessName(/*out*/char *buf, uptr buf_len) {
	char *tmpbuf;
	uptr tmpsize;
	uptr tmplen;
	if (ReadFileToBuffer("/proc/self/cmdline", &tmpbuf, &tmpsize, &tmplen,
			1024 * 1024)) {
		internal_strncpy(buf, tmpbuf, buf_len);
		UnmapOrDie(tmpbuf, tmpsize);
		return internal_strlen(buf);
	}
	return ReadBinaryName(buf, buf_len);
}

uptr internal_lstat(const char *const path, struct stat *const buf) {
	return _stat(path, buf, sizeof(*buf), S_IFLNK, AT_FDCWD);
}

uptr internal_stat(const char *const path, struct stat *const buf) {
	return _stat(path, buf, sizeof(*buf), 0, AT_FDCWD);
}

uptr internal_fstat(const int fd, struct stat *const statl) {
	io_stat_t msg;

	msg.i.type = _IO_STAT;
	msg.i.combine_len = sizeof msg.i;
	msg.i.format = _STAT_FORM_PREFERRED;

	int rc = (int) MsgSendnc(fd, &msg.i, sizeof msg.i, statl, sizeof *statl);
	if (rc == -1) {
		if (errno == EISDIR) {
			return fstatat(fd, ".", statl, 0);
		}
		return -1;
	}

	return 0;
} /* fstat */

uptr internal_filesize(fd_t fd) {
	struct stat st;
	if (internal_fstat(fd, &st))
		return -1;
	return (uptr) st.st_size;
}

#ifdef F_DUP2FD
// F_DUP2FD is not available in <= 7.1.0
uptr internal_dup2(int oldfd, int newfd) {
	return (uptr) fcntl(oldfd, F_DUP2FD, newfd);
}
#endif

uptr internal_write(fd_t fd, const void *buf, uptr count) {
	io_write_t msg;
	iov_t iov[2];

	msg.i.combine_len = sizeof msg.i;
	msg.i.xtype = _IO_XTYPE_NONE;
	msg.i.nbytes = (uint32_t) count;
	msg.i64.nbytes_hi = SIZET_VAL_GET_HI32(count);
	if (msg.i64.nbytes_hi == 0) {
		msg.i.type = _IO_WRITE;
	} else {
		msg.i.type = _IO_WRITE64;
	}
	SETIOV(iov + 0, &msg.i, sizeof msg.i);
	SETIOV_CONST(iov + 1, buf, count);
	return (uptr) MsgSendv(fd, iov, 2, 0, 0);
}

uptr internal_waitpid(const pid_t pid, int *const stat_loc, const int options) {
	return (uptr) wait4(pid, stat_loc, options, NULL);
} /* waitpid */

static int internal_getProcinfo() {
	char path[24] = "";

	if (__procinfo == NULL) {
		__procinfo = (debug_thread_t*) malloc(sizeof(debug_thread_t));

		snprintf(path, 24, "/proc/%lu/ctl", __sanitizer::internal_getpid());
		int fd = __sanitizer::internal_open(path, O_RDONLY);
		if (fd < 0) {
			free(__procinfo);
			__procinfo = NULL;
			return 1;
		}
		if (devctl(fd, DCMD_PROC_STATUS, __procinfo, sizeof(debug_thread_t),
				NULL) < 0) {
			free(__procinfo);
			__procinfo = NULL;
			return 1;
		}
		__sanitizer::internal_close(fd);
	}
	return 0;
}

static void GetArgsAndEnv(char ***argv, char ***envp) {
	uptr *stack_end = NULL;
	int argc = 0;
	if (__sanitizer::internal_getProcinfo() == 0) {
		stack_end = (uptr*) (__procinfo->stkbase - __procinfo->stksize);
		argc = *stack_end;
		*argv = (char**) (stack_end + 1);
		*envp = (char**) (stack_end + argc + 2);
	}
}

char** GetArgv() {
	char **argv = NULL, **envp = NULL;
	GetArgsAndEnv(&argv, &envp);
	return argv;
}

// Like getenv, parses the 'environ' array and does not use libc. This function should be
// called first inside __asan_init.
const char* GetEnv(const char *name) {
	if (::environ != 0) {
		uptr NameLen = internal_strlen(name);
		for (char **Env = ::environ; *Env != 0; Env++) {
			if (internal_strncmp(*Env, name, NameLen) == 0
					&& (*Env)[NameLen] == '=')
				return (*Env) + NameLen + 1;
		}
	} else {
		Printf("environment unavailable!\n");
		Die();
	}
	return 0;  // Not found.
}

bool FileExists(const char *filename) {
	struct stat st;
	if (internal_stat(filename, &st))
		return false;
	// Sanity check: filename is a regular file.
	return S_ISREG(st.st_mode);
}

uptr GetPageSize() {
	return sysconf(_SC_PAGESIZE);
}

static HandleSignalMode GetHandleSignalModeImpl(int signum) {
	switch (signum) {
	case SIGABRT:
		return common_flags()->handle_abort;
	case SIGILL:
		return common_flags()->handle_sigill;
	case SIGFPE:
		return common_flags()->handle_sigfpe;
	case SIGSEGV:
		return common_flags()->handle_segv;
	case SIGBUS:
		return common_flags()->handle_sigbus;
	}
	return kHandleSignalNo;
}

HandleSignalMode GetHandleSignalMode(int signum) {
	HandleSignalMode result = GetHandleSignalModeImpl(signum);
	if (result == kHandleSignalYes && !common_flags()->allow_user_segv_handler)
		return kHandleSignalExclusive;
	return result;
}

} // namespace __sanitizer

/**
 * helperfunctions to support connect_ctrl functionality outside of libc.
 */
#include <stddef.h>
#include <sys/procmgr.h>

#define _CONNECT_CTRL_NOCTTY				0x00010000
#define _CONNECT_CTRL_TEST_ENTRY			0x00040000		/* Test the entry, nid,pid,handle,chid */
#define _CONNECT_CTRL_NO_SYM				0x00100000
#define _CONNECT_CTRL_MALLOC_FDS			0x00200000
#define _CONNECT_CTRL_TEST_NPC_ONLY			0x00400000		/* Test only the nid,pid,chid when _CONNECT_CTRL_TEST_ENTRY is set*/

#define _CONNECT_CTRL_STACK_ALLOC			0x01000000		/* Allocate from stack (alloca) not heap (malloc) */
#define _CONNECT_CTRL_TEST_ND_ONLY			0x02000000		/* Only send full requests to the node matching the 'nd' value */

#define FD_BUF_INCREMENT    10

/* If we think that we have space on the stack (guesstimate
 32 symlinks with 32 servers with 1K path == 32 * 2K == 64K)
 make it 80K for good measure. */
#define MIN_STACK_FOR_GROWTH 81920
#define CTRL_ALLOC(flag, len) (((flag) & _CONNECT_CTRL_STACK_ALLOC) ? alloca((len)) : malloc((len)))
#define CTRL_FREE(flag, data) (((flag) & _CONNECT_CTRL_STACK_ALLOC) ? ((void)0) : free((data)))

static const struct _io_connect_entry _connect_proc_entry = { ND_LOCAL_NODE,
		PATHMGR_PID, PATHMGR_CHID, PATHMGR_HANDLE, 0, 0, 0, { 0 } };

static int _connect_handle_server_errno(int *const error,
		const int saved_error) {
	int need_loop = 0;
	switch (*error) {
	case ENOENT:
	case ENXIO:
	case ESRCH:
	case EBADFSYS:
		switch (saved_error) {
		case EOK:
		case ENOSYS:
			break;
		default:
			*error = saved_error;
			break;
		}
		need_loop = 1;
		break;
	case EROFS:
		switch (saved_error) {
		case ENOSYS:
		case ESRCH:
		case ENXIO:
		case ENOENT:
		case EOK:
			break;
		default:
			*error = saved_error;
			break;
		}
		need_loop = 1;
		break;
	case ENOSYS:
		switch (saved_error) {
		case EOK:
			break;
		default:
			*error = saved_error;
			break;
		}
		need_loop = 1;
		break;
	default:
		if ((*error < ENETDOWN) || (*error > EHOSTUNREACH)) {
			break;
		}
		switch (saved_error) {
		case EOK:
		case ENOSYS:
			break;
		default:
			*error = saved_error;
			break;
		}
		need_loop = 1;
		break;
	}
	return need_loop;
}

static int _connect_io(const struct _connect_ctrl *const ctrl, const int fd,
		const char *const prefix, const unsigned prefix_len,
		const char *const path, void *const buffer,
		const struct _io_connect_entry *const entry) {

	register struct _io_connect *msg = ctrl->msg;
	register struct _io_connect_link_reply *reply = &(ctrl->reply->link);
	iov_t siov[5], riov[2];
	register unsigned sparts;
	static const char padding[_QNX_MSG_ALIGN - 1] = "";
	int ret, tryagain;
	const struct _io_connect_entry *const ent = ctrl->entry;

	// The last server may have returned a key to authorize us with this server
	msg->key = entry->key;

	SETIOV(siov + 0, msg, offsetof(struct _io_connect, path));
	if (prefix_len) {
		SETIOV_CONST(siov + 1, prefix, prefix_len);
		sparts = 2;
	} else {
		sparts = 1;
	}
	SETIOV_CONST(siov + sparts, path, msg->path_len);
	sparts++;
	msg->path_len += prefix_len;
	if (msg->extra_len) {
		size_t align;

		if ((align = (_QNX_MSG_ALIGN
				- (offsetof(struct _io_connect, path) + msg->path_len))
				& (_QNX_MSG_ALIGN - 1))) {
			SETIOV_CONST(siov + sparts, padding, align);
			sparts++;
		}
		SETIOV_CONST(siov + sparts, ctrl->extra, msg->extra_len);
		sparts++;
	}
	SETIOV(riov + 0, reply, sizeof *reply);
	SETIOV(riov + 1, buffer, msg->reply_max - sizeof *reply);

	/*
	 If our entries don't match, then try and resolve it to a link to find a match
	 by sending an COMBINE_CLOSE message to the handler to see if it will
	 resolve into a bigger linke.  If we do find a match (later on as we recursed
	 through the entries in the process) then actually sent the message that
	 we originally were supposed to send. See rename() to see how this is used.

	 This functionality is also used to resolve links "magically" by switching
	 the message type to be an open if the intial request fails.  This means
	 that we don't have to fill proc with all the resolution.
	 */

	//We don't want to test the entries, or we have a matching entry ... send original message
	if (!(ctrl->flags & _CONNECT_CTRL_TEST_ENTRY)) {
		ret = 1;
	} else if ((ent->pid == entry->pid) && (ent->chid == entry->chid)
			&& (ND_NODE_CMP(ent->nd, entry->nd) == 0)
			&& ((ctrl->flags & _CONNECT_CTRL_TEST_NPC_ONLY)
					|| (ent->handle == entry->handle))) {
		ret = 1;
	} else {
		ret = 0;
	}

	if (ret
			&& (!(ctrl->flags & _CONNECT_CTRL_TEST_ND_ONLY)
					|| (ND_NODE_CMP(ctrl->nd, entry->nd) == 0))) {
		if (((ret = (int) ctrl->send(fd, siov, sparts, riov, 2)) != -1)
				|| ((ctrl->flags & _CONNECT_CTRL_TEST_ENTRY))) {
			return ret;
		}
	}

	//We only try to resolve a link reply if we didn't send in the first place or if
	//the request went out and returned with ENOSYS indicating no callout.
	tryagain = ((ret != -1) || (_errno == ENOSYS));
	switch (msg->subtype) {
	case _IO_CONNECT_OPEN:
	case _IO_CONNECT_COMBINE:
	case _IO_CONNECT_COMBINE_CLOSE:
		break;

		/*
		 These have specific resmgr helpers, that return specific
		 errno's in the case of failure.
		 */
	case _IO_CONNECT_LINK:
		tryagain |= (_errno == ENXIO) ? 1 : 0;
		break;
	default:
		break;
	}

	//If we failed (or we didn't have a matching entry) stuff a msg to resolve possible links
	if (tryagain) {
		uint32_t saved_ioflag;
		uint16_t saved_type;
		uint16_t saved_elen;
		uint8_t saved_eflag;
		uint8_t saved_etype;
		int saved_errno;

		saved_ioflag = msg->ioflag;
		saved_type = msg->subtype;
		saved_eflag = msg->eflag;
		saved_etype = msg->extra_type;
		saved_elen = msg->extra_len;

		msg->ioflag = saved_ioflag & O_DIRFD; // don't lose dirfd
		msg->extra_len = 0;
		msg->extra_type = _IO_CONNECT_EXTRA_NONE;
		msg->subtype = _IO_CONNECT_COMBINE_CLOSE;

		saved_errno = _errno;			//Meaningless errno for matching entry
		ret = (int) ctrl->send(fd, siov, sparts, riov, 2);
		if (ret == -1) {
			//Every other error is disregarded
			_errno =
					(ctrl->flags & _CONNECT_CTRL_TEST_ENTRY) ?
							ENXIO : saved_errno;

			//If we return anything other than a link here, it is an error
		} else if ((ret & (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_TYPE_MASK))
				!= (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_LINK)) {
			_errno =
					(ctrl->flags & _CONNECT_CTRL_TEST_ENTRY) ?
							ENXIO : saved_errno;
			ret = -1;
		}

		msg->subtype = saved_type;
		msg->eflag = saved_eflag;
		msg->extra_type = saved_etype;
		msg->extra_len = saved_elen;
		msg->ioflag = saved_ioflag;
	} else {
		_errno = (_errno == EOK) ? ENOENT : _errno;
		ret = -1;
	}

	return ret;

} /* _connect_io */

/**
 * Appends a path section to the one tracked by the given control structure.
 * @param   ctrl        Control structure to append to
 * @param   path        Path to append
 * @param   path_skip   Offset into @p path from which to start copying
 */
static void copy_path(struct _connect_ctrl *const ctrl, const char *const path,
		const unsigned path_skip) {
	if (ctrl->path == NULL) {
		return;
	}

	const size_t pathlen = __sanitizer::internal_strlen(path + path_skip) + 1;
	char *insert = &ctrl->path[ctrl->pathlen];
	size_t extra = 0;

	if (pathlen != 1) {
		// Will need to add a '/'.
		extra = 1;
	}

	if ((ctrl->pathsize - ctrl->pathlen) < (int) (pathlen + extra)) {
		// Not enough space remaining in ctrl->path[].
		ctrl->path[0] = '\0';
		ctrl->pathsize = 0;
		return;
	}

	if (extra) {
		*insert = '/';
		insert++;
	}

	__sanitizer::internal_memcpy(insert, path + path_skip, pathlen);
}

static int _connect_request(struct _connect_ctrl *const ctrl,
		const char *const prefix, const unsigned prefix_len,
		const char *const path, unsigned path_skip,
		const struct _io_connect_entry *entry, void *const buffer,
		unsigned chrootlen) {
	register struct _io_connect *msg = ctrl->msg;
	register struct _io_connect_link_reply *reply = &(ctrl->reply->link);
	register int fd;
	unsigned const cof_flags = ctrl->flags & _NTO_COF_MASK;

	fd = ConnectAttach(entry->nd, entry->pid, entry->chid, ctrl->base,
			_NTO_COF_CLOEXEC | cof_flags);
	if (fd != -1) {
		msg->handle = entry->handle;
		msg->eflag = reply->eflag;

		//Get the status of the node in question along with all of the node entries associated with it
		ctrl->status = _connect_io(ctrl, fd, prefix, prefix_len,
				path + path_skip, buffer, entry);
		if (-1 == ctrl->status) {
			ConnectDetach_r(fd);
			return (-1);
		}

		/*
		 If a link was returned it means that there are other managers out there
		 that might handle use.  We can cycle through each of the node entries
		 querying them to see if they can do what we need them to do
		 */
		if ((ctrl->status & (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_TYPE_MASK))
				== (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_LINK)) {

			ConnectDetach_r(fd);

			//Nuke the chroot_len reply field if that flag not set
			if (!(ctrl->status & _IO_CONNECT_RET_CHROOT)) {
				reply->chroot_len = 0;
			}

			//Check the mode flag against our umask
			if ((entry->pid == PATHMGR_PID) && (entry->chid == PATHMGR_CHID)
					&& !prefix) {
				if (ctrl->status & _IO_CONNECT_RET_UMASK) {
					msg->mode &= ~(reply->umask & ~S_IFMT);
				}
				if (ctrl->status & _IO_CONNECT_RET_NOCTTY) {
					ctrl->flags |= _CONNECT_CTRL_NOCTTY;
				}
			}

			//Make sure we do not recurse forever
			if (msg->entry_max == 0) {
				_errno = ELOOP;
				return -1;
			}

			//Make sure we fail on symlinks if we find one
			if ((msg->ioflag & O_NOSYMLINK) && !reply->nentries) {
				_errno = ELOOP;
				return -1;
			}

			if (sizeof(*reply) + reply->nentries * sizeof(*entry)
					+ reply->path_len >= msg->reply_max) {
				_errno = ENAMETOOLONG;
				return -1;
			}

			//If we have multiple entries for this node, then look at each entry/object/connection
			//in turn to see if that connection can give us the services we desire
			if (reply->nentries) {
				char *save;
				void *buff;
				unsigned path_len, cnt;
				uint8_t num; /* 256 entries returned max */

				path_len = reply->path_len;
				cnt = num = reply->nentries;
				chrootlen += reply->chroot_len;

				ctrl->chroot_len = reply->chroot_len;

				buff = ((struct _io_connect_entry*) buffer + num);
				if ((path_skip > 1) && (path[path_skip - 1] == '/')) {
					path_skip--;
				}
				save = (char*) CTRL_ALLOC(ctrl->flags, path_len + path_skip);
				if (NULL == save) {
					_errno = ENOMEM;
					return -1;
				}
				__sanitizer::internal_memcpy(save, path, path_skip);
				__sanitizer::internal_memcpy(save + path_skip, buff, path_len);

				msg->reply_max -= num * sizeof *entry;
				entry = (struct _io_connect_entry*) buffer;

				msg->entry_max--;
				for (; cnt > 0; entry++, cnt--) {
					/*
					 If this is a FTYPE_ALL/FTYPE_MATCHED, skip this entry, this is
					 here since you might return an FTYPE_MATCHED at one of the
					 earlier iterations.  A better solution would be to switch on
					 msg->file_type below rather than ftype, then remove this test.
					 */
					if (msg->file_type == (unsigned) _FTYPE_ALL) {
						continue;
					}

					//Check to see if this entry/manager provides the type of service we want
					if ((msg->file_type == _FTYPE_ANY)
							|| (entry->file_type == (unsigned) _FTYPE_ALL)
							|| (msg->file_type == entry->file_type)) {
						int pad_len;
						int save_errno;
						int marker;

						save_errno = _errno;
						msg->path_len = path_len - entry->prefix_len;

						/*
						 We stuff the path piecewise whenever we have a skip component.
						 In order to do this we shift the path insert point forward
						 before we recurse and then move it back and stuff the path
						 after we recurse.
						 We expect that the component that we are stuffing will always
						 begin with a / and doesn't terminate with a slash.
						 */
						pad_len = entry->prefix_len;
						if (((path_skip + pad_len) > 0)
								&& (save[path_skip + pad_len - 1] == '/')) {
							--pad_len;
						}
						if ((ctrl->pathsize - ctrl->pathlen) < pad_len) {
							pad_len = 0;
						}
						ctrl->pathlen += pad_len;
						marker = ctrl->pathlen;	//We might be able to remove the marker

						fd = _connect_request(ctrl, 0, 0, save,
								entry->prefix_len + path_skip, entry, buff,
								chrootlen);

						if (pad_len && (marker == ctrl->pathlen)) {
							ctrl->pathlen -= pad_len;
							if ((fd != -1) && (ctrl->path && ctrl->pathsize)) {
								__sanitizer::internal_memcpy(
										&ctrl->path[ctrl->pathlen],
										&save[path_skip], pad_len);
							}
						}

						//We want to continue cycling if we have an array, and we have space
						//in the array to store fd's, otherwise we break out and return the fd
						if ((fd != -1) && ctrl->fds) {
							continue;
						}

						//We had an error, try it again with another manager or exit if the
						//manager says they handle us but want to return an error (ie ejected cdrom)
						//Since each resmgr is not aware of any other resmgr, we need to determine
						//what the final error should be.  Returned errors can either indicate
						//that the resmgr intends an error, or it could mean the resmgr does not
						//handle the request, in which case, its error message should not be
						//considered for return to the user, unless there are no other
						//errors
						//
						//Error importance is:
						//EOK < ENOSYS < ENOENT | ENXIO | ESRCH | EBADFSYS < EROFS < any other error
						//
						if ((fd == -1)
								&& (msg->file_type != (unsigned) _FTYPE_MATCHED)) {
							if (_connect_handle_server_errno(&_errno,
									save_errno)) {
								// A return of 1 indicates the need to loop,
								// the old code would have done a continue
								// from the switch here, so still do the continue
								continue;
							}
						}

						break;
					}
				}
				msg->entry_max++;

				msg->reply_max += num * sizeof *entry;
				CTRL_FREE(ctrl->flags, save);

				/*
				 Otherwise we are a link to somewhere, but there are no specific
				 entries (ie managers) for us to query, but we have a new path
				 (ie symlink) for us to query and traverse, looking for handlers.

				 Proc always receives a request which is relative to the chroot
				 and returns a path which is absolute.  We do the translation
				 as required when a symlink is involved.
				 */
			} else {
				char *savedpath, *buff = (char*) buffer;
				int hold_pathlen;
				unsigned preoffset, postoffset;

				msg->path_len = reply->path_len;
				hold_pathlen = ctrl->pathlen;
				ctrl->pathlen = 0;

				/* Don't bother with the path work if we only want real path */
				if (ctrl->path && (ctrl->flags & _CONNECT_CTRL_NO_SYM)) {
					savedpath = ctrl->path;
					ctrl->path = NULL;
				} else {
					savedpath = NULL;
				}

				if (*buff == '/') { /* Don't mess with absolute links */
					preoffset = path_skip;
					postoffset = 0;
				} else if (chrootlen < path_skip) { /* chroot fits under mount point */
					preoffset = (uint16_t) chrootlen;
					postoffset = 0;
				} else { /* chroot over mount point */
					preoffset = path_skip;
					postoffset = chrootlen - path_skip;
				}

				fd = _connect_request(ctrl, path + preoffset,
						path_skip - preoffset, buff + postoffset, 0,
						&_connect_proc_entry, buff, 0);

				if (savedpath && (fd != -1)) {
					ctrl->path = savedpath;
					ctrl->pathlen = hold_pathlen;
					copy_path(ctrl, path, path_skip);
				}
			}

			/* File was matched but a request to change the file type was made */
		} else if ((ctrl->status
				& (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_TYPE_MASK))
				== (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_FTYPE)) {
			ConnectDetach_r(fd);

			if (msg->file_type == _FTYPE_ANY) {
				// Requested any file type, got back a particular type.
				// The call needs to bail out through all recursion levels and
				// connect to the path manager of the current node using the
				// specific type. The _CONNECT_CTRL_TEST_ND_ONLY causes the
				// second attempt to skip all managers from other nodes
				// (particularly the local node if the response came from
				// another node).
				// FIXME:
				// What is the check for _FTYPE_MATCHED below used for?
				msg->file_type = ctrl->reply->ftype.file_type;
				ctrl->nd = entry->nd;
				ctrl->flags |= _CONNECT_CTRL_TEST_ND_ONLY;
			}

			//Only if the file type is matched do we change it. Does it matter?
			if (ctrl->reply->ftype.file_type == (unsigned) _FTYPE_MATCHED) {
				msg->file_type = ctrl->reply->ftype.file_type;
			}

			// A return value with _IO_CONNECT_RET_FTYPE is not an error. The
			// code sets errno to ENOSYS in order to bail out and get back to
			// _connect_ctrl(), which will invoke _connect_request() again (see
			// the onemoretime label).
			// FIXME:
			// ENOSYS causes the link loop to keep on going, which is wrong. We
			// should bail out all the way to _connect_ctrl() immediately.
			_errno = ctrl->reply->ftype.status;
			_errno = (_errno == EOK) ? ENOSYS : _errno;
			fd = -1;

			//We have connected to the server, and the server returned some stuff for us to re-send
		} else if ((ctrl->status & (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_MSG))
				== (_IO_CONNECT_RET_FLAG | _IO_CONNECT_RET_MSG)) {

			msg->file_type = (unsigned) _FTYPE_MATCHED;
			ConnectDetach_r(fd);
			if (entry->pid != PATHMGR_PID) {
				// _IO_CONNECT_RET_MSG is used by procnto to redirect /dev/tty, /dev/stdout etc to the
				// appropriate server.  Allowing any other process to return an unknown message
				// that we'll blindly send is incredibly dangerous so disallow it.
				fd = -1;
				_errno = ENOTSUP;
			} else if (((msg->subtype == _IO_CONNECT_OPEN)
					&& (msg->extra_len == 0))
					|| (((msg->subtype == _IO_CONNECT_COMBINE)
							|| (msg->subtype == _IO_CONNECT_COMBINE_CLOSE))
							&& reply->path_len)) {
				register struct _server_info32 *info =
						(struct _server_info32*) buffer;

				if ((fd = ConnectAttach(info->nd, info->pid, info->chid,
						ctrl->base, _NTO_COF_CLOEXEC | cof_flags)) != -1) {
					if (reply->path_len) {
						register struct _io_combine *next =
								(struct _io_combine*) (info + 1);
						iov_t siov[2], riov[2];
						int sparts = 1;

						SETIOV(siov + 0, next, reply->path_len);
						if (msg->extra_len) {
							next->combine_len |= _IO_COMBINE_FLAG;
							SETIOV_CONST(siov + 1, ctrl->extra, msg->extra_len);
							sparts++;
						}
						SETIOV(riov + 0, reply, sizeof *reply);
						SETIOV(riov + 1, buffer,
								msg->reply_max - sizeof *reply);
						ctrl->status = (int) ctrl->send(fd, siov, sparts, riov,
								2);
						if ((ctrl->status == -1)
								|| (msg->subtype == _IO_CONNECT_COMBINE_CLOSE)) {
							io_close_t msg2;
							int save_errno;

							msg2.i.type = _IO_CLOSE;
							msg2.i.combine_len = sizeof msg2.i;
							SETIOV(siov + 0, &msg2.i, sizeof msg2.i);
							save_errno = _errno;
							(void) ctrl->send(fd, siov, 1, 0, 0);
							_errno = save_errno;
							if (ctrl->status == -1) {
								ConnectDetach_r(fd);
								fd = -1;
							}
						}
					}
				}
			} else {
				fd = -1;
				_errno = ENOTSUP;
			}

			//We didn't get any return message from the server, end of recursion on this tree?
		} else {
			//Stick the discovered fd into an array of fds, resizing if required/allowed
			if (ctrl->fds) {
				if (ctrl->fds_index >= (ctrl->fds_len - 1)) {
					int *tmp;
					//If we are not ok with resizing, or we run out of memory ... error out
					if (!(ctrl->flags & _CONNECT_CTRL_MALLOC_FDS)
							|| !(tmp = (int*) realloc(ctrl->fds,
									(ctrl->fds_len + FD_BUF_INCREMENT)
											* sizeof(*ctrl->fds)))) {
						_errno = ENOMEM;
						return (-1);
					}
					ctrl->fds = tmp;
					ctrl->fds_len += FD_BUF_INCREMENT;
				}

				ctrl->fds[ctrl->fds_index++] = fd;
			}

			//This only gets done once, if the message has extra data ... copy it over
			//We use memmove since there may be overlapping areas involved here.
			if (ctrl->response_len) {
				int b;

				b = min((int )sizeof(*ctrl->reply), ctrl->response_len);
				__sanitizer::internal_memmove(ctrl->response, ctrl->reply, b);
				if (ctrl->response_len > b) {
					__sanitizer::internal_memmove(((char*) ctrl->response) + b,
							buffer, ctrl->response_len - b);
				}

				ctrl->response_len = 0;
			}

			if (ctrl->entry) {
				*ctrl->entry = *entry;
				ctrl->entry->prefix_len = prefix_len + path_skip;
			}

			copy_path(ctrl, path, path_skip);
		}
	}

	//We don't want to return -1 if we actually manage to cache other managers
	return (((fd == -1) && ctrl->fds && ctrl->fds_index) ? ctrl->fds[0] : fd);

} /* _connect_request */

struct _link_reply {
	struct _io_connect_link_reply reply;
	char filler[MIN_FILLER_SIZE];
};

static int _connect_ctrl(struct _connect_ctrl *const ctrl,
		const char *const path, unsigned response_len, void *const response) {
	struct _io_connect *msg = ctrl->msg;
	int fd;
	int save_errno;
	unsigned save_ftype;
	unsigned save_ioflag;
	struct _link_reply *buffer;
	int oflag, freebuffer;

	ctrl->chroot_len = 0;

	if (*path == '\0') {
		_errno = ENOENT;
		return -1;
	}

	/*
	 * Check if path exceeds PATH_MAX bytes (including terminating NULL)
	 */
	if (__sanitizer::internal_strlen(path) >= PATH_MAX) {
		_errno = ENAMETOOLONG;
		return -1;
	}

	/* If we have a valid entry, do we want to test ourselves against it? */
	if (msg->file_type == (unsigned) _FTYPE_MATCHED) {
		msg->file_type = _FTYPE_ANY;
		if (ctrl->entry) {
			ctrl->flags |= _CONNECT_CTRL_TEST_ENTRY;
		}
	}
	save_ftype = msg->file_type;
	save_ioflag = msg->ioflag;

	onemoretime: msg->file_type = save_ftype;
	msg->ioflag = save_ioflag;

	/*
	 This is where the first response will go from the client. In the
	 case of multiple fd's only the first reply is permanently recorded,
	 all others are ignored
	 */
	response_len = (response) ? response_len : 0;
	ctrl->response_len = response_len;
	ctrl->response = response;

	/* TODO: Make the allocation, re-use and buffer sizes
	 all user configurable somehow. */

	/*
	 Decide which type of allocation policy we want to
	 use: malloc/free on the heap, alloc/xxx on the stack

	 If we think that we have space on the stack (guesstimate
	 32 symlinks with 32 servers with 1K path == 32 * 2K == 64K)
	 then go with stack allocation?
	 */
	ctrl->flags |= _CONNECT_CTRL_STACK_ALLOC;
	if (_connect_malloc && (__stackavail() < MIN_STACK_FOR_GROWTH)) {
		ctrl->flags &= ~_CONNECT_CTRL_STACK_ALLOC;
	}

	/*
	 We only need to allocate a copy if we are going to  be iterating
	 over multiple fds, otherwise just make response the same as the
	 reply buffer (unless the reply buffer won't hold our minimum size)
	 This saves us from double allocating when we don't have to.
	 */
	if (ctrl->fds || (ctrl->flags & _CONNECT_CTRL_MALLOC_FDS)
			|| (response_len < sizeof(*buffer))) {
		freebuffer = 1;
		if (!(buffer = (struct _link_reply*) CTRL_ALLOC(ctrl->flags,
				max(response_len, sizeof(*buffer))))) {
			_errno = ENOMEM;
			return (-1);
		}
	} else {
		freebuffer = 0;
		buffer = (struct _link_reply*) response;
	}
	ctrl->reply = (_connect_ctrl::_io_connect_reply_type*) buffer;
	msg->reply_max = (uint16_t)max(response_len, sizeof(*buffer));

	ctrl->reply->link.eflag = 0;

	/*
	 Always send a connect message.  When we allow a user
	 configurable buffer, set the entry_max accordingly.

	 max_entry starts at MAX + 1 because the first iteration of
	 _connect_request doesn't traverse any path node yet but decrements
	 the value by one.
	 */
	msg->type = _IO_CONNECT;
	msg->entry_max = SYMLOOP_MAX + 1;
	msg->path_len = (uint16_t)(__sanitizer::internal_strlen(path) + 1);
	oflag = msg->ioflag;
	msg->ioflag = (unsigned) ((oflag & ~(O_ACCMODE | O_CLOEXEC))
			| ((oflag + 1) & msg->access & O_ACCMODE));

	save_errno = _errno;
	_errno = EOK;

	__LINT(assert(NULL != buffer));

	if ((fd = _connect_request(ctrl, 0, 0, path, 0, &_connect_proc_entry,
			buffer->filler, 0)) != -1) {
		_errno = save_errno;

		// If not close on exec, then turn off the close on exec bit
		if (!(ctrl->base & _NTO_SIDE_CHANNEL) && !(oflag & O_CLOEXEC)) {
			ConnectFlags_r(0, fd, FD_CLOEXEC, 0);
		}
		if ((ctrl->flags & _CONNECT_CTRL_NOCTTY) && !(oflag & O_NOCTTY)
				&& isatty(fd)) {
			(void) procmgr_session(ND_LOCAL_NODE, getpid(), fd,
					PROCMGR_SESSION_TCSETSID);
		}

		//Unfortunately path = "" is both a valid return (internally) but an
		//error condition (externally) so we resort to munging the path here
		if (ctrl->path && (ctrl->pathsize > 1) && (ctrl->path[0] == '\0')) {
			ctrl->path[0] = '/';
			ctrl->path[1] = '\0';
		}
	} else if ((save_ftype == _FTYPE_ANY)
			&& ((_errno == ENOSYS) || (_errno == ENOENT))
			&& (msg->file_type != save_ftype)
			&& (msg->file_type != (unsigned) _FTYPE_MATCHED)) {
		/* If the filetype change, but we still failed, then try sending the
		 request again but with the new filetype.  This is for servers who
		 have mounted on top of filesystems using their services. */
		if (freebuffer) {
			CTRL_FREE(ctrl->flags, buffer);
		}
		save_ftype = msg->file_type;
		goto onemoretime;
	}

	if (freebuffer) {
		CTRL_FREE(ctrl->flags, buffer);
	}

	return fd;

} /* _connect_ctrl */

/* Minimal implementation of pthread_attr_get_np for NTO
 * must only be used to read information as the pthread_attr_t structure is just a
 * representation of the actual TIDSTATUS */
int pthread_getattr_np(pthread_t thread, pthread_attr_t *attr) {
	if (__sanitizer::internal_getProcinfo() == 0) {
		pthread_attr_setstack(attr, (void*) __procinfo->stkbase,
				__procinfo->stksize);
		return 0;
	}
	return 1;
}

#endif  // SANITIZER_QNX
