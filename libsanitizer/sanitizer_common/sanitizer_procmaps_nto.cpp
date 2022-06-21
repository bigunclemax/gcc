//===-- sanitizer_procmaps_nto.cc ---------------------------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Information about the process mappings (Neutrino-specific parts).
// Copyright (c) 2021, QNX Software Systems. All Rights Reserved.
//===----------------------------------------------------------------------===//

#include "sanitizer_platform.h"
#if SANITIZER_QNX
#include "sanitizer_common.h"
#include "sanitizer_procmaps.h"

namespace __sanitizer {

void ReadProcMaps(ProcSelfMapsBuff *proc_maps) {
	ReadFileToBuffer("/proc/self/pmap", &proc_maps->data, &proc_maps->mmaped_size,
			&proc_maps->len);
}

bool MemoryMappingLayout::Next(MemoryMappedSegment *segment) {
	char *last = data_.proc_self_maps.data + data_.proc_self_maps.len;
	if (data_.current >= last) return false;
	char *next_line =
			(char *)internal_memchr(data_.current, '\n', last - data_.current);
	if (next_line == 0)
		next_line = last;
	// The format line needs to be skipped!
	else if (*data_.current == 'v') {
		data_.current = next_line + 1;
		next_line = (char *)internal_memchr(data_.current, '\n', last - data_.current);
	}

	// Format: vaddr,size,flags,prot,maxprot,dev,ino,offset,rsv,guardsize,refcnt,mapcnt,path */
	// Read vaddr
	segment->start = ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// read len, end = start+len
	segment->end = segment->start+ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip flags
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// read prot
	segment->protection = ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip maxprot
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip dev
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip ino
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// read offset
	segment->offset = ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip rsv
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip guardsize
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip refcnt
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// skip mapcnt
	ParseHex(&data_.current);
	CHECK_EQ(*data_.current++, ',');
	// Fill in the path
	if (segment->filename) {
		uptr len =
				Min((uptr)(next_line - data_.current), segment->filename_size - 1);
		internal_strncpy(segment->filename, data_.current, len);
		segment->filename[len] = 0;
	}
	data_.current = next_line + 1;
	return true;
}

}  // namespace __sanitizer

#endif  // SANITIZER_QNX
