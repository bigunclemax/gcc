#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "opts.h"

/**
 * The library names.  These will be passed to the linker using the '-l' option.
 */
static const char * const gnu_cxx_stdlib = "stdc++";
static const char * const llvm_cxx_stdlib = "c++";

/**
 * Determines the C++ standard library to use, given the combination of
 * configured defaults and command-line options.  The default is determined at
 * compiler configuration time and the actual library depends on the last
 * instance of the -stdlib= command-line option given.
 *
 * Because this function is called before duplicate options are removed and the
 * canonical option setting determined, it's mandatory to scan the entire list
 * of known options to look for the lastmost occurrence of the -stdlib option,
 * which may be given more than once.
 */
const char *
nto_select_libstdcxx (struct cl_decoded_option* options, unsigned int options_count)
{
#if defined(DEFAULT_STDLIB_LIBSTDCXX)
    const char * stdlib = gnu_cxx_stdlib;
#elif defined(DEFAULT_STDLIB_LIBCXX)
    const char * stdlib = llvm_cxx_stdlib;
#else
# error No default C++ standard library configured.
#endif

	for(unsigned int i = 0; i < options_count; ++i)
	{
		if(options[i].opt_index == OPT_stdlib_)
		{
			if(0 == strcmp (options[i].arg, "libstdc++"))
			    stdlib = gnu_cxx_stdlib;
			else if(0 == strcmp (options[i].arg, "libc++"))
			    stdlib = llvm_cxx_stdlib;
		}
	}

	return stdlib;
}

const char *
nto_select_libstdcxx_static (void)
{
  return NULL;
}

