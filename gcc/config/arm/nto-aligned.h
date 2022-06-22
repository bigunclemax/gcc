#undef NTO_OVERRIDE_ALIGNED_ACCESS
#define NTO_OVERRIDE_ALIGNED_ACCESS	\
do {					\
    if (unaligned_access == 2)		\
		unaligned_access = 0;	\
} while (0)
