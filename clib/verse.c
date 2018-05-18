#include "verse.h"

/*
 *  These are declared as macros because they will work for both
 *  32-bit as well as 64-bit cases.
 */

#define MASK(i)                                                                \
	(0xFFULL << (8 * (i))) /* mask to select the ith byte              */

#define SEL(a, i) ((a)&MASK(i)) /* select the ith byte                      */

#define MOVL(a, i)                                                             \
	((a) << (8 * (i))) /* shift the bytes i positions to the left  */

#define MOVR(a, i)                                                             \
	((a) >> (8 * (i))) /* shift the bytes i positions to the right */

#define SWAP(a, i, j) (MOVL(SEL(a, i), (j - i)) | MOVR(SEL(a, j), (j - i)))
/* This function swaps the ith and jth bytes and sets other bytes to 0 */

#define TO16(x) ((uint16_t)(x))
#define TO32(x) ((uint32_t)(x))
#define TO64(x) ((uint64_t)(x))

#define B16(ptr, i) (TO16(ptr[i]))
#define B32(ptr, i) (TO32(ptr[i]))
#define B64(ptr, i) (TO64(ptr[i]))

/* Make a 16-bit quantity out of the 4 bytes given in MSB first order */
#define MK16(a, b) ((a) << 8 | (b))
/* Similar to MK16 but for 32-bit quantities */
#define MK32(a, b, c, d) ((a) << 24 | (b) << 16 | (c) << 8 | (d))
/* Similar to MK32 but for 64-bit quantities */
#define MK64(a, b, c, d, e, f, g, h)                                           \
	((a) << 56 | (b) << 48 | (c) << 40 | (d) << 32 | (e) << 24 | (f) << 16 |   \
	 (g) << 8 | (h))

#ifdef __VERSE_REQUIRE_PORTABLE_SWAP__

uint16_t verse_bswap16(uint16_t a) { return (SWAP(a, 0, 1)); }
uint32_t verse_bswap32(uint32_t a) { return (SWAP(a, 0, 3) | SWAP(a, 1, 2)); }
uint64_t verse_bswap64(uint64_t a) {
	return (SWAP(a, 0, 7) | SWAP(a, 1, 6) | SWAP(a, 2, 5) | SWAP(a, 3, 4));
}

#endif

#ifdef __VERSE_REQUIRE_PORTABLE_ENDIAN__

uint16_t verse_to_be16(uint16_t x) {
	uint8_t *ptr = (uint8_t *)&x;
	return MK16(B32(ptr, 0), B32(ptr, 1));
}

uint16_t verse_to_le32(uint16_t x) {
	uint8_t *ptr = (uint8_t *)&x;
	return MK32(B32(ptr, 1), B32(ptr, 0));
}

uint32_t verse_to_be32(uint32_t x) {
	uint8_t *ptr = (uint8_t *)&x;
	return MK32(B32(ptr, 0), B32(ptr, 1), B32(ptr, 2), B32(ptr, 3));
}

uint32_t verse_to_le32(uint32_t x) {
	uint8_t *ptr = (uint8_t *)&x;
	return MK32(B32(ptr, 3), B32(ptr, 2), B32(ptr, 1), B32(ptr, 0));
}

uint64_t verse_to_be64(uint64_t x) {
	uint8_t *ptr = (uint8_t *)&x;
	return MK64(B64(ptr, 0), B64(ptr, 1), B64(ptr, 2), B64(ptr, 3), B64(ptr, 4),
	            B64(ptr, 5), B64(ptr, 6), B64(ptr, 7));
}

uint64_t verse_to_le64(uint64_t x) {
	uint8_t *ptr = (uint8_t *)&x;
	return MK64(B64(ptr, 7), B64(ptr, 6), B64(ptr, 5), B64(ptr, 4), B64(ptr, 3),
	            B64(ptr, 2), B64(ptr, 1), B64(ptr, 0));
}

uint16_t verse_from_be16(uint16_t x) { return verse_to_be16(x); }
uint32_t verse_from_be32(uint32_t x) { return verse_to_be32(x); }
uint64_t verse_from_be64(uint64_t x) { return verse_to_be64(x); }
uint16_t verse_from_le16(uint16_t x) { return verse_to_le16(x); }
uint32_t verse_from_le32(uint32_t x) { return verse_to_le32(x); }
uint64_t verse_from_le64(uint64_t x) { return verse_to_le64(x); }

#endif
