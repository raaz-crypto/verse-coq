#pragma once
#include <stdint.h>

/*
 *         Byte swapping. Use platform specific ones when we know it.
 */

#ifdef PLATFORM_OSX
#include <libkern/OSByteOrder.h> /* For PLATFORM OSX */

static inline uint16_t verse_bswap16(uint16_t x) { return OSSwapInt16(x); }
static inline uint32_t verse_bswap32(uint32_t x) { return OSSwapInt32(x); }
static inline uint64_t verse_bswap64(uint64_t x) { return OSSwapInt64(x); }

#elif defined(PLATFORM_WINDOWS)
#include <stdlib.h>
static inline uint16_t verse_bswap16(uint16_t x) { return _byteswap_ushort(x); }
static inline uint32_t verse_bswap32(uint32_t x) { return _byteswap_ulong(x); }
static inline uint64_t verse_bswap64(uint64_t x) { return _byteswap_uint64(x); }

#elif defined(PLATFORM_OPENBSD)
#include <endian.h>
static inline uint16_t verse_bswap16(uint16_t x) { return swap16(x); }
static inline uint32_t verse_bswap32(uint32_t x) { return swap32(x); }
static inline uint64_t verse_bswap64(uint64_t x) { return swap64(x); }

#elif defined(PLATFORM_LINUX) /* All other platforms */
#include <byteswap.h>
static inline uint16_t verse_bswap16(uint16_t x) { return bswap_16(x); }
static inline uint32_t verse_bswap32(uint32_t x) { return bswap_32(x); }
static inline uint64_t verse_bswap64(uint64_t x) { return bswap_64(x); }
#else

/* We do not have platform specific byte swap */
#define __VERSE_REQUIRE_PORTABLE_SWAP__

extern uint16_t verse_bswap16(uint16_t x);
extern uint32_t verse_bswap32(uint32_t x);
extern uint64_t verse_bswap64(uint64_t x);

#endif

#ifdef __GNUC__

/* For GNUC compiler use byte order checks to define efficient endian
 * conversion */

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__

static inline uint16_t verse_to_be16(uint16_t x) { return verse_bswap16(x); }
static inline uint32_t verse_to_be32(uint32_t x) { return verse_bswap32(x); }
static inline uint64_t verse_to_be64(uint64_t x) { return verse_bswap64(x); }
static inline uint16_t verse_from_be16(uint16_t x) { return verse_bswap16(x); }
static inline uint32_t verse_from_be32(uint32_t x) { return verse_bswap32(x); }
static inline uint64_t verse_from_be64(uint64_t x) { return verse_bswap64(x); }

static inline uint16_t verse_to_le16(uint16_t x) { return x; }
static inline uint32_t verse_to_le32(uint32_t x) { return x; }
static inline uint64_t verse_to_le64(uint64_t x) { return x; }
static inline uint16_t verse_from_le16(uint16_t x) { return x; }
static inline uint32_t verse_from_le32(uint32_t x) { return x; }
static inline uint64_t verse_from_le64(uint64_t x) { return x; }

#else

static inline uint16_t verse_to_be16(uint16_t x) { return x; }
static inline uint32_t verse_to_be32(uint32_t x) { return x; }
static inline uint64_t verse_to_be64(uint64_t x) { return x; }
static inline uint16_t verse_from_be16(uint16_t x) { return x; }
static inline uint32_t verse_from_be32(uint32_t x) { return x; }
static inline uint64_t verse_from_be64(uint64_t x) { return x; }

static inline uint16_t verse_to_le16(uint16_t x) { return verse_bswap16(x); }
static inline uint32_t verse_to_le32(uint32_t x) { return verse_bswap32(x); }
static inline uint64_t verse_to_le64(uint64_t x) { return verse_bswap64(x); }
static inline uint16_t verse_from_le16(uint16_t x) { return verse_bswap16(x); }
static inline uint32_t verse_from_le32(uint32_t x) { return verse_bswap32(x); }
static inline uint64_t verse_from_le64(uint64_t x) { return verse_bswap64(x); }

#endif /* Byte order */

#else /* Not __GNUC__ use portable implementations */
#define __VERSE_REQUIRE_PORTABLE_ENDIAN__

extern uint16_t verse_to_be16(uint16_t x);
extern uint32_t verse_to_be32(uint32_t x);
extern uint64_t verse_to_be64(uint64_t x);
extern uint16_t verse_to_le16(uint16_t x);
extern uint32_t verse_to_le32(uint32_t x);
extern uint64_t verse_to_le64(uint64_t x);

extern uint16_t verse_from_be16(uint16_t x);
extern uint32_t verse_from_be32(uint32_t x);
extern uint64_t verse_from_be64(uint64_t x);
extern uint16_t verse_from_le16(uint16_t x);
extern uint32_t verse_from_le32(uint32_t x);
extern uint64_t verse_from_le64(uint64_t x);

#endif

/*
 *         Rotation functions.
 */

static inline uint16_t verse_rotL16(uint16_t w, uint16_t c) {
	return (w << c) | (w >> (16 - c));
}

static inline uint32_t verse_rotL32(uint32_t w, uint32_t c) {
	return (w << c) | (w >> (32 - c));
}

static inline uint64_t verse_rotL64(uint64_t w, uint64_t c) {
	return (w << c) | (w >> (64 - c));
}

static inline uint16_t verse_rotR16(uint16_t w, uint16_t c) {
	return (w >> c) | (w << (16 - c));
}

static inline uint32_t verse_rotR32(uint32_t w, uint32_t c) {
	return (w >> c) | (w << (32 - c));
}

static inline uint64_t verse_rotR64(uint64_t w, uint64_t c) {
	return (w >> c) | (w << (64 - c));
}
