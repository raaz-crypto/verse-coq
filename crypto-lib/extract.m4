dnl This is an m4 template that generates the extraction line for an
dnl implementation of a primitive in verse.

define(`EXTRACT_IT',`
	define(`PRIM',$1)dnl
	define(`ARCH',$2)dnl
	define(`FEATURES',$3)dnl
	define(`ML_FILE',ML_DIR/PRIM/ARCH/FEATURES)dnl
	define(`OUT_FILE',VERSE_DIR/PRIM/ARCH/FEATURES)dnl
	define(`C_FUN',verse`_'PRIM`_'ARCH`_'FEATURES)dnl
	define(`COQ_FUN',PRIM`_'ARCH`_'FEATURES)dnl
	define(`VERSE_MOD',`Verse.CryptoLib.'PRIM`.'ARCH`.'FEATURES)dnl

Require VERSE_MOD.
Definition COQ_FUN : unit
	   := VERSE_MOD`.implementation'
	      "OUT_FILE"
	      "C_FUN".

Extraction "ML_FILE" COQ_FUN.
')dnl
define(`EXTRACT',`EXTRACT_IT(patsubst($1,`/',`,'))')dnl
