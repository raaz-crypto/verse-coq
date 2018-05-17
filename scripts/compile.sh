#!/bin/bash

set -e

function usage
{
    echo "usage: $0 -v VERSE_PATH -o OUTPUT_NAME VERSE_SCRIPT || -h"
    echo "   ";
    echo "  -v | --verse-path        : Path to verse";
    echo "  -o | --output-name       : Name of the output file";
    echo "  -h | --help              : This message";
}

function parse_args
{
	while [ "$1" != "" ]; do
		case "$1" in
			-v | --verse-path )        PATH_TO_VERSE="$2";    shift;;
			-o | --output-name )       OUTPUT_FILE="$2";      shift;;
			-h | --help )              usage;                 exit;;
			* )                        VERSE_FILE="$1";
		esac
		shift
	done

	if [[ -z "${PATH_TO_VERSE}" || -z "${OUTPUT_FILE}" || -z "${VERSE_FILE}" ]]; then
		echo "Invalid arguments"
		usage
		exit;
	fi

}

function run
{
	parse_args "$@"

	FNAME=$(echo "$VERSE_FILE" | rev | cut -d '/' -f1 | rev)
	VERSE_FILE_TEMP=/tmp/$FNAME
	cp "$VERSE_FILE" "$VERSE_FILE_TEMP"

	echo "temp file done";

	EXTRACTION_CODE='
	Extraction Language Haskell.
	Extraction "code.hs" code layout.
	'

	echo "$EXTRACTION_CODE" >> "$VERSE_FILE_TEMP"

	echo "extraction done";

	coqc "$VERSE_FILE_TEMP" -R "$PATH_TO_VERSE" Verse

	sed -i 's|import qualified Prelude|import qualified Prelude\
import System.Environment\
import qualified Data.Bits\
import qualified Data.Char\
import qualified Data.List\
import qualified Control.Monad\
import Data.Maybe\n|g' code.hs

	sed -i 's|GHC.Prim.Any|()|g' code.hs

	FILE_WRITE_CODE='
main = do
    args <- getArgs
    let contents = layout (fromMaybe NilDoc code)
    Prelude.writeFile (args Prelude.!! 0) contents
'

	echo "$FILE_WRITE_CODE" >> code.hs

	runhaskell code.hs "$OUTPUT_FILE"

	rm code.hs

}

run "$@";
