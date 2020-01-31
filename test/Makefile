TESTS=C.v TestCode.v

.PHONY: all clean
all:
	$(foreach test, ${TESTS}, coqc -R ../src Verse ${test};)
clean:
	echo "Someday there will be something to clean"
