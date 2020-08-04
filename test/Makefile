TESTS=TestCode.v
GENERATED=$(wildcard .*.aux *.glob *.vo)

.PHONY: all clean
all:
	$(foreach test, ${TESTS}, coqc -R ../src Verse ${test};)
clean:
	rm -f ${GENERATED}
