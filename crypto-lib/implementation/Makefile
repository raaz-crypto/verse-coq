subdirs=c

.PHONY: all clean

all:
	$(foreach dir, ${subdirs}, make -C ${dir} all; )


clean:
	$(foreach dir, ${subdirs}, make -C ${dir} clean; )
