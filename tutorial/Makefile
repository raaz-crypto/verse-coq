GENERATED=tutorial.html
.PHONY: all clean
all: ${GENERATED}

tutorial.html: tutorial.v
	coqdoc --html -R ../src/ Verse tutorial.v
clean:
	rm -f ${GENERATED}
