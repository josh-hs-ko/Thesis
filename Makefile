THESISPATH = ~/Programs
LIBPATH = ~/Programs/Agda/lib/src

all:	doc check

doc:
	runghc GenerateEverything.hs

check:
	time agda +RTS -K512M -RTS -i $(THESISPATH) -i $(LIBPATH) Everything.agda

clean:
	find . -name '*.agdai' -exec rm -f {} ';'
