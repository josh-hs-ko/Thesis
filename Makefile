THESISPATH = ~/Programs/Thesis
LIBPATH = ~/Programs/Agda/lib/src

all:	doc check

doc:
	runghc GenerateEverything.hs

check:
	time agda -i $(THESISPATH) -i $(LIBPATH) Everything.agda
#	time agda +RTS -K128M -RTS -i $(THESISPATH) -i $(LIBPATH) Everything.agda

clean:
	find . -name '*.agdai' -exec rm -f {} ';'
