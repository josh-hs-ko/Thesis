THESISPATH = ~/Programs
LIBPATH = ~/Programs/Agda/lib/src

all:
	runghc GenerateEverything.hs
	time agda +RTS -K512M -RTS -i $(THESISPATH) -i $(LIBPATH) Everything.agda
