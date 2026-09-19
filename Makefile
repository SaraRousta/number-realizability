COQMAKEFILE := Makefile.coq

.PHONY: all clean html

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) all

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) clean

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

include coqdocjs/Makefile.doc

html: coqdoc
	cp html/indexpage.html html/index.html