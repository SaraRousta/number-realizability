COQMAKEFILE := Makefile.coq

.PHONY: all clean html

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) all

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) clean

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

COQDOCFLAGS := \
  --toc --toc-depth 3 --html --interpolate --short \
  --index indexpage --no-lib-name --parse-comments \
  --with-header coqdocjs/extra/header.html \
  --with-footer coqdocjs/extra/footer.html

include coqdocjs/Makefile.doc

html: coqdoc
	cp html/indexpage.html html/index.html