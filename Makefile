.PHONY: all build coq clean clean-coq-generated

RM := rm -f

all: build

build:
	opam exec -- dune build

coq:
	opam exec -- coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq
	$(MAKE) clean-coq-generated

clean-coq-generated:
	python -c "from pathlib import Path; pats=('*.vo','*.vos','*.vok','*.glob','.*.aux'); [p.unlink() for pat in pats for p in Path('theories').rglob(pat) if p.is_file()]; [p.unlink() for p in map(Path, ('Makefile.coq','Makefile.coq.conf','.Makefile.coq.d','.lia.cache','.nia.cache')) if p.exists()]"

clean:
	opam exec -- dune clean
	$(MAKE) clean-coq-generated
