.PHONY: all verify-% __force__

FSTAR = fstar.exe

EXERCISES =\
  ex4a-append-intrinsic\
  ex4b-append-extrinsic\
  ex4c-mem\
  ex4e-find\
  ex4f-fold-left\
  ex4g-hd-tl\
  ex4h-nth\
  ex4d-reverse

all: $(EXERCISES:%=verify-%)

verify-%: __force__
	$(FSTAR) $*.fst
