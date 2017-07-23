.PHONY: all verify-% __force__

FSTAR = fstar.exe

EXERCISES =\
  ex_bst\
  ex_while\
  ex5a-rev\
  ex5b-fib

all: $(EXERCISES:%=verify-%)

verify-%: __force__
	$(FSTAR) $*.fst
