FSTAR=fstar.exe
STATE=ext.fst set.fsi heap.fst st.fst --admit_fsi FStar.Set

all : hoare cond-st hoare-shallow while

all-st : cond-st.fst hoare-shallow.fst
	$(FSTAR) $(STATE) $^

hoare : exp.fst swhile.fst hoare.fst
	$(FSTAR) $^

cond-st : cond-st.fst
	$(FSTAR) $(STATE) cond-st.fst

hoare-shallow : hoare-shallow.fst
	$(FSTAR) $(STATE) hoare-shallow.fst

while: arith.fst while.fst
	$(FSTAR) $^
