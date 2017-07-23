FSTAR=fstar.exe
LIST=set.fsi heap.fst st.fst all.fst list.fst --admit_fsi FStar.Set

all : 8a-acls insertionsort insertionsortcmp mergesort

8a-acls : 8a-acls.fst
	$(FSTAR) $(LIST) string.fst 8a-acls.fst

insertionsort : intsort.fst insertionsort.fst
	$(FSTAR) $(LIST) $^

insertionsortcmp : intsort.fst insertionsortcmp.fst
	$(FSTAR) $(LIST) $^

mergesort: intsort.fst mergesort.fst
	$(FSTAR) $(LIST) $^
