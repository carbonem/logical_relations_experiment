# Thin wrapper around coq_makefile.
#
#   make               build every file listed in _CoqProject (default)
#   make clean         remove build artifacts
#   make CoqMakefile   force-regenerate the delegate makefile
#
# The real rules live in CoqMakefile, regenerated from _CoqProject
# whenever it or this file changes; CoqMakefile* is git-ignored.

KNOWNTARGETS := CoqMakefile
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
	@true
