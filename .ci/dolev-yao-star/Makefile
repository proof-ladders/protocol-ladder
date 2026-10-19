DY_FM_CRYPTO_LIB_HOME ?= .
FSTAR_EXE     ?= fstar.exe
COMPARSE_HOME ?= $(DY_FM_CRYPTO_LIB_HOME)/../comparse
DY_HOME       ?= $(DY_FM_CRYPTO_LIB_HOME)/../dolev-yao-star

INNER_SOURCE_DIRS = basic-hash/dolev-yao-star signedDH/dolev-yao-star

SOURCE_DIRS = $(addprefix $(DY_FM_CRYPTO_LIB_HOME)/, $(INNER_SOURCE_DIRS))

DY_INCLUDE_DIRS = core lib lib/comparse lib/communication lib/crypto lib/event lib/hpke lib/label lib/state lib/utils
INCLUDE_DIRS = $(SOURCE_DIRS) $(COMPARSE_HOME)/src $(addprefix $(DY_HOME)/src/, $(DY_INCLUDE_DIRS))
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

FSTAR_EXTRACT = --extract '-* +BasicHash +SignedDH +Comparse -Comparse.Tactic +DY'

# Allowed warnings:
# - (Warning 242) Definitions of inner let-rec ... and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types
# - (Warning 331) This name is being ignored
# - (Warning 335) Interface ... is admitted without an implementation 
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '@0..1000' --warn_error '+242+331-335' --cache_dir cache --odir obj --cmi $(OTHERFLAGS)

.PHONY: all clean

all: copy_lib

clean:
	rm -rf hints cache obj ml/lib/src ml/tests/src

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend
endif


# Verification

hints:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | hints obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction

ALL_LIB_ML_FILES = $(ALL_ML_FILES)
ALL_TEST_ML_FILES =

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib extract_tests copy_tests

extract_lib: $(ALL_LIB_ML_FILES)

copy_lib: extract_lib
	mkdir -p ml/lib/src
	cp $(ALL_LIB_ML_FILES) ml/lib/src

extract_tests: $(ALL_TEST_ML_FILES)

copy_tests: extract_tests

# Final binary

.PHONY: build check release

check: copy_lib copy_tests $(ALL_TEST_VECTORS_JSON)
	OCAMLRUNPARAM=b $(FSTAR_EXE) --ocamlenv dune runtest --force --no-buffer --display=quiet --profile=release

# Interactive mode support

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include $(DY_FM_CRYPTO_LIB_HOME)/cache
