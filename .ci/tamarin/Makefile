TAMARIN_EXAMPLES = basic-hash signedDH signedKEM signedDH+KEM ntor acme
TAMARIN_FILES = $(wildcard $(addsuffix /Tamarin/*.spthy, $(TAMARIN_EXAMPLES)))
TAMARIN_CHECKED = $(addsuffix .checked, $(TAMARIN_FILES))

all: $(TAMARIN_CHECKED)

%.spthy.checked: %.spthy
	tamarin-prover $(subst .checked,,$<) --prove --quit-on-warning
