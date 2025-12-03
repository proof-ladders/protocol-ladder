PROVERIF_EXAMPLES = basic-hash signedDH ntor
PROVERIF_FILES = $(wildcard $(addsuffix /ProVerif/*.pv, $(PROVERIF_EXAMPLES)))
PROVERIF_CHECKED = $(addsuffix .checked, $(PROVERIF_FILES))

all: $(PROVERIF_CHECKED)

%.pv.checked: %.pv
	proverif $(subst .checked,,$<)
