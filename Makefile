PROJECT = binary-relations
IPKG = $(PROJECT).ipkg

.PHONY: all install clean

all:
	idris --build $(IPKG)

install:
	idris --install $(IPKG)

clean:
	idris --clean $(IPKG)
