#
# Students' Makefile for the Malloc Lab
#
TEAM = bovik
VERSION = 1
HANDINDIR = /afs/cs.cmu.edu/academic/class/15213-f01/malloclab/handin

CC = gcc
CFLAGS = -Wall -O2 -m32 -g

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o

mdriver: $(OBJS) ## Build the mdriver executable
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h ## Compile mdriver.o
memlib.o: memlib.c memlib.h ## Compile memlib.o
mm.o: mm.c mm.h memlib.h ## Compile mm.o
fsecs.o: fsecs.c fsecs.h config.h ## Compile fsecs.o
fcyc.o: fcyc.c fcyc.h ## Compile fcyc.o
ftimer.o: ftimer.c ftimer.h config.h ## Compile ftimer.o
clock.o: clock.c clock.h ## Compile clock.o

handin: ## Copy mm.c to handin directory
	cp mm.c $(HANDINDIR)/$(TEAM)-$(VERSION)-mm.c

clean: ## Remove generated files
	rm -f *~ *.o mdriver

run: clean mdriver ## Clean, build, and run mdriver
	./mdriver

help: ## Show this help message
	@echo "Available make targets:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | \
		awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-12s\033[0m %s\n", $$1, $$2}'
