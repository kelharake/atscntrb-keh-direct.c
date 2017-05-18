
INCLUDE 		+= -lgc
INCLUDE 		+= -ldill

INCLUDE 		+= $(patsubst %,-I %,$(subst :, ,$(PATSHOMELOCS)))
INCLUDE_ATS += $(patsubst %,-IATS %,$(subst :, ,$(PATSHOMELOCS)))

PATSCC=patscc
PATSCC2=$(PATSCC) $(INCLUDE) $(INCLUDE_ATS)

CC=gcc

all: basic-test0.out session-test0.out session-test1.out

%.out: %.dats
	$(PATSCC2) -DATS_MEMALLOC_LIBC $(INCLUDE) -o $@ $<

clean:
	rm -f *.out
	rm -f *_dats.c

