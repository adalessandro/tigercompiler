# Unix makefile for tigermain example

HOME=~
MOSMLHOME=/usr/bin
MOSMLTOOLS=camlrunm /usr/share/mosml/tools
MOSMLLEX=mosmllex
MOSMLYACC=mosmlyac -v

GCC=gcc
CFLAGS= -g
MOSMLC=mosmlc -c -liberal
MOSMLL=mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo

GRALOBJS= Tigerabs.uo Tigergrm.uo Tigerlex.uo Tigermain.uo \
	Tigernlin.uo Tigerpp.uo Tigerescap.uo Tigertab.uo Tigerseman.uo Tigertemp.uo Topsort.uo \
    CantPrints.uo

all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) Tigermain.uo

Tigergrm.sml Tigergrm.sig: Tigergrm.y 
	$(MOSMLYACC) Tigergrm.y

Tigerlex.sml: Tigerlex.lex
	$(MOSMLLEX) Tigerlex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) Tigergrm.output
	$(REMOVE) Tigergrm.sig
	$(REMOVE) Tigergrm.sml
	$(REMOVE) Tigerlex.sml
	$(REMOVE) Tigermain
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: Tigerabs.sml Tigergrm.sml Tigerlex.sml Tigermain.sml \
	Tigernlin.sml Tigerpp.sml Topsort.sml \
    CantPrints.sml

	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
CantPrints.uo: CantPrints.ui Tigerabs.uo 
Topsort.uo: Topsort.ui Tigerabs.uo Tigersres.uo 
Tigerescap.uo: Tigerescap.ui Tigerabs.uo Tigertab.ui 
CantPrints.ui: Tigerabs.uo 
Tigerpp.ui: Tigerabs.uo 
Tigerpp.uo: Tigerpp.ui Tigerabs.uo 
Tigerseman.uo: Tigerseman.ui Tigerabs.uo Tigersres.uo Tigertab.ui \
    Topsort.ui 
Tigergrm.uo: Tigergrm.ui Tigerabs.uo Tigernlin.uo 
Tigersres.uo: Tigerabs.uo Tigertips.uo Tigertab.ui Tigertemp.ui 
Tigergrm.ui: Tigerabs.uo 
Tigerescap.ui: Tigerabs.uo 
Tigertab.uo: Tigertab.ui 
Tigermain.uo: Tigerseman.ui Tigerlex.uo Tigerpp.ui Tigerescap.ui \
    Tigergrm.ui CantPrints.ui 
Tigertemp.uo: Tigertemp.ui 
Tigerseman.ui: Tigerabs.uo 
Topsort.ui: Tigerabs.uo Tigertips.uo Tigertab.ui 
Tigerlex.uo: Tigergrm.ui Tigernlin.uo 
