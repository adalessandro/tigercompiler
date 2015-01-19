# Unix makefile for tigermain example

HOME=~
MOSMLHOME=/usr/bin
MOSMLTOOLS=camlrunm /usr/local/share/mosml/tools
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
    Tigercanon.uo Tigerframe.uo Tigerinterp.uo Tigerpila.uo Tigertrans.uo Tigertree.uo \
    Tigerassem.uo Tigersimpleregalloc.uo \
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
    Tigertrans.sml Tigerassem.sml \
    CantPrints.sml

	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
Tigermain.uo: Tigerseman.ui Tigerlex.uo Tigerpp.ui Tigerescap.ui \
    Tigerinterp.ui Tigerframe.ui Tigercanon.ui Tigerassem.ui Tigergrm.ui \
    Tigertrans.ui CantPrints.ui 
Tigertemp.uo: Tigertemp.ui 
CantPrints.uo: CantPrints.ui Tigerabs.uo 
Tigergrm.ui: Tigerabs.uo 
Tigersimpleregalloc.uo: Tigersimpleregalloc.ui Tigerassem.ui 
CantPrints.ui: Tigerabs.uo 
Tigerassem.uo: Tigerassem.ui Tigerframe.ui Tigerit.uo Tigertemp.ui 
Tigersres.uo: Tigerabs.uo Tigertips.uo Tigertab.ui Tigertemp.ui \
    Tigertrans.ui 
Tigerassem.ui: Tigertree.uo Tigertemp.ui 
Topsort.uo: Topsort.ui Tigerabs.uo Tigersres.uo Tigertips.uo Tigertab.ui 
Tigerpp.uo: Tigerpp.ui Tigerabs.uo 
Tigercanon.ui: Tigertree.uo Tigerframe.ui Tigertemp.ui 
Tigerseman.ui: Tigerabs.uo 
Tigerframe.ui: Tigertree.uo Tigertemp.ui 
Tigerpp.ui: Tigerabs.uo 
Tigerlex.uo: Tigergrm.ui Tigernlin.uo 
Tigerescap.uo: Tigerescap.ui Tigerabs.uo Tigertab.ui 
Tigerseman.uo: Tigerseman.ui Tigerabs.uo Tigersres.uo Tigerpila.ui \
    Tigertab.ui Topsort.ui Tigertrans.ui 
Tigerescap.ui: Tigerabs.uo 
Topsort.ui: Tigerabs.uo Tigertips.uo Tigertab.ui 
Tigertree.uo: Tigertemp.ui 
Tigerpila.uo: Tigerpila.ui 
Tigertrans.uo: Tigertrans.ui Tigerabs.uo Tigertree.uo Tigerframe.ui \
    Tigerpila.ui Tigerit.uo Tigertemp.ui 
Tigergrm.uo: Tigergrm.ui Tigerabs.uo Tigernlin.uo 
Tigerinterp.ui: Tigertree.uo Tigerframe.ui Tigertemp.ui 
Tigerframe.uo: Tigerframe.ui Tigertree.uo Tigertemp.ui 
Tigerit.uo: Tigertree.uo Tigertab.ui 
Tigercanon.uo: Tigercanon.ui Tigertree.uo Tigerframe.ui Tigertab.ui \
    Tigertemp.ui 
Tigerinterp.uo: Tigerinterp.ui Tigertree.uo Tigerframe.ui Tigertab.ui \
    Tigerit.uo Tigertemp.ui 
Tigertab.uo: Tigertab.ui 
Tigertrans.ui: Tigerabs.uo Tigertree.uo Tigerframe.ui Tigertemp.ui 
