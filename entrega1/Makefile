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
    Tigercanon.uo Tigerframe.uo Tigerinterp.uo Tigerpila.uo Tigertrans.uo Tigertree.uo \
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
    Tigertrans.sml \
    CantPrints.sml

	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
Tigermain.uo: Tigerseman.ui Tigerlex.uo Tigerpp.ui Tigerescap.ui \
    Tigerinterp.ui Tigerframe.ui Tigercanon.ui Tigergrm.ui Tigertrans.ui \
    CantPrints.ui 
Tigergrm.uo: Tigergrm.ui Tigerabs.uo Tigernlin.uo 
Tigerpp.uo: Tigerpp.ui Tigerabs.uo 
Tigerinterp_postam.uo: Tigerinterp_postam.ui Tigertree.uo Tigerframe.ui \
    Tigertab.ui Tigerit.uo Tigertemp.ui 
Tigerframe.ui: Tigertree.uo Tigertemp.ui 
Tigerinterp_postam.ui: Tigertree.uo Tigerframe.ui Tigertemp.ui 
Tigersres.uo: Tigerabs.uo Tigertips.uo Tigertab.ui Tigertemp.ui \
    Tigertrans.ui 
Tigergrm.ui: Tigerabs.uo 
Tigertrans.uo: Tigertrans.ui Tigerabs.uo Tigertree.uo Tigerframe.ui \
    Tigerpila.ui Tigerit.uo Tigertemp.ui 
Tigercanon.uo: Tigercanon.ui Tigertree.uo Tigerframe.ui Tigertab.ui \
    Tigertemp.ui 
Topsort.ui: Tigerabs.uo Tigertips.uo Tigertab.ui 
Tigerit.uo: Tigertree.uo Tigertab.ui 
CantPrints.uo: CantPrints.ui Tigerabs.uo 
Tigerpila.uo: Tigerpila.ui 
Tigerescap.ui: Tigerabs.uo 
Tigerinterp_orig.uo: Tigertree.uo Tigerframe.ui Tigertab.ui Tigerit.uo \
    Tigertemp.ui 
Tigercanon.ui: Tigertree.uo Tigerframe.ui Tigertemp.ui 
Tigerseman.ui: Tigerabs.uo 
Tigertree.uo: Tigertemp.ui 
Topsort.uo: Topsort.ui Tigerabs.uo Tigersres.uo Tigertips.uo Tigertab.ui 
Tigertrans.ui: Tigerabs.uo Tigertree.uo Tigerframe.ui Tigertemp.ui 
Tigerinterp.uo: Tigerinterp.ui Tigertree.uo Tigerframe.ui Tigertab.ui \
    Tigerit.uo Tigertemp.ui 
Tigerinterp_actual.uo: Tigertree.uo Tigerframe.ui Tigertab.ui Tigerit.uo \
    Tigertemp.ui 
Tigerlex.uo: Tigergrm.ui Tigernlin.uo 
CantPrints.ui: Tigerabs.uo 
Tigerseman.uo: Tigerseman.ui Tigerabs.uo Tigersres.uo Tigerpila.ui \
    Tigertab.ui Topsort.ui Tigertrans.ui 
Tigerframe.uo: Tigerframe.ui Tigertree.uo Tigertemp.ui 
Tigertab.uo: Tigertab.ui 
Tigerinterp.ui: Tigertree.uo Tigerframe.ui Tigertemp.ui 
Tigerescap.uo: Tigerescap.ui Tigerabs.uo Tigertab.ui 
Tigertemp.uo: Tigertemp.ui 
Tigerpp.ui: Tigerabs.uo 
