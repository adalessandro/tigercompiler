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

GRALOBJS= Abs.uo Grm.uo Lex.uo Main.uo \
	Nlin.uo Tigerpp.uo Escap.uo Tab.uo Seman.uo Temp.uo Topsort.uo \
    Canon.uo Frame.uo Interp.uo Pila.uo Trans.uo Tree.uo \
    Assem.uo Simpleregalloc.uo Graph.uo Flow.uo Coloring.uo \
 	Tigerextras.uo

all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) Main.uo

Grm.sml Grm.sig: Grm.y 
	$(MOSMLYACC) Grm.y

Lex.sml: Lex.lex
	$(MOSMLLEX) Lex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) Grm.output
	$(REMOVE) Grm.sig
	$(REMOVE) Grm.sml
	$(REMOVE) Lex.sml
	$(REMOVE) Main
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: Abs.sml Grm.sml Lex.sml Main.sml \
	Nlin.sml Tigerpp.sml Topsort.sml \
    Trans.sml Assem.sml

	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
Frame.uo: Frame.ui Temp.ui Tigerit.uo Tree.uo Tigerextras.uo 
Seman.uo: Seman.ui Trans.ui Tab.ui Topsort.ui Abs.uo Sres.uo Pila.ui 
Main.uo: Tigerpp.ui Trans.ui Interp.ui Seman.ui Grm.ui Temp.ui Escap.ui \
    Frame.ui Canon.ui Lex.uo Tree.uo Assem.ui Coloring.uo 
Seman.ui: Abs.uo 
Canon.uo: Canon.ui Tab.ui Temp.ui Frame.ui Tree.uo 
Trans.ui: Temp.ui Frame.ui Abs.uo Tree.uo 
Tree.uo: Temp.ui 
Lex.uo: Nlin.uo Grm.ui 
Pila.uo: Pila.ui 
Simpleregalloc.ui: Temp.ui Frame.ui Assem.ui 
Trans.uo: Trans.ui Temp.ui Frame.ui Tigerit.uo Abs.uo Tree.uo Pila.ui 
Temp.uo: Temp.ui 
Interp.ui: Temp.ui Frame.ui Tree.uo 
Grm.uo: Grm.ui Nlin.uo Abs.uo 
Graph.uo: Graph.ui Tab.ui Tigerextras.uo 
Topsort.uo: Topsort.ui Tab.ui Abs.uo Sres.uo Tips.uo 
Tigerpp.uo: Tigerpp.ui Abs.uo 
Canon.ui: Temp.ui Frame.ui Tree.uo 
Simpleregalloc.uo: Simpleregalloc.ui Temp.ui Frame.ui Assem.ui 
Tigerpp.ui: Abs.uo 
Escap.ui: Abs.uo 
Sres.uo: Tab.ui Trans.ui Temp.ui Abs.uo Tips.uo 
Assem.ui: Temp.ui Frame.ui Tree.uo 
Escap.uo: Escap.ui Tab.ui Abs.uo 
Flow.uo: Tab.ui Temp.ui Graph.ui Assem.ui 
Grm.ui: Abs.uo 
Topsort.ui: Tab.ui Abs.uo Tips.uo 
Frame.ui: Temp.ui Tree.uo 
Assem.uo: Assem.ui Temp.ui Frame.ui Tigerextras.uo 
Interp.uo: Interp.ui Tab.ui Temp.ui Frame.ui Tigerit.uo Tree.uo 
Coloring.uo: Tab.ui Simpleregalloc.ui Temp.ui Graph.ui Flow.uo Frame.ui \
    Assem.ui Pila.ui Tigerextras.uo 
Tigerit.uo: Tab.ui Tree.uo 
Graph.ui: Tab.ui 
Tab.uo: Tab.ui 
