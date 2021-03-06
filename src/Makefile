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

GRALOBJS= \
	Abs.uo \
	Assem.uo \
	Canon.uo \
	Codegen.uo \
	Coloring.uo \
	Escap.uo \
	Flow.uo \
	Frame.uo \
	Graph.uo \
	Grm.uo \
	Interp.uo \
	Lex.uo \
	Main.uo \
	Nlin.uo \
	Pila.uo \
	Seman.uo \
	Simpleregalloc.uo \
	Sres.uo \
	Tab.uo \
	Temp.uo \
	Tigerextras.uo \
	Tigerit.uo \
	Tigerpp.uo \
	Tips.uo \
	Topsort.uo \
    Trans.uo \
	Tree.uo

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
	$(REMOVE) tiger
	$(REMOVE) a.out output.s

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: \
	Abs.sml \
	Assem.sml \
	Canon.sml \
	Codegen.sml \
	Coloring.sml \
	Escap.sml \
	Flow.sml \
	Frame.sml \
	Graph.sml \
	Grm.sml \
	Interp.sml \
	Lex.sml \
	Main.sml \
	Nlin.sml \
	Pila.sml \
	Seman.sml \
	Simpleregalloc.sml \
	Sres.sml \
	Tab.sml \
	Temp.sml \
	Tigerextras.sml \
	Tigerit.sml \
	Tigerpp.sml \
	Tips.sml \
	Topsort.sml \
	Trans.sml \
	Tree.sml

	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
Frame.uo: Frame.ui Temp.ui Tigerit.uo Tree.uo Assem.ui Tigerextras.uo 
Seman.uo: Seman.ui Trans.ui Tab.ui Topsort.ui Abs.uo Sres.uo Pila.ui \
    Tigerextras.uo 
Main.uo: Tigerpp.ui Trans.ui Interp.ui Seman.ui Grm.ui Temp.ui Escap.ui \
    Frame.ui Canon.ui Lex.uo Tree.uo Assem.ui Coloring.uo Tigerextras.uo \
    Codegen.ui 
Seman.ui: Abs.uo 
Canon.uo: Canon.ui Tab.ui Temp.ui Frame.ui Tree.uo 
Trans.ui: Temp.ui Frame.ui Abs.uo Tree.uo 
Tree.uo: Temp.ui 
Lex.uo: Nlin.uo Grm.ui 
Pila.uo: Pila.ui 
Simpleregalloc.ui: Temp.ui Frame.ui Assem.ui 
Trans.uo: Trans.ui Temp.ui Frame.ui Abs.uo Tree.uo Pila.ui Tigerextras.uo 
Temp.uo: Temp.ui 
Interp.ui: Temp.ui Frame.ui Tree.uo 
Grm.uo: Grm.ui Nlin.uo Abs.uo 
Graph.uo: Graph.ui Tab.ui Tigerextras.uo 
Topsort.uo: Topsort.ui Tab.ui Abs.uo Sres.uo Tigerextras.uo Tips.uo 
Tigerpp.uo: Tigerpp.ui Abs.uo 
Canon.ui: Temp.ui Frame.ui Tree.uo 
Simpleregalloc.uo: Simpleregalloc.ui Temp.ui Frame.ui Assem.ui \
    Tigerextras.uo Codegen.ui 
Tigerpp.ui: Abs.uo 
Escap.ui: Abs.uo 
Codegen.uo: Codegen.ui Temp.ui Frame.ui Assem.ui Tree.uo Tigerextras.uo 
Sres.uo: Tab.ui Trans.ui Temp.ui Abs.uo Tips.uo 
Assem.ui: Temp.ui 
Escap.uo: Escap.ui Tab.ui Abs.uo 
Flow.uo: Tab.ui Temp.ui Graph.ui Assem.ui Tigerextras.uo 
Grm.ui: Abs.uo 
Topsort.ui: Tab.ui Abs.uo Tips.uo 
Frame.ui: Temp.ui Tree.uo Assem.ui 
Codegen.ui: Frame.ui Assem.ui Tree.uo 
Assem.uo: Assem.ui Temp.ui Tigerextras.uo 
Interp.uo: Interp.ui Tab.ui Temp.ui Frame.ui Tigerit.uo Tree.uo 
Coloring.uo: Tab.ui Simpleregalloc.ui Temp.ui Graph.ui Flow.uo Frame.ui \
    Assem.ui Pila.ui Tigerextras.uo Codegen.ui 
Tigerit.uo: Tab.ui Tree.uo 
Graph.ui: Tab.ui 
Tab.uo: Tab.ui 
