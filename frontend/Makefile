# The main Makefile, fragments shared between Makefile and Makefile.nt
CAMLYACC=ocamlyacc
YACCFLAGS=-v --strict
YACCFLAGS=-v
CAMLLEX=ocamllex

world: parsing/lexer.ml parsing/parser.mli parsing/parser.ml

clean: partialclean

parsing/parser.mli parsing/parser.ml: parsing/parser.mly
	$(CAMLYACC) $(YACCFLAGS) parsing/parser.mly

partialclean::
	rm -f parsing/parser.mli parsing/parser.ml parsing/parser.output

beforedepend:: parsing/parser.mli parsing/parser.ml

# The lexer

parsing/lexer.ml: parsing/lexer.mll
	$(CAMLLEX) parsing/lexer.mll

partialclean::
	rm -f parsing/lexer.ml

beforedepend:: parsing/lexer.ml

default: world
