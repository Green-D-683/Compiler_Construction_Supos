Compiler Construction 2021
mjp217@cam.ac.uk 

This directory contains the basis of an L1 parser which we'll build
up during the supervisions using the structure provided in the 
original Slang interpreter.

With thanks to Tim Griffin who's original code has been used extensively

===============================================
Building 
===============================================
Install ocamlbuild.  Then do either 

  ocamlbuild l1.byte

===============================================
Usage 
===============================================

Usage: l1.byte [options] [<file>]
Options are:
  -V verbose front end
  -v verbose interpreter(s)
  -c show compiled code (but don't run it)
  -i0 Interpreter 0
  -all all interpreters
  -stackmax set max stack size (default = 1000)
  -heapmax set max heap size (default = 1000)
  -t run all test/*.l1 with each selected interpreter, report unexpected outputs (silent otherwise)
  -help  Display this list of options
  --help  Display this list of options


===============================================
Files
===============================================

Every .ml file has an associated .mli file describing its interface. 

errors.ml      : Error exception 
past.ml        : the Parsed AST, with pretty printing 
lexer.mll      : specification for ocamllex 
parser.mly     : specification for ocamlyacc 
ast.ml         : "internal" AST, with pretty printing  
past_to_ast.ml : translated from parsed to internal AST 
static.ml      : static analysis (check types and other rules) 
front_end.ml   : the front end : parse, static check, translate. 
free_vars.ml   : free variable calculation 
tests.ml       : code for parsing tests/manifest.txt and setting up testing. 
l1.ml       : main file, implementing the command-line for the interpreter and compiler 

Interpreters (In order of presentation in lectures)
interp_0.ml    : The "definitional" interpreter. 



               
