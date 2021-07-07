# Data-Driven Abductive Inference of Library Specifications
Data-Driven Abductive Inference of Library Specifications

## Dependency

- ocaml version: ocaml-base-compiler.4.08.1
- dune: 2.7.0
- z3 version: z3.4.7.1

## Build and Clean

+ run `./init.sh` first to initilize lexer and parser.
+ run `dune build` to build.
+ run `cp _build/default/bench/main.exe main.exe` to copy the tool to current path.
+ run `rm main.exe && dune clean && ./init_clean.sh` to clean the repo.

## Instructures

- run `./main.exe [arguments]` or `dune exec bench/main.exe [arguments]` to execute the tool.
- The tool first infers a consistent specification mapping, then tries to weaken it until maximal. The tool will serialize all results and statistic informations in json. 
  + Infer a specification mapping result and save the result to the target output directory(with a prefix "_"):

```
      ./main.exe consistent [sourcefile] [assertionfile] [outputdir]
```

  + Weaken the consistent specification mapping in the output directory and save maximal result in the same directory(need to run consistent inference first)::

```
      ./main.exe weakening [outputdir]
```

  + Do consistent inference and weakening consecutively.
  
```
      ./main.exe consistent [sourcefile] [assertionfile] [outputdir]
```
  
  + Show the consistent specification mappinp(if exists):

```
      ./main.exe show consistent [outputdir]
```

  + Show the consistent specification mappinp(if exists):
  
```
      ./main.exe show weakening [outputdir]
```

## Examples

- run `./main.exe full data/customstack.ml data/customstack_assertion1.ml exampleout` to infer consistent and maximal specification mapping.
- run `./main.exe show consistent exampleout` to show consistent specification mapping.

```
Customstk.top(il_0,i_0):=
forall u_0,(
 !(u_0==i_0) ||
 hd(il_0,i_0)
)
```

where `Customstk.top` is the library function name, `il_0,i_0` are the input and output of the library function, `u_0` is the univeral quantified variable. The specification means `Customstk.top` always returns the top element.
