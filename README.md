# Data-Driven Abductive Inference of Library Specifications
Data-Driven Abductive Inference of Library Specifications

## Dependency

- ocaml version: ocaml-base-compiler.4.08.1
- dune: 2.7.0
- z3 version: z3.4.7.1

## Build and Clean

+ run `./init.sh` first to initilize lexer and parser.
+ run `dune build` to build.
+ run `cp _build/default/main/main.exe main.exe` to copy the tool to current path.
+ run `rm main.exe && dune clean && ./init_clean.sh` to clean the repo.

## Benchmarks

  + The benchmarks are saved in `data` directory. The implementation of all predicates and library function are fixed now. The details binding is shown in `traslate/imps.ml` and `pred/pred.ml`.
  
  + Each benchmark consistent with a source file(includes the library signature and client code) and an assertion file(include predicates, precondition and postcondition, the precondition is optional).

  + Run `./run_benchmarks.sh consistent` to infer consistent specification mapping. Run `./run_benchmarks.sh consistent` to infer consistent and maximal specification(will take serveal hours). The results and log file are saved in `_benchmark_.*` directories.

## Detail Execution Instructions

- run `./main.exe <arguments>` or `dune exec -- main/main.exe <arguments>` to execute the tool.
- run `./main.exe --help` or `dune exec -- main/main.exe --help` to show instructions.
- The tool first infers a consistent specification mapping, then tries to weaken it until maximal. The tool will serialize all results and statistic informations in json. 
  + Infer a specification mapping result and save the result to the target output directory(with a prefix "_"):

```
      ./main.exe infer consistent <sourcefile> <assertionfile> <outputdir>
```

  + Weaken the consistent specification mapping in the output directory and save maximal result in the same directory(need to run consistent inference first)::

```
      ./main.exe infer weakening <outputdir>
```

  + Do consistent inference and weakening consecutively.
  
```
      ./main.exe infer full <sourcefile> <assertionfile> <outputdir>
```
  
  + Show the consistent specification mappinp(if exists):

```
      ./main.exe show consistent <outputdir>
```

  + Show the consistent specification mappinp(if exists):
  
```
      ./main.exe show weakening <outputdir>
```

## Example in Motivation Section

- run `./main.exe full data/customstack.ml data/customstack_assertion1.ml exampleout -sb 4` to infer consistent and maximal specification mapping. The flag `-sb 4` limits the sampling bound to small number in order to simulate a biased test generator.
- run `./main.exe show consistent exampleout` to show consistent specification mapping. TODO: add explaination according the Figure 4 in the paper.

```
Customstk.push(i_0,il_0,il_1):=
forall u_0,(ite mem(il_1,u_0)
    (ite mem(il_0,u_0)
        (
         !(u_0==i_0) &&
         !hd(il_1,u_0)
        )
        ((u_0==i_0) && hd(il_1,i_0)))
    (
     !(u_0==i_0) &&
     (
      !mem(il_0,u_0) &&
      (
       !hd(il_0,u_0) &&
       !hd(il_1,u_0)
      )
     )
    ))
```

- run `./main.exe show weakening exampleout -s` to show maximal specification mapping. The flag `-s` means simplifing the specifications. TODO: add explaination according the Figure 5 in the paper.

```
Customstk.push(i_0,il_0,il_1):=
forall u_0,(ite mem(il_1,u_0)
    (
     (u_0==i_0) ||
     (
      mem(il_0,u_0) &&
      !hd(il_1,u_0)
     )
    )
    (
     !(u_0==i_0) &&
     (
      !mem(il_0,u_0) &&
      (
       hd(il_0,u_0) ||
       !hd(il_1,u_0)
      )
     )
    ))
```
