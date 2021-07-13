# Artifact Guide: Data-Driven Abductive Inference of Library Specifications

This document describes installation and use of Elrond, an OCaml tool
for data-driven abduction of black-box library method specifications.
This is the accompanying artifact for the OOPSLA 2021 submission
*Data-Driven Abductive Inference of Library Specifications* by Zhou et
al.


## TODO

* Re-add this comment somewhere?
  `python3 bin/evaluation_tool.py weakening config/standard.config -tb 3600 -l` sets the time bound(in seconds) for weakening inference, the default time bound is `3600` seconds.

* Add suggested hardware requirements (i.e. RAM and hard disk)

* Stipulate that reviews might need to disable memory limits in docker

* Include our own docker image

* Add a command to run a single benchmark to the ‘Getting Started’ guide, so reviewers have a sense things are actually working

* Include lists of claims supported and not supported by the artifact


## Requirements

* Docker, which may be installed according to [the official
  installation instructions](https://docs.docker.com/get-docker/).
  This guide was tested using Docker version 20.10.7, but any
  contemporary Docker version is expected to work.


## Getting Started

This artifact is built as a Docker image. Before proceeding, ensure
Docker is installed. (On *nix, `sudo docker run hello-world` will test
your installation.) If Docker is not installed, install it via the
[official installation guide](https://docs.docker.com/get-docker/).

### Using the Pre-Built Docker Image

**TODO**

### Building the Docker Image

To build the Docker image yourself, navigate to the directory
containing the Dockerfile and tell Docker to build:

    # docker build . --tag elrond

### Running the Docker Image

To launch a shell in the Elrond Docker image, say:

    # docker run -it elrond

You can print Elrond's help message to verify the tool is operating
successfully:

    $ ./main.exe --help

When you are finished using the image, you may stop it by terminating
the shell with `exit`.


##  Running Benchmarks

##### Comprehensive Scripts

The following scripts run the benchmark suite displayed in Table 4 of
the paper:

* `./bin/run_benchmarks_short.sh` executes all shorter-running benchmarks (~ 1 to 2 hours).
* `./bin/run_benchmarks_long.sh` executes all longer-running benchmarks (> 10 hours).
* `./bin/visualize_running_result.sh` visualizes from results which were just run (immediate).

##### Detailed Steps

The above scripts automate the following process:

1. Use Elrond to find consistent (but not weakened) specification mappings:

    `$ python3 bin/evaluation_tool.py consistent config/standard.config`

   Output of these mappings is stored in the `_benchmark_<name>` directories.

2. Use Elrond to weaken the consistent specifications. There are six
   benchmarks labeled as `Limit` in Table 4 which take more than one hour
   to complete. We have grouped these long-running benchmarks separately;
   you may execute the shorter-running weakening benchmarks with:

    `$ python3 bin/evaluation_tool.py weakening config/standard.config -s`

   and the longer-running weakening benchmarks with:

    `$ python3 bin/evaluation_tool.py weakening config/standard.config -l`

   Output is again stored in the `_benchmark_<name>` directories.

3. Calculate the times needed for the SMT solver to find a sample
   allowed by a weakened solution but not the initial one (`time𝑑` in
   Table 4.) This calculation is not a core part of Elrond, but rather a
   post-processing step for our experimental evaluation.

    `$ python3 bin/evaluation_tool.py diff config/standard.config`

4. Count the total positive feature vectors in the space of
   weakenings (`|𝜙+|` in Table 4). Again, this is a post-processing step
   for our experimental evaluation rather than a core part of Elrond.

   There are three cells in Table 4 shown in blue, indicating the benchmarks
   timed out in our testing. You can perform the counting for all benchmarks
   except these three which timed out with:

    `$ python3 bin/evaluation_tool.py count config/standard.config -s`

   To run the counting for the three benchmarks which timed out for us, say:

    `$ python3 bin/evaluation_tool.py count config/standard.config -l`

   The latter command may obviously take a long time to complete.

5. Build the table:

    `$ python3 bin/evaluation_tool.py table config/standard.config`

  The table may be displayed at any stage of the benchmark process;
  any missing entries will be displayed as `None`.

##### Building Figure 5

`python3 bin/evaluation_tool.py figure config/prebuilt.config`
generates Figure 5 from the weakening experimental results. The
figure is saved in the output directory.

##### Building From Saved Results

`./bin/visualize_prebuilt_result.sh` visualizes from prebuilt results
(immediate).


## Running Elrond

Elrond requires both a source file and assertion file as input, and
outputs results in JSON format to some output directory. The input
source and assertion files for the benchmark suite are located in the
`~/ADT-Lemma-Discovery/data` directory in the Docker image.

The command to run an individual input without weakening is:

    $ ./main.exe infer consistent <source_file> <assertion_file> <output_dir>

For example,

    $ ./main.exe infer consistent data/bankersq.ml data/bankersq_assertion1.ml bankersq_out

will run the `bankersq` benchmark, writing results to the
`_bankersq_out` directory.

To find weakened specification mappings, first run the benchmark
without weakening as above, then say:

    $ ./main.exe infer weakening <output_dir>

on the same `<output_dir>`. For example,

    $ ./main.exe infer weakening bankersq_out

will perform weakening on the `bankersq` benchmark we executed above.

Alternately, you may run the full inference-with-weakening pipeline at
once by saying:

    $ ./main.exe infer full <source_file> <assertion_file> <output_dir>

For example, we can recreate the `bankersq` output directory in one pass:

    $ rm -rf _bankersq_out
    $ ./main.exe infer full data/bankersq.ml data/bankersq_assertion1.ml bankersq_out


## Displaying Specification Mappings

The following command displays inferred specifications before weakening:

    $ ./main.exe show consistent <output_dir>

where `<output_dir>` is the location of Elrond inference output.

For example, to infer and display specifications from the paper's
motivating example (called `exampleout` in this artifact), run the
following commands:

    $ ./main.exe full data/customstack.ml data/customstack_assertion1.ml exampleout -sb 4
    $ ./main.exe show consistent exampleout

(Here, the `-sb 4` flag limits the sampling bound to small number in order to simulate a biased test generator.)

This yields the following result:

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

The following command displays the weakened specification mappings
(`-s` asks for simplified specifications):

    $ ./main.exe show weakening <output_dir> -s

For example, the following command displays weakened specifications
for the paper's motivating example (assuming the specifications have
already been found as above):

    $ ./main.exe show weakening exampleout

This yields the output:

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


## Input File Formats

Elrond expects both an input OCaml code listing and an assertion
file. The input code listing is given as a specially formatted
OCaml source file with certain restrictions, and looks as follows:

```c
(* The library signature. *)
module type DT_NAME = sig
  type TP_NAME
  ...
  val VAR: FUNC_TP
  ...
end

(* The type of the client function. *)
val VAR: FUNC_TP

(* The client implementation. *)
let [rec] VAR (VAR: ARG_TP) ... = EXPR
```

The all-caps placeholders are filled according to the following
grammar:

```c
DT_NAME:= string
TP_NAME:= string | DT_NAME "." TP_NAME
ARG_TP:= "int" | "bool" | TP_NAME
RET_TP:= "int" | "bool" | TP_NAME | "(" FUNC_TP "," ... ")"
FUNC_TP:= RET_TP | ARG_TP "->" FUNC_TP

VAR := string
VAR_TUPLE := VAR | "(" VAR "," ... ")"
Lit := integer | boolean
OP := "+" | "<=" | ">=" | ">" | "<" | "=="
FUNC_APP := FUNC_NAME | FUNC_APP VAR
CASE := "| _ when" EXPR "->" EXPR
EXPR :=
| "if" FUNC_APP "then" EXPR "else" EXPR
| VAR
| EXPR OP EXPR
| "(" EXPR "," ... ")"
| FUNC_NAME
| EXPR EXPR
| "let" VAR_TUPLE : ARG_TP "=" EXPR "in" EXPR
| match VAR_TUPLE with CASE ...
```

The input source file must observe the following rules:

* The type in signature must be abstract.
* The input type of a function is a list of `ARG_TP`, and the output
  type of a function is written as a tuple.
* The condition of an `if` statement must be a single function application.
* The match cases in `match` statements must be written as `| _ ->
when CASE` instead of `| CASE`. (This is because we use the OCaml
parser, which asks that the matched case be an application of a
datatype constructor. However, here the type is abstract.)
* New variables must be typed when they first appear (we do not
  perform any type inference).
+ All variables must have distinct names (we do not do perform any
  alpha renaming).

The assertion file is formatted as follows:

```c
(* Predicates *)
let preds = [| PRED; ...|]

(* Precondtion (optional) *)
let pre VAR (IVAR: ARG_TP) ... (OVAR: ARG_TP) ... (QVAE: ARG_TP) ... = ASSERTION
(* Postcondtion *)
let post VAR (IVAR: ARG_TP) ... (OVAR: ARG_TP) ... (QVAE: ARG_TP) ... = ASSERTION
```

where the all-caps placeholders are filled according to the following
grammar:

```c
DT_NAME:= string
TP_NAME:= string | DT_NAME "." TP_NAME
ARG_TP:= "int" | "bool" | TP_NAME

IVAR := string
OVAR := string
QVAR := string

PRED := "mem" | "hd" | "ord" | "once" | "left" | "right" | "para" | "ance" | "root"
OP := "==" | "!=" | "<=" | ">=" | "<" | ">"

ASSERTION :=
| PRED VAR ...
| VAR OP VAR
| implies ASSERTION ASSERTION
| iff ASSERTION ASSERTION
| ASSERTION "&&" ASSERTION
| ASSERTION "||" ASSERTION
| NOT ASSERTION
```

Currently, implementations of libraries and predicates are fixed; users can define
their own assertions, but not their own libraries or predicates.


## Coq Formalization

The Coq proofs of our inferred specifications are located in the
`proof` directory. These proofs may be executed by running `make`.
Each file with prefix `Verify` contains the proof of one inferred
specification.

Proof obligations expressed in Coq may be generated via:

    $ dune exec -- main/main.exe coq  <specificaion mapping file> <function name>

This command converts the inferred specification mappings to the Coq
lemmas for manual proof. For example, running:

    $ dune exec -- main/main.exe coq _data/_result/_customstk1/_oracle_maximal.json Customstk.push

prints several lemmas:

```
Lemma Customstk.push_1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_member  il_1 u_0)) -> (not (list_head  il_1 u_0))).
```

Here, `push_spec` is the pre-defined specification of `push` (see
`proof/.*Aux.v*`) and `(((not (u_0 = i_0))/\(list_member il_1 u_0)) ->
(not (list_head il_1 u_0)))` is one branch of the inferred decision
tree. Proving all given lemmas establishes the correctness of the
inferred specifications.


## Artifact Structure

This section gives a brief overview of the files in this artifact.

* `bin/`: various scripts for collecting and displaying experimental results.
* `config/`: the configuration files for the benchmark scripts.
* `data/`: the benchmark input files.
  + `data/result.zip`: a collection of saved inference results.
* `frontend/`: the Elrond parser, a modified OCaml parser.
* `inference/`: the specification mapping inference modules, including both consistent inference and weakening inference.
* `language/`: Elrond's intermediate specification language.
* `ml/`: the decistion tree learner.
* `main/main.ml`: the main entry point of Elrond.
* `pred/`: built-in implementation of predicates.
* `proof/`: the coq proof generator.
* `solver/`: the Z3 (SMT solver) wrapper.
* `tp/`: Elrond's built-in types.
* `translate/`: VC generation.
  + `translate/imps.ml`: built-in implementation of libraries.
* `utils/`: miscellaneous utility functions.
