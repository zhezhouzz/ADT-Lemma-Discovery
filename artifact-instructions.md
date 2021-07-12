# Artifact Guide: Data-Driven Abductive Inference of Library Specifications

This document describes installation and use of Elrond, an OCaml tool
for data-driven abduction of black-box library method specifications.
This is the accompanying artifact for the OOPSLA 2021 submission
*Data-Driven Abductive Inference of Library Specifications* by Zhou et
al.


## TODO

* Should we publish a Docker image instead of asking evaluators to
  build the Dockerfile directly?
  + [ZZ] Not sure, their website mentions "dockerfile", I think it's
    Ok. Anyway, as the artifact is developing thus dockerfile is
    better.
  + [RD] I'm guessing it's fine to submit a Dockerfile, but having the
    image ready to go would save a bunch of the evaluators' time. So,
    publishing an image seems like the nice thing to do if we have the
    time / resources. I'll leave this TODO here, but maybe we should
    consider it lower priority / nice-to-have.

* Add a section about the Coq formalization.

* Annotate the artifact structure.

* Improve output of the benchmark script; currently difficult to
  correlate the script's output to our evaluation figure (Table 4).
  There are several columns in Table 4; does our benchmark script give
  us all of these numbers?

* Document the input file formats.

* Running Other Programs -> Providing Other Assertions or similar.

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

1. Ensure Docker is installed. (On *nix, `sudo docker run hello-world`
will test your installation.) If Docker is not installed, install it
via the [official installation guide](https://docs.docker.com/get-docker/).

2. Navigate to the location of the Elrond Docker file.

   `# cd <Dockerfile dir>`

3. Build the Elrond Docker image.

    `# docker build . --tag elrond`

4. Launch a shell in the Elrond Docker image.

    `# docker run -it elrond`

5. Print Elrond's help message to verify the tool was installed
   successfully.

    `$ ./main.exe --help`

6. When you are finished, you may stop the Elrond image by terminating
the shell with `exit`.


##  Running Benchmarks

Experimental results on the benchmark suite displayed in Table 4 of
the paper can be obtained as follows:

1. Make sure you are in the root Elrond directory:

    `$ cd ~/ADT-Lemma-Discovery`

2. Use Elrond to find consistent (but not weakened) specification mappings:

    `$ python3 bin/evaluation_tool.py consistent config/standard.config`

   Output of these mappings is stored in the `_benchmark_<name>` directories.

3. Use Elrond to weaken the consistent specifications. There are six
   benchmarks labeled as `Limit` in Table 4 which take more than one hour
   to complete. We have grouped these long-running benchmarks separately;
   you may execute the shorter-running weakening benchmarks with:

    `$ python3 bin/evaluation_tool.py weakening config/standard.config -s`

   and the longer-running weakening bencharmsk with:

    `$ python3 bin/evaluation_tool.py weakening config/standard.config -l`

   Output is again stored in the `_benchmark_<name>` directories.

4. Calculate the times needed for the SMT solver to find a sample
   allowed by a weakened solution but not the initial one (`time𝑑` in
   Table 4.) This calculation is not a core part of Elrond, but rather a
   post-processing step for our experimental evaluation.

    `$ python3 bin/evaluation_tool.py diff config/standard.config`

5. Count the total positive feature vectors in the space of
   weakenings (`|𝜙+|` in Table 4). Again, this is a post-processing step
   for our experimental evaluation rather than a core part of Elrond.

   There are three cells in Table 4 shown in blue, indicating the benchmarks
   timed out in our testing. You can perform the counting for all benchmarks
   except these three which timed out with:

    `$ python3 bin/evaluation_tool.py count config/standard.config -s`

   To run the counting for the three benchmarks which timed out for us, say:

    `$ python3 bin/evaluation_tool.py count config/standard.config -l`

   The latter command may obviously take a long time to complete.

6. Build the table:

    `$ python3 bin/evaluation_tool.py table config/standard.config`

  The table may be displayed at any stage of the benchmark process;
  any missing entries will be displayed as `None`.

##### Comprehensive Scripts

* `./bin/run_benchmarks_short.sh` runs all short benchmarks (~ 1 to 2 hours).
* `./bin/run_benchmarks_long.sh` runs the longer benchmarks (over ~10 hours).
* `./bin/visualize_running_result.sh` visualizes from results which were just run (immediate).

##### Building Figure 5

`python3 bin/evaluation_tool.py figure config/prebuilt.config` generates
Figure 5 from the weakening expirement result. The resulting figure is
saved under the output directory.

##### Building From Saved Results

* `./bin/visualize_prebuilt_result.sh` visualizes from prebuilt result(immediate).


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


### Running Other Programs

To run Elrond on your own programs, you must provide both an input
OCaml code listing and an assertion file.

+ source file:

```c
(* Signature of library *)
module type DT_NAME = sig
  type TP_NAME
  ...
  val VAR: FUNC_TP
  ...
end

(* type of client *)
val VAR: FUNC_TP

(* implementation of client *)
let [rec] VAR (VAR: ARG_TP) ... = EXPR
```

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
+ The type in signature should be abstract.
+ The input type of function is a list of "ARG_TP", the output type of function are written as a tuple.
+ The condition of "if" should be a single function application.
+ The matched case in "match" are written as "| _ -> when CASE" instead of "| CASE"(we use ocaml parser which asks the matched case be an application of data type constrcutor, put the CASE after when can get round this limitation. In our situation the datatype is abstract and we do not distinguish if it is a constructor.)
+ New variable should be typed when it first appears(we do not do type inference).
+ All variables have distinct names(we do not do alpha renaming now).

+ assertion:

```c
(* Predicates *)
let preds = [| PRED; ...|]

(* Precondtion, which is optional *)
let pre VAR (IVAR: ARG_TP) ... (OVAR: ARG_TP) ... (QVAE: ARG_TP) ... = ASSERTION
(* Postcondtion *)
let post VAR (IVAR: ARG_TP) ... (OVAR: ARG_TP) ... (QVAE: ARG_TP) ... = ASSERTION
```

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

+ Impelementation of libraries and impelementation of predicates are fixed now, thus user cannot define their own libraries/predicaets. But user can define their own assertions.

## Proof of the result

+ The coq proof of our inferred specifications are saved in `proof` directory. run `make` to execute.
+ Each file with prefix `Verify` proves one inferred specification.
+ These files are generated by a command `dune exec -- main/main.exe coq <specificaion mapping file> <function name>` which can convert the inferred specification mappings to the coq lemmas for the furthur proving. For example, run `dune exec -- main/main.exe coq _data/_result/_customstk1/_oracle_maximal.json Customstk.push` can print several lemmas:

```
Lemma Customstk.push_1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_member  il_1 u_0)) -> (not (list_head  il_1 u_0))).
```

The `push_spec` is the pre-defined specification(defined and proved in `proof/.*Aux.v*`) of the `push`, `(((not (u_0 = i_0))/\(list_member  il_1 u_0)) -> (not (list_head  il_1 u_0)))` are one branch of the inferred decision tree. The all lemmas in the file are proved, the correctness of the inferred specification will be hold.

## Artifact Structure

This section gives a brief overview of the files in this artifact.

* `bin/`: scripts.
* `config/`: the config files for benchmark script.
* `data/`: the input data of banchmarks
  + `data/result.zip`: a saved inference result.
* `frontend/`: the parser of Elrond, modified from Ocmal parser.
* `inference/`: the specification mapping inference modules, includes both consistent inference and weakening inference.
* `language/`: the intermidate specification language of Elrond.
* `ml/`: the decistion tree learner.
* `main/main.ml`: the entry of Elrond.
* `pred/`: built-in implementation of predicates.
* `proof/`: the coq proof.
* `solver/`: the z3 solver wrapper.
* `tp/`: built-in types of Elrond.
* `translate/`: Vc generation.
  + `translate/imps.ml`: built-in implementation of libraries.
* `utils/`: utils functions.

### Configuration Files

* We use config file in json format to describe the source file, assertion file, output directory and details arguments for each benchmark. There are two config files:
  + `config/standard.config` for reviewers to run consistent inference and weakening inference by themselvies, the output directory of it is empty.
  + As the weakening inference may take several hours, we provides our consistent inference and weakening inference result under the output directory of `config/prebuilt.config` as some command takes serveral hours to run. Don't use this config file do inference which will corrupt the saved expirement result.
