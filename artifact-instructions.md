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

* Command to get _time<sub>w</sub>_ and _time<sub>d</sub>_ values from
  Table 4.

* There are other columns in Table 4; does our benchmark script give
  us all of these numbers?

* Improve output of the benchmark script; currently difficult to
  correlate the script's output to our evaluation figure (Table 4).

* Document the input file formats.


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

   ```# cd <Dockerfile dir>```

3. Build the Elrond Docker image.

    ```# docker build . --tag elrond```

4. Launch a shell in the Elrond Docker image.

    ```# docker run -it elrond```

5. Print the Elrond's help message to verify the tool was installed
   successfully.

    ```$ ./main.exe --help```

6. When you are finished, you may stop the Elrond image by terminating
the shell with `exit`.


## Using Elrond

### Running All Benchmarks

Experimental results on the benchmark suite displayed in Table 4 of
the paper can be obtained via the
`~/ADT-Lemma-Discovery/run_benchmarks.sh` script in the Docker image
as follows:

* `./run_benchmarks.sh consistent` finds consistent specification
  mappings which enable successful verifications, but does not find
  weakenings of these specifications. This corresponds to the
  _time<sub>c</sub>_ column in Table 4.

* **TODO: Command** finds weakened specifications, corresponding to
  the _time<sub>w</sub>_ and _time<sub>d</sub>_ columns in Table 4.

* **TODO: There are other columns in Table 4; can our benchmark script
  give us these numbers too?**


### Running Individual Benchmarks

Elrond requires both a source file and assertion file as input, and
outputs results in JSON format to some output directory. The input
source and assertion files for the benchmark suite are located in the
`~/ADT-Lemma-Discovery/data` directory in the Docker image.

The command to run an individual benchmark without weakening is:

```./main.exe infer consistent <source_file> <assertion_file> <output_dir>```

For example,

```$ ./main.exe infer consistent data/bankersq.ml data/bankersq_assertion1.ml bankersq_out```

will run the `bankersq` benchmark, writing results to the
`_bankersq_out` directory. **TODO: A little confusing to prepend `_`
to the output dir here?**

To find weakened specification mappings, first run the benchmark without
weakening as above, then say:

```./main.exe infer weakening <output_dir>```

on the same `<output_dir>`.

For example,

```$ ./main.exe infer weakening bankersq_out```

will perform weakening on the `bankersq` benchmark we executed above.

Alternately, you may run the full inference-with-weakening pipeline
at once by saying:

```$ ./main.exe infer full <source_file> <assertion_file> <output_dir>```

For example, we can recreate the `bankersq` output directory in one pass:

    $ rm -rf _bankersq_out
    $ ./main.exe infer full data/bankersq.ml data/bankersq_assertion1.ml bankersq_out


### Running Other Programs

To run Elrond on your own programs, you must provide both an input
OCaml code listing and an assertion file.

**TODO: Document the requirements on these inputs.**


## Artifact Structure

This section gives a brief overview of the files in this artifact.

TODO: Annotate the basic layout of the artifact code.
