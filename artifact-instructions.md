# Artifact Guide: Data-Driven Abductive Inference of Library Specifications

This document describes installation and use of Elrond, an OCaml tool
for data-driven abduction of black-box library method specifications.
This is the accompanying artifact for the OOPSLA 2021 submission
*Data-Driven Abductive Inference of Library Specifications* by Zhou et
al.


## TODO

* Test these instructions in OSX and Windows.

* Should we publish a Docker image instead of asking evaluators to
  build the Dockerfile directly?

* Where in the artifact layout is the Dockerfile? Root?

* A "Hello World" Elrond invocation to make sure the Docker image is
  up and running successfully.

* How to actually run benchmarks? The README instructions are likely
  outdated, and it's not obvious to me how to do it.

* A script to run all benchmarks from the paper at once.

* Is verification via Dafny still supported, or should we omit that
  section?

* Annotate the artifact structure.


## Requirements

* Docker, which may be installed according to [the official
  installation instructions](https://docs.docker.com/get-docker/).
  This guide was tested using Docker version 20.10.7, but any
  contemporary Docker version is expected to work.


## Getting Started

1. Ensure Docker is installed. (On *nix, `sudo docker run hello-world`
will test your installation.) If Docker is not installed, install it
via the [official installation guide](https://docs.docker.com/get-docker/).

2. Navigate to the location of the Elrond Docker file in this artifact.

   ```# cd <Dockerfile dir>```

3. Build the Elrond Docker image.

    ```# docker build . --tag elrond```

4. Launch a shell in the Elrond Docker image.

    ```# docker run -it elrond```

5. Verify Elrond is running successfully.

    **TODO: Need a "hello world" Elrond invocation here.**

6. When you are finished, you may stop the Elrond image by terminating
the shell with `exit`.


## Running Benchmarks

To run benchmark `$bench`, run `dune exec bench/$bench.exe`. For example,

```dune exec bench/customstack.exe```

will run all Custom Stack benchmarks.

**TODO: I pulled the above from the project's README, but I can't
actually figure out how to execute benchmarks.**

**TODO: A script that runs all benchmarks from the paper?**

### Verifying Inferred Lemmas (TODO: Is this still supported?)

Optionally, the inferred lemmas may be verified via
[Dafny](https://github.com/dafny-lang/dafny). To verify a benchmark
named `$bench`, run `dafny lemma_verifier/$bench.dfy` after running
Elrond. For example,

```dafny lemma_verifier/custstk.dfy```

verifies the abduced specifications for the `custstk` benchmark.


## Artifact Structure

TODO: Annotate the basic layout of the artifact code.
