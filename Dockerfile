FROM ocaml/opam:debian-ocaml-4.08
RUN sudo apt-get install -y libgmp-dev
RUN sudo apt-get install -y python
RUN opam init --auto-setup
RUN opam install dune.2.9.0
RUN opam install core.v0.14.0
RUN opam install yojson.1.7.0
RUN opam install ounit2.2.2.3
RUN opam install z3.4.7.1
RUN opam install qcheck.0.14
RUN sudo apt-get install -y python3
SHELL ["/bin/bash", "-lc"]
RUN git clone https://github.com/zhezhouzz/ADT-Lemma-Discovery.git
WORKDIR ADT-Lemma-Discovery
ARG CACHEBUST=1
RUN git pull
RUN git checkout artifact
ENV LD_LIBRARY_PATH=/home/opam/.opam/4.08/lib/z3
RUN bash ./init.sh
RUN dune build
RUN cp _build/default/main/main.exe main.exe