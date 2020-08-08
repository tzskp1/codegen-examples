FROM ubuntu:20.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    m4 \
    nano \
    git \
    ocaml \
    opam \
    emacs-nox \
  && apt-get clean \
  && rm -rf /var/lib/apt/lists/*
RUN groupadd coq \
    && useradd coq -g coq -m
USER coq
RUN opam init --disable-sandboxing --comp 4.09.0 --reinit -n
RUN eval $(opam env) \
    && opam repo add coq-released https://coq.inria.fr/opam/released \
    && opam pin add -y coq 8.11.1 \
    && opam install -y coq-mathcomp-algebra coq-coqprime coq-mathcomp-field

WORKDIR /tmp
RUN eval $(opam env) \
    && git clone https://github.com/akr/codegen \
    && cd codegen \
    && git checkout 2a7ebe6b26233b0947e6e93e2940f4598e737e1a \
    && make && make install

COPY --chown=coq:coq . /workdir
WORKDIR /workdir/

RUN eval $(opam env) && make clean && make && make mt
RUN mkdir ~/.emacs.d && mv init.el ~/.emacs.d/ && emacs --script ~/.emacs.d/init.el
CMD eval $(opam env) && emacs
