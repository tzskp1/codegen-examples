FROM ubuntu:20.04

RUN apt update \
  && apt install -y --no-install-recommends \
    ca-certificates \
    curl \
    m4 \
    nano \
    git \
    ocaml \
    opam \
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

VOLUME /workdir
COPY --chown=coq:coq . /workdir
WORKDIR /workdir/

RUN eval $(opam env) && make && make mt
CMD /workdir/mt
