FROM coqorg/coq:8.16-ocaml-4.12-flambda

USER root
ENV DEBIAN_FRONTEND=noninteractive
ENV OPAMYES=true

# Install required packages
RUN apt-get update && apt-get install -y --no-install-recommends \
    git bubblewrap m4 unzip pkg-config libgmp-dev libev-dev \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /root

# Clone the zoo repo
RUN git clone https://github.com/clef-men/zoo
WORKDIR /root/zoo

# Initialize opam and set up local switch
RUN opam init --disable-sandboxing -y && \
    eval $(opam env) && \
    opam update --all --repositories && \
    opam switch create . --deps-only \
      --repos="default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git" --yes && \
    eval $(opam env --switch=. --set-switch) && \
    make -j4

CMD ["/bin/bash"]
