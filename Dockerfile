FROM coqorg/coq:8.20.1-ocaml-4.14.2-flambda

USER root
ENV DEBIAN_FRONTEND=noninteractive
ENV OPAMYES=true

# Install required packages
RUN apt-get update && apt-get install --yes --no-install-recommends \
    git bubblewrap m4 unzip pkg-config libgmp-dev libev-dev \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /root

# Clone the zoo repo
RUN git clone https://github.com/clef-men/zoo
WORKDIR /root/zoo

# Copy build script into image
COPY make_package.sh /usr/local/bin/build-package
RUN chmod +x /usr/local/bin/build-package

# Initialize opam and set up local switch
RUN opam init --disable-sandboxing --yes && \
    eval $(opam env) && \
    opam switch create . --deps-only \
      --repos="default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git" --yes


# Default command (can be overridden at runtime)
CMD ["/usr/local/bin/build-package", "zoo"]
