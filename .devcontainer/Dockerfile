FROM python:3.10

## BEGIN: RUNS AS ROOT

# Create a user

ARG USERNAME=artifact
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN apt-get update -y

RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME --shell /bin/zsh \
    #
    # [Optional] Add sudo support. Omit if you don't need to install software after connecting.
    && apt-get install -y sudo \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

RUN apt-get install -y build-essential
RUN apt-get install -y linux-libc-dev
RUN apt-get install -y m4
RUN apt-get install -y opam
RUN apt-get install -y time
RUN apt-get install -y zip
RUN apt-get install -y zsh
RUN apt-get install -y libgmp3-dev
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y pkg-config

USER $USERNAME

# Configure opam/ocaml
# Install Cobb dependencies
WORKDIR /home/artifact/Cobb
RUN opam init -y --disable-sandboxing --compiler=5.3.0
RUN opam install -y num
RUN opam install -y dune
RUN opam install -y ppx_jane
RUN opam install -y pomap
RUN opam install -y core_unix
RUN opam install -y core_kernel
RUN opam install -y async
RUN opam install -y z3
RUN opam install -y ocolor
RUN opam install -y yojson
RUN opam install -y dolog
RUN opam update -y
RUN opam upgrade -y

COPY --chown=$USERNAME:$USERNAME Cobb/ .
RUN eval $(opam env)
RUN opam exec -- dune build

WORKDIR /home/artifact
COPY --chown=$USERNAME:$USERNAME experiments.sh .
