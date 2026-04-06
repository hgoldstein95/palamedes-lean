FROM python:3.10

## BEGIN: RUNS AS ROOT

SHELL ["/bin/bash", "-c"]

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
RUN apt-get install -y vim
RUN apt-get install -y nano
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y pkg-config

USER $USERNAME

# Configure opam/ocaml
# Install Cobb dependencies

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

# Install QuickChick
RUN opam pin add -y coq 8.20.0
RUN opam repo add -y rocq-released https://rocq-prover.org/opam/released
RUN opam install -y coq-quickchick

WORKDIR /home/artifact/Cobb
COPY --chown=$USERNAME:$USERNAME Cobb/ .
RUN eval $(opam env)
RUN opam exec -- dune build

WORKDIR /home/artifact
COPY --chown=$USERNAME:$USERNAME README.md .
COPY --chown=$USERNAME:$USERNAME run_palamedes.sh .
COPY --chown=$USERNAME:$USERNAME run_cobb.sh .
COPY --chown=$USERNAME:$USERNAME run_cobb_oob.sh .
COPY --chown=$USERNAME:$USERNAME cobb_ktt.sh .
COPY --chown=$USERNAME:$USERNAME ktt.sh .


COPY --chown=$USERNAME:$USERNAME QC/ QC/

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
ENV PATH="$PATH:/home/artifact/.elan/bin"

COPY --chown=$USERNAME:$USERNAME Palamedes/ Palamedes/
WORKDIR /home/artifact/Palamedes/
RUN lake update
RUN lake clean
RUN lake exe cache get
RUN lake build
RUN pip install tqdm

WORKDIR /home/artifact