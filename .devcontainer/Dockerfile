FROM mcr.microsoft.com/devcontainers/base:ubuntu

USER vscode
WORKDIR /home/vscode

# `elan` is Lean's toolchain manager (the analogue of `rustup`).
# `--default-toolchain none` installs no Lean version here: elan reads the
# project's `lean-toolchain` file and fetches the right one on first use, so
# this image does not go stale when the tutorial is bumped to a newer Lean.
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# elan-init appends this to ~/.profile, but devcontainer lifecycle commands do
# not necessarily run a login shell. Set it explicitly so `lake` is always found.
ENV PATH="/home/vscode/.elan/bin:${PATH}"
