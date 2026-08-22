# Lean seminar dev container
#
# Checked against: Lean 4.33.0 / Mathlib v4.33.0
#
# `--default-toolchain none` is deliberate. It installs elan with no default
# Lean, so elan falls through to the `lean-toolchain` file committed at the
# repository root and installs exactly that version. The pin therefore lives
# in one place: the file participants already have. Verified in the sandbox --
# `elan show` inside the project reports:
#     leanprover/lean4:v4.33.0 (overridden by '.../lean-toolchain')

FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain none

ENV PATH="/home/vscode/.elan/bin:${PATH}"
