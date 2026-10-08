# The Rocq toolchain for vpuff/rocq: Rocq 9.3, rocq-lean-import, CompCert 3.18
# (32-bit, clightgen) and VST 2.17. Build from vpuff/:
#   docker build -t vst-rli:9.3 docker
# VST 2.17 and CompCert 3.18 declare Rocq <= 9.2 and rocq-lean-import's NDJSON
# reader needs Rocq >= 9.3, so the version checks are switched off; both build
# with warnings only.
FROM rocq/rocq-prover:9.3

# rocq-lean-import at the first commit that reads lean4export's NDJSON, plus a
# shim for one Rocq API change (Summary.Ref) made after 9.3
RUN opam install -y yojson menhir.20240715
COPY rocq-lean-import-9.3.patch /tmp/
RUN git clone -q https://github.com/rocq-community/rocq-lean-import /home/rocq/rli \
 && cd /home/rocq/rli && git -c core.hooksPath=/dev/null checkout -q 546979b \
 && git apply /tmp/rocq-lean-import-9.3.patch \
 && eval $(opam env) && make -j8

# CompCert 3.18, 32-bit x86, with its Rocq development and clightgen
RUN git clone -q --depth 1 -b v3.18 https://github.com/AbsInt/CompCert.git /home/rocq/compcert \
 && cd /home/rocq/compcert && eval $(opam env) \
 && ./configure -ignore-coq-version -clightgen -install-coqdev -prefix /home/rocq/cc \
      -coqdevdir /home/rocq/cc/coq x86_32-linux \
 && make -j32 && make install

# VST 2.17 against that CompCert. VST's makefile calls coqc/coqdep, which
# Rocq 9.3 calls rocq c/rocq dep; it also wants Flocq and MenhirLib installed,
# which CompCert bundles.
RUN mkdir -p /home/rocq/bin \
 && printf '#!/bin/sh\nexec rocq c "$@"\n' > /home/rocq/bin/coqc \
 && printf '#!/bin/sh\nexec rocq dep "$@"\n' > /home/rocq/bin/coqdep \
 && printf '#!/bin/sh\nexec rocq top "$@"\n' > /home/rocq/bin/coqtop \
 && chmod +x /home/rocq/bin/coqc /home/rocq/bin/coqdep /home/rocq/bin/coqtop \
 && eval $(opam env) && W=$(coqc -where)/user-contrib && mkdir -p $W \
 && ln -sfn /home/rocq/cc/coq/flocq $W/Flocq && ln -sfn /home/rocq/cc/coq/MenhirLib $W/MenhirLib
ENV PATH=/home/rocq/bin:$PATH
RUN git clone -q --depth 1 -b v2.17 https://github.com/PrincetonUniversity/VST.git /home/rocq/vst \
 && cd /home/rocq/vst && eval $(opam env) \
 && F="IGNORECOQVERSION=true IGNORECOMPCERTVERSION=true COMPCERT=inst_dir COMPCERT_INST_DIR=/home/rocq/cc/coq BITSIZE=32 ZLIST=bundled" \
 && make $F depend && make -j32 $F CLIGHTGEN=/home/rocq/cc/bin/clightgen vst
