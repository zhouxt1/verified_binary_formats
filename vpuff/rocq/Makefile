# Rocq 9.3 + VST 2.17 + CompCert 3.18 (32-bit) + rocq-lean-import; run via ./build.sh
CC := /home/rocq/cc
ROCQ := rocq c $(shell cat _CoqProject)

VFILES := LeanSpec.v LeanNat.v Model.v Bridge.v Inflate.v InflateFacts.v InflateEq.v \
  puff.v Spec_puff.v Main.v DecodeLemmas.v Verif_decode.v ConstructLemmas.v Verif_construct.v \
  P2_Bits.v P2_Stored.v Verif_bits.v Verif_stored.v \
  Codes_Dist30.v CodesLemmas.v Verif_codes.v Verif_fixed.v DynLemmas.v Verif_dynamic.v \
  PuffLemmas.v Verif_puff.v Puff.v
all: $(VFILES:.v=.vo)

# puff.c (../c, altered from zlib's contrib/puff) as Clight
puff.v: ../c/puff.c ../c/puff.h
	cp ../c/puff.c ../c/puff.h . && $(CC)/bin/clightgen -normalize puff.c && rm -f puff.c puff.h

%.vo: %.v
	$(ROCQ) $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
.PHONY: all clean
