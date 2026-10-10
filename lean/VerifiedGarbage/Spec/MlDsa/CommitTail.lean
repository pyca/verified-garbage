module

public import VerifiedGarbage.Spec.MlDsa.Poly

@[expose] public section

namespace VG.Spec.MlDsa

/-- A standard commitment hash and an independent next-attempt mask seed.
The two sponge streams are evaluated together without changing either result. -/
def commitTailSig (wlen olen : Nat) : Sig where
  params := [("mu",.array false .u8 64),("w1",.array false .u8 wlen),
    ("commitment",.array true .u8 olen),("scratch",.array true .u64 256),
    ("seed",.array false .u8 64),("nonce",.int .u64 false),("mask",.array true .u32 256)]

def commitTailSeed (m : Mem) (seed : Addr) (nonce : BitVec 64) : List Byte :=
  Spec.Sha3.bytesAt m seed 64 ++ [nonce.extractLsb' 0 8,nonce.extractLsb' 8 8]

def commitTailContract {M : ISA} (A : Abi M) (wlen olen : Nat) (stack : Nat := 0) : Contract M :=
  (commitTailSig wlen olen).contract A
    (post := fun mu w1 commitment _scratch seed nonce mask m m' _ =>
      Spec.Sha3.bytesAt m' commitment olen =
        H (Spec.Sha3.bytesAt m mu 64 ++ Spec.Sha3.bytesAt m w1 wlen) olen ∧
      PolyIs m' mask (toRq (bitUnpack (H (commitTailSeed m seed nonce) 640) 524287 524288)))
    (writeArgs := true) (stack := stack)

def commitTailApi (wlen olen : Nat) : Api where
  module := "mldsa"
  name := if wlen=768 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87"
  sig := commitTailSig wlen olen
  writeArgs := true
  contracts := some fun A stack => commitTailContract A wlen olen stack
  safety := []
  summary := "Computes the ML-DSA commitment and an independent mask polynomial using two SHAKE256 lanes."

end VG.Spec.MlDsa
