module

public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA: the contract of high bits, packed

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Fixed-parameter fused HighBits and SimpleBitPack helper, with the same
output encoding as the separate standard operations. -/
def highPackSig (gamma2 : Nat) : Sig where
  params := [("r", .array false .u32 256),
    ("out", .array true .u8 (32*bitlen ((q-1)/(2*gamma2)-1)))]

/-- Fused helper contract. Input coefficients are canonical; output
bytes are the original HighBits followed by SimpleBitPack, with no leakage
of coefficient values. The parameter is fixed when the helper is generated. -/
def highPackContract (gamma2 : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (highPackSig gamma2).contract A
    (pre := fun r _out m => Reduced m r)
    (post := fun r out m m' _ =>
      Spec.Sha3.bytesAt m' out (32*bitlen ((q-1)/(2*gamma2)-1)) =
        simpleBitPack ((polyAt m r).map fun c => (highBits gamma2 c).toNat) ((q-1)/(2*gamma2)-1))
    (writeArgs := true)
    (stack := stack)

end VG.Proof.MlDsa
