module

public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ML-DSA: the contract of two `ExpandMask` polynomials at once

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Two independent 66-byte ExpandMask seeds and separately addressed outputs. -/
def expandMaskPairSig : Sig where
  params := [("seeds", .array false .u8 132), ("gamma1", .int .u32 true),
    ("a", .array true .u32 256), ("b", .array true .u32 256),
    ("scratch", .array true .u64 1024)]

/-- Each output is exactly one standard ExpandMask polynomial. Pairing the
SHAKE streams changes neither their seeds nor their coefficient encodings. -/
def expandMaskPairContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandMaskPairSig.contract A
    (pre := fun _seeds gamma1 _a _b _scratch _m => gamma1.toNat=2^17 ∨ gamma1.toNat=2^19)
    (post := fun seeds gamma1 a b _scratch m m' _ =>
      let c := 1+bitlen (gamma1.toNat-1)
      PolyIs m' a (toRq (bitUnpack (H (Spec.Sha3.bytesAt m seeds 66) (32*c))
        (gamma1.toNat-1) gamma1.toNat)) ∧
      PolyIs m' b (toRq (bitUnpack (H (Spec.Sha3.bytesAt m (seeds+66) 66) (32*c))
        (gamma1.toNat-1) gamma1.toNat)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa
