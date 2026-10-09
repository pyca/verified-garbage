import VerifiedGarbage.Spec.MlDsa.Poly

namespace VG.Spec.MlDsa

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

/-- Internal paired sampler exposed through the normal checked artifact path. -/
def expandMaskPairApi : Api where
  module := "mldsa"
  name := "vg_mldsa_expand_mask_pair"
  sig := expandMaskPairSig
  writeArgs := true
  contracts := some fun A stack => expandMaskPairContract A stack
  summary := "Expands two independent 66-byte seeds into two canonical ML-DSA mask polynomials." ++
    " Timing depends only on the pointers and gamma1."
  safety := ["gamma1 must be 131072 or 524288."]

end VG.Spec.MlDsa
