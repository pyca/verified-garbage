module

public import VerifiedGarbage.Spec.MlDsa.ResponseZ

@[expose] public section

namespace VG.Spec.MlDsa

/-- Reconstruct the field coefficient represented by its signed low part and high part. -/
def responseHintBase (m : Mem) (low high : Addr) (g i : Nat) : Zq :=
  ofInt ((coeffAt m low i).toInt+2*(g:Int)*(coeffAt m high i).toNat)

/-- Inputs are an exact decomposition, including the special high-zero boundary. -/
def ResponseDecomposed (m : Mem) (low high : Addr) (g : Nat) : Prop :=
  ∀i<n,(coeffAt m low i).toInt=lowBits g (responseHintBase m low high g i) ∧
    (coeffAt m high i).toNat=(highBits g (responseHintBase m low high g i)).toNat

def responseHintPoly (m : Mem) (low ct high : Addr) (g : Nat) : Vector Bool n :=
  Vector.ofFn fun i =>
    let c := ofInt (coeffAt m ct i.val).toInt
    makeHint g (-c) (responseHintBase m low high g i.val+c)

def hintNormSig : Sig where
  params := [("low",.array true .u32 256),("ct0",.array false .u32 256),
    ("high",.array false .u32 256),("gamma2",.int .u32 true)]
  ret := some .u64

/-- Replace the low parts by hints and return their count in the low 32 bits.
The high 32 bits are one exactly when the challenge product passes the strict
norm check. Both outputs remain exact on rejection. -/
def hintNormContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  hintNormSig.contract A
    (pre := fun low ct high gamma2 m => gamma2.toNat∈gamma2s ∧
      RawReduced m ct ∧ ResponseDecomposed m low high gamma2.toNat)
    (post := fun low ct high gamma2 m m' r =>
      HintIs m' low 1 [responseHintPoly m low ct high gamma2.toNat] ∧
      r=BitVec.ofNat 64 (hintOnes [responseHintPoly m low ct high gamma2.toNat]+
        if normRq [signedPolyAt m ct]<gamma2.toNat then 4294967296 else 0))
    (writeArgs := true) (stack := stack)

def hintNormApi : Api where
  module := "mldsa"
  name := "vg_mldsa_signed_hint_norm"
  sig := hintNormSig
  writeArgs := true
  contracts := some fun A stack => hintNormContract A stack
  summary := "Creates hints from decomposed signed low and high parts and a signed challenge product, returning hint count and strict norm validity."
  safety := ["Gamma2 must be 95232 or 261888; the low/high inputs must be an exact decomposition for that Gamma2.",
    "Challenge-product coefficients must be signed integers strictly between -8380417 and 16760834."]

end VG.Spec.MlDsa
