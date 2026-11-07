module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Verified
public import VerifiedGarbage.TCB.X86.Print

/-! # DSA parameter generation over refillable tapes on i686, for every SHA-1, SHA-256 and Miller–Rabin backend -/

@[expose] public section
namespace VG.Generic.Sha1.Sha256.MillerRabin.X86.Dsa
open VG VG.X86 VG.Proof.Dsa.X86.Generation VG.Proof.MillerRabin.X86

/-- DSA's parameter search for a SHA-1 and a SHA-256 backend for the same
CPUs (both baselines or both SHA extensions), with each Miller–Rabin round:
either other pair needs the features of one of these, which runs both
hashes with them. -/
def artifacts (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    List Artifact :=
  if v1.suffix != v256.suffix then [] else
  let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
  [Spec.Dsa.parameterSearchApi.artifact target {
    suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
    code := Impl.Dsa.X86.Generation.code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)
    stack := 216
    verified := verified v1 v256 v
    spSafe := code_all v1 v256 v
    features := hashes ++ v.features.filter (!hashes.contains ·) }]

end VG.Generic.Sha1.Sha256.MillerRabin.X86.Dsa
