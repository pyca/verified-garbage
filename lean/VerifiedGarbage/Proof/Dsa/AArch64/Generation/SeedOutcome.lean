module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context

/-! # A native seed attempt returns either exhaustion, retry, or packed parameters -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.Generation.Layout

def SeedOutcome (p : GenerationContext) (res : Option (Option Spec.Dsa.Params × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = 0 ∧ res = none) ∨
  (W 19 = 3 ∧ res = some (none, p.rand.bytes.drop used)) ∨
  (W 19 = 1 ∧ ∃ a, res = some (some a, p.rand.bytes.drop used) ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
      Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)

end VG.Proof.Dsa.AArch64.Generation
