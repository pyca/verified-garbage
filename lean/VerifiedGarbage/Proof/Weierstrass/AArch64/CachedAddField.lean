module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedField
public import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64

def inputs : List Nat := rcbR K.S K.R K.E ++ [5400,5432]
def ops : CachedJac.Ops where
  head := VG.Impl.P256.VerifyArithmetic.program K.M head
  tail := VG.Impl.P256.VerifyArithmetic.program K.M tail
  double := VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D

theorem out_tail : ∀ x∈[K.D.x,K.D.y,K.D.z],x∈tail.map FOp.out := by decide +kernel
theorem reads_head : readsOk head inputs=true := by decide +kernel
theorem reads_full : readsOk (head++tail) inputs=true := by decide +kernel

theorem head_readonly {F : Type} [Lean.Grind.CommRing F] (E : Nat → F)
    {x : Nat} (hx : x∈inputs) : runOps head E x=E x := by
  apply runOps_of_not_out
  have h : ∀ op∈head,∀ x∈inputs,op.out≠x := by decide +kernel
  exact fun op hop => h op hop x hx

end VG.Proof.Weierstrass.AArch64.CachedField
