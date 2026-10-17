module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
public import VerifiedGarbage.Impl.P224.X86_64.Joint
meta import VerifiedGarbage.Impl.P224.X86_64.Joint

/-!
# P-224 on x86-64: the templates of the field operations

The erased code of P-224's field operations modulo `p` in the joint
verifier's window (`FieldTmpl`, `Proof/Weierstrass/X86_64/FieldErase.lean`),
as a literal, proven to be the code of every slot's operation by the
kernel's evaluation of the code with the slots variables.
-/

@[expose] public section

namespace VG.Proof.P224.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The templates modulo `p`. -/
def_literal p224T := FieldTmpl.ofMod p224v.MH

theorem p224_callOf : Mont.callOf p224v.MH = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p224T_ok : p224T.Ok p224v.MH where
  mul _ _ _ _ := by kernel_rfl
  sqr _ _ := by kernel_rfl
  add _ _ _ _ := by kernel_rfl
  dbl _ _ := by kernel_rfl
  sub _ _ _ := by kernel_rfl
  call f body hf _ _ _ := by rw [p224_callOf] at hf; cases hf

/-- The erased double of `ForwardField.programB` (`double4`). -/
def_literal p224D := KList.map Instr.erase (Impl.Mont.X86_64.double4 p224v.MH 0 8)

theorem p224D_ok (o a : Nat) : KList.map Instr.erase (Impl.Mont.X86_64.double4 p224v.MH o a) = p224D := by
  kernel_rfl

end VG.Proof.P224.X86_64
