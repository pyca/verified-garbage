module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64

/-!
# P-256 on x86-64: the templates of the field operations

The erased code of P-256's field operations modulo `p` in the window
(`FieldTmpl`, `Proof/Weierstrass/X86_64/FieldErase.lean`), with and without
BMI2 and ADX, as literals, proven to be the code of every slot's operation
by the kernel's evaluation of the code with the slots variables.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The templates modulo `p`. -/
def_literal p256T := FieldTmpl.ofMod p256.MH

/-- The templates modulo `p`, with BMI2 and ADX. -/
def_literal p256XT := FieldTmpl.ofMod p256x.MH

theorem p256_callOf : Mont.callOf p256.MH = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p256x_callOf : Mont.callOf p256x.MH = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p256T_ok : p256T.Ok p256.MH where
  mul _ _ _ _ := by kernel_rfl
  sqr _ _ := by kernel_rfl
  add _ _ _ _ := by kernel_rfl
  dbl _ _ := by kernel_rfl
  sub _ _ _ := by kernel_rfl
  call f body hf _ _ _ := by rw [p256_callOf] at hf; cases hf

theorem p256x_mul (o a b : Nat) :
    Impl.Mont.X86_64.mul p256x.MH o a b =
      if a = b then Impl.Mont.X86_64.sqrRX p256x.MH 32 o a else Impl.Mont.X86_64.mulRX p256x.MH 32 o a b := by
  unfold Impl.Mont.X86_64.mul Impl.Mont.X86_64.mulR
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel), show Impl.Mont.X86_64.prodK? p256x.MH = some 32 by decide +kernel]

theorem p256XT_ok : p256XT.Ok p256x.MH where
  mul o a b h := by rw [p256x_mul, ite_eq_right_of_eq_false _ _ (eq_false h)]; kernel_rfl
  sqr o a := by rw [p256x_mul, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; kernel_rfl
  add _ _ _ _ := by kernel_rfl
  dbl _ _ := by kernel_rfl
  sub _ _ _ := by kernel_rfl
  call f body hf _ _ _ := by rw [p256x_callOf] at hf; cases hf

/-- The erased double of `ForwardField.programB` (`double4`). -/
def_literal p256D := KList.map Instr.erase (Impl.Mont.X86_64.double4 p256.MH 0 8)

theorem p256D_ok (o a : Nat) : KList.map Instr.erase (Impl.Mont.X86_64.double4 p256.MH o a) = p256D := by
  kernel_rfl

end VG.Proof.P256.X86_64
