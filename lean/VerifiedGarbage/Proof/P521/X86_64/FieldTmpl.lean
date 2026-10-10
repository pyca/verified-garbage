import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-!
# P-521 on x86-64: the templates of the field operations

The erased code of P-521's field operations modulo `p` (`FieldTmpl`,
`Proof/Weierstrass/X86_64/FieldErase.lean`), with and without BMI2 and ADX,
as literals, proven to be the code of every slot's operation by the
kernel's evaluation of the code with the slots variables.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The templates modulo `p`. -/
def_literal p521T := FieldTmpl.ofMod p521.MP'

theorem p521_mul (o a b : Nat) :
    Impl.Mont.X86_64.mul p521.MP' o a b =
      if a = b then Impl.Mont.X86_64.sqrP p521.MP' o a else Impl.Mont.X86_64.mulP p521.MP' o a b := by
  unfold Impl.Mont.X86_64.mul
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p521_add (o a b : Nat) :
    Impl.Mont.X86_64.add p521.MP' o a b =
      if a = b then Impl.Mont.X86_64.dblMer o a else Impl.Mont.X86_64.addMer o a b := by
  unfold Impl.Mont.X86_64.add
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p521_sub (o a b : Nat) : Impl.Mont.X86_64.sub p521.MP' o a b = Impl.Mont.X86_64.subMer o a b := by
  unfold Impl.Mont.X86_64.sub
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p521_callOf : Mont.callOf p521.MP' = some (Spec.Weierstrass.Mont.p521p.mulApi.name, Mont.mulFn) := by
  unfold Mont.callOf
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p521T_ok : p521T.Ok p521.MP' where
  mul o a b h := by rw [p521_mul, ite_eq_right_of_eq_false _ _ (eq_false h)]; kernel_rfl
  sqr o a := by rw [p521_mul, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; kernel_rfl
  add o a b h := by rw [p521_add, ite_eq_right_of_eq_false _ _ (eq_false h)]; kernel_rfl
  dbl o a := by rw [p521_add, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; kernel_rfl
  sub o a b := by rw [p521_sub]; kernel_rfl
  call f body hf o a b := by
    rw [p521_callOf, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    kernel_rfl

/-- The templates modulo `p`, with BMI2 and ADX. -/
def_literal p521XT := FieldTmpl.ofMod p521x.MP'

theorem p521x_mul (o a b : Nat) :
    Impl.Mont.X86_64.mul p521x.MP' o a b =
      if a = b then Impl.Mont.X86_64.sqrPX p521x.MP' o a else Impl.Mont.X86_64.mulPX p521x.MP' o a b := by
  unfold Impl.Mont.X86_64.mul
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel),
    ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p521x_add (o a b : Nat) :
    Impl.Mont.X86_64.add p521x.MP' o a b =
      if a = b then Impl.Mont.X86_64.dblMer o a else Impl.Mont.X86_64.addMer o a b := by
  unfold Impl.Mont.X86_64.add
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p521x_sub (o a b : Nat) : Impl.Mont.X86_64.sub p521x.MP' o a b = Impl.Mont.X86_64.subMer o a b := by
  unfold Impl.Mont.X86_64.sub
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p521x_callOf :
    Mont.callOf p521x.MP' = some (Spec.Weierstrass.Mont.p521p.mulApi.name ++ "_adx", Mont.mulFnX) := by
  unfold Mont.callOf
  rw [ite_eq_left_of_eq_true _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p521XT_ok : p521XT.Ok p521x.MP' where
  mul o a b h := by rw [p521x_mul, ite_eq_right_of_eq_false _ _ (eq_false h)]; kernel_rfl
  sqr o a := by rw [p521x_mul, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; kernel_rfl
  add o a b h := by rw [p521x_add, ite_eq_right_of_eq_false _ _ (eq_false h)]; kernel_rfl
  dbl o a := by rw [p521x_add, ite_eq_left_of_eq_true _ _ (eq_true rfl)]; kernel_rfl
  sub o a b := by rw [p521x_sub]; kernel_rfl
  call f body hf o a b := by
    rw [p521x_callOf, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    kernel_rfl

/-- The template of a product modulo `n` (for any two slots: the code does
not tell a square apart). -/
def_literal p521NMul := KList.map Instr.erase (Impl.Mont.X86_64.mul p521.MN' 0 8 16)

theorem p521NMul_ok (o a b : Nat) : KList.map Instr.erase (Impl.Mont.X86_64.mul p521.MN' o a b) = p521NMul := by
  unfold Impl.Mont.X86_64.mul
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  kernel_rfl

/-- With BMI2 and ADX, the products modulo `n` are the same. -/
theorem p521XNMul_ok (o a b : Nat) :
    KList.map Instr.erase (Impl.Mont.X86_64.mul p521x.MN' o a b) = p521NMul := by
  unfold Impl.Mont.X86_64.mul
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel),
    ite_eq_left_of_eq_true _ _ (by decide +kernel)]
  kernel_rfl

/-- P-521 writes out no products (`Cfg.hot`): its `MH` is its `MP'`. -/
theorem p521_MH : p521.MH = p521.MP' := Impl.Mont.Mod.with_inl_false rfl
theorem p521x_MH : p521x.MH = p521x.MP' := Impl.Mont.Mod.with_inl_false rfl

theorem p521HT_ok : p521T.Ok p521.MH := p521_MH ▸ p521T_ok
theorem p521XHT_ok : p521XT.Ok p521x.MH := p521x_MH ▸ p521XT_ok

end VG.Proof.P521.X86_64
