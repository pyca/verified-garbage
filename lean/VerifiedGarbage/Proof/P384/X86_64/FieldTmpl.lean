import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-!
# P-384 on x86-64: the templates of the field operations

The erased code of P-384's field operations modulo `p` (`FieldTmpl`,
`Proof/Weierstrass/X86_64/FieldErase.lean`), with and without BMI2 and ADX,
as literals, proven to be the code of every slot's operation by the
kernel's evaluation of the code with the slots variables.
-/

namespace VG.Proof.P384.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- The templates modulo `p`. -/
def_literal p384T := FieldTmpl.ofMod p384.MP'

/-- The templates modulo `p`, with BMI2 and ADX. -/
def_literal p384XT := FieldTmpl.ofMod p384x.MP'

section
variable {M : Impl.Mont.Mod} (hn : M.n = 6) (hs : M.sparse = true) (hk : Impl.Mont.X86_64.prodK? M = none)
include hn hs hk

theorem mul_ne {o a b : Nat} (h : a ≠ b) :
    Impl.Mont.X86_64.mul M o a b =
      Impl.Mont.X86_64.mulRounds M a b ++
        Impl.Mont.X86_64.csub M ((List.range M.n).map (Impl.Mont.X86_64.win M.n M.n))
          (Impl.Mont.X86_64.win M.n M.n M.n) ++
        Impl.Mont.X86_64.stores ((List.range M.n).map (Impl.Mont.X86_64.win M.n M.n)) o := by
  simp only [Impl.Mont.X86_64.mul, Impl.Mont.X86_64.mulR, Impl.Mont.X86_64.mulG, hn, hs, hk, h]
  rfl

theorem mul_eq (o a : Nat) : Impl.Mont.X86_64.mul M o a a = Impl.Mont.X86_64.sqrS M o a := by
  simp only [Impl.Mont.X86_64.mul, Impl.Mont.X86_64.mulR, hn, hs, hk]
  rfl

end

theorem add_eq {M : Impl.Mont.Mod} (hn : M.n = 6) (o a b : Nat) :
    Impl.Mont.X86_64.add M o a b = Impl.Mont.X86_64.addR M o a b := by
  simp only [Impl.Mont.X86_64.add, hn, show 6 < 7 from by decide, ite_true]

theorem sub_eq {M : Impl.Mont.Mod} (hn : M.n = 6) (hs : M.sparse = true)
    (hr : (M.adx = true ∧ M.red = .friendly Impl.Mont.X86_64.p256Ws) = False) (o a b : Nat) :
    Impl.Mont.X86_64.sub M o a b = Impl.Mont.X86_64.sub384 o a b := by
  unfold Impl.Mont.X86_64.sub
  rw [ite_eq_right_of_eq_false _ _ hr]
  simp only [hn, hs, and_self, ite_true]

theorem p384_callOf :
    Mont.callOf p384.MP' = some (Spec.Weierstrass.Mont.p384p.mulApi.name, Mont.mulFn6 false) := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel),
    ite_eq_right_of_eq_false _ _ (by decide +kernel)]

theorem p384x_callOf :
    Mont.callOf p384x.MP' = some (Spec.Weierstrass.Mont.p384p.mulApi.name ++ "_adx", Mont.mulFn6 true) := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_left_of_eq_true _ _ (by decide +kernel),
    ite_eq_left_of_eq_true _ _ (by decide +kernel)]

theorem p384T_ok : p384T.Ok p384.MP' where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf o a b := by
    rw [p384_callOf, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    kernel_rfl

theorem p384XT_ok : p384XT.Ok p384x.MP' where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf o a b := by
    rw [p384x_callOf, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    kernel_rfl

/-- With its products written out (`Mod.inl`), `p384`'s modulus calls none. -/
theorem p384h_callOf : Mont.callOf { p384.MP' with inl := true } = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel)]

/-- The templates modulo `p`, for the products written out. -/
theorem p384HT_ok : p384T.Ok { p384.MP' with inl := true } where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf o a b := by rw [p384h_callOf] at hf; cases hf

/-- With its products written out (`Mod.inl`), `p384x`'s modulus calls none. -/
theorem p384xh_callOf : Mont.callOf { p384x.MP' with inl := true } = none := by
  unfold Mont.callOf
  rw [ite_eq_right_of_eq_false _ _ (by decide +kernel), ite_eq_right_of_eq_false _ _ (by decide +kernel)]

/-- The templates modulo `p` with BMI2 and ADX, for the products written out. -/
theorem p384XHT_ok : p384XT.Ok { p384x.MP' with inl := true } where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf o a b := by rw [p384xh_callOf] at hf; cases hf

end VG.Proof.P384.X86_64
