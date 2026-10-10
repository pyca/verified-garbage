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
variable {c : Cfg} (hn : c.MP'.n = 6) (hs : c.MP'.sparse = true) (hk : Impl.Mont.X86_64.prodK? c.MP' = none)
include hn hs hk

theorem mul_ne {o a b : Nat} (h : a ≠ b) :
    Impl.Mont.X86_64.mul c.MP' o a b =
      Impl.Mont.X86_64.mulRounds c.MP' a b ++
        Impl.Mont.X86_64.csub c.MP' ((List.range c.MP'.n).map (Impl.Mont.X86_64.win c.MP'.n c.MP'.n))
          (Impl.Mont.X86_64.win c.MP'.n c.MP'.n c.MP'.n) ++
        Impl.Mont.X86_64.stores ((List.range c.MP'.n).map (Impl.Mont.X86_64.win c.MP'.n c.MP'.n)) o := by
  simp only [Impl.Mont.X86_64.mul, Impl.Mont.X86_64.mulR, Impl.Mont.X86_64.mulG, hn, hs, hk, h]
  rfl

theorem mul_eq (o a : Nat) : Impl.Mont.X86_64.mul c.MP' o a a = Impl.Mont.X86_64.sqrS c.MP' o a := by
  simp only [Impl.Mont.X86_64.mul, Impl.Mont.X86_64.mulR, hn, hs, hk]
  rfl

end

theorem add_eq {c : Cfg} (hn : c.MP'.n = 6) (o a b : Nat) :
    Impl.Mont.X86_64.add c.MP' o a b = Impl.Mont.X86_64.addR c.MP' o a b := by
  simp only [Impl.Mont.X86_64.add, hn, show 6 < 7 from by decide, ite_true]

theorem sub_eq {c : Cfg} (hn : c.MP'.n = 6) (hs : c.MP'.sparse = true)
    (hr : (c.MP'.adx = true ∧ c.MP'.red = .friendly Impl.Mont.X86_64.p256Ws) = False) (o a b : Nat) :
    Impl.Mont.X86_64.sub c.MP' o a b = Impl.Mont.X86_64.sub384 o a b := by
  unfold Impl.Mont.X86_64.sub
  rw [ite_eq_right_of_eq_false _ _ hr]
  simp only [hn, hs, and_self, ite_true]

theorem p384T_ok : p384T.Ok p384.MP' where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf := by cases (hf.symm.trans (by decide +kernel) : some (f, body) = none)

theorem p384XT_ok : p384XT.Ok p384x.MP' where
  mul o a b h := by rw [mul_ne (by decide +kernel) (by decide +kernel) (by decide +kernel) h]; kernel_rfl
  sqr o a := by rw [mul_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  add o a b _ := by rw [add_eq (by decide +kernel)]; kernel_rfl
  dbl o a := by rw [add_eq (by decide +kernel)]; kernel_rfl
  sub o a b := by rw [sub_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]; kernel_rfl
  call f body hf := by cases (hf.symm.trans (by decide +kernel) : some (f, body) = none)

end VG.Proof.P384.X86_64
