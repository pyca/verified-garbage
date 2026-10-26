module
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.RecoverProduct
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # The exact product of the private and public exponents -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev mTop (g : Geo) : Nat := 2 ^ (32 * g.W - 1)
def AW1 (e d : Nat) : Nat → Nat := upd (upd (fun _ => 0) wE e) wD d
def AWp (g : Geo) (e d : Nat) : Nat → Nat := upd (upd (AW1 e d) wMod (mTop g)) wM (d * e)

theorem product_core_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {e d eLen dLen : Nat}
    (h : KS g s0 A [aN] (upd (AW1 e d) wMod (mTop g))
      [wMod, wZ, wE, wD, wM, wMod] (fun _ => 0) [] s)
    (ePos : 0 < eLen) (eBound : eLen ≤ 8 * g.n) (dBound : dLen ≤ 8 * g.n)
    (eFits : e < 2 ^ (8 * eLen)) (dFits : d < 2 ^ (8 * dLen))
    (count : s.gpr .esi = BitVec.ofNat 32 (8 * eLen)) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.mulMod VG.Impl.Rsa.X86.RecoverRt.wid wZ wE wD wM wMod wT) s fun t =>
      KS g s0 A [aN] (AWp g e d) [wM, wMod, wZ] (fun _ => 0) [] t := by
  have upper := h.upper
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.mulMod_ok h.rtW (by decide) (by omega) (by omega) count)
    fun t ⟨_, k, r, value⟩ => ?_
  rw [kw_wid] at k value
  have gZ : num s.mem g.B g.W wZ = 0 := by
    rw [h.arrsW wZ (by simp)]; simp [AW1, upd, wZ, wMod, wD, wE]
  have gE : num s.mem g.B g.W wE = e := by
    rw [h.arrsW wE (by simp)]; simp [AW1, upd, wMod, wD, wE]
  have gD : num s.mem g.B g.W wD = d := by
    rw [h.arrsW wD (by simp)]; simp [AW1, upd, wMod, wD]
  have gA : num s.mem g.B g.W wM = 0 := by
    rw [h.arrsW wM (by simp)]; simp [AW1, upd, wM, wMod, wD, wE]
  have gM : num s.mem g.B g.W wMod = mTop g := by
    rw [h.arrsW wMod (by simp)]; simp [upd]
  have expBound : 8 * dLen + 8 * eLen ≤ 32 * g.W - 1 := by
    change 8 * dLen + 8 * eLen ≤ 32 * (2 * (2 * g.n + 2) + 2) - 1
    omega
  have dSmall : d < mTop g := Nat.lt_of_lt_of_le dFits
    (Nat.pow_le_pow_right (by decide) (by omega))
  have result := value gZ (by rw [gA, gM]; exact Nat.two_pow_pos _)
    (by rw [gD, gM]; exact dSmall) (by
      rw [gM, show 2 * mTop g = 2 ^ (32 * g.W - 1 + 1) by rw [Nat.pow_succ, Nat.mul_comm],
        show 32 * g.W - 1 + 1 = 32 * g.W by have := h.wsW.wpos; omega])
  rw [gA, gE, gD, gM, VG.Proof.Rsa.recover_product_exact dFits eFits expBound] at result
  have hd : ∀ d ∈ [sB, sC], SlotOk d := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl) <;> decide
  refine h.core k (fun j hj => h.wsW.arr_fit (by
      simp only [VG.Proof.Rsa.X86.KeyRt.mulArrs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hd (r.mono (by decide))
    (h.arrs_W k (by simp only [List.mem_singleton]; rintro j rfl; decide) hd) h.live_lt ?_ ?_
    (by simp) (by simp)
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [result]; simp [AWp, upd]
    · rw [k.num (by decide) (by decide) (h.wsW.fit64 (by decide)), gM]
      simp [AWp, upd, wM, wMod]
    · rw [k.num (by decide) (by decide) (h.wsW.fit64 (by decide)), gZ]
      simp [AWp, AW1, upd, wM, wMod, wZ, wE, wD]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro j (rfl | rfl | rfl) <;> decide

end VG.Proof.Rsa.X86.Recover
