module
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Run

/-! Precise byte and memory framing for the shared native output-clearing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.WriteBytes (writeW8_apply)

structure OutputZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.x11, .x12] s t
  r10 : t.gpr .x11 = out + BitVec.ofNat 64 j
  r11 : t.gpr .x12 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem zeroOut_bytes_ok {s : State} {F S op : Addr} {k : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hO : W 19 = op) (hK : W 21 = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.x11, .x12, .x13] s t := by
  have ho : s.mem.readW (F + BitVec.ofNat 64 sOut) 64 = op := (R.fr 19 (by decide)).trans hO
  have hk : s.mem.readW (F + BitVec.ofNat 64 sK) 64 = BitVec.ofNat 64 k := (R.fr 21 (by decide)).trans hK
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x11, .x12, .x13] (Q := fun t => t.gpr .x11 = op ∧
      t.gpr .x12 = BitVec.ofNat 64 k ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (off := sOut) (by decide), exec_ldrSp (off := sK) (by decide), L.sp,
      L.ld (d := sOut) (n := 8) (by decide), L.ld (d := sK) (n := 8) (by decide), ho, hk]) rfl rfl rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.RsaOaep.AArch64.count_loop (cr := .x12) hk1 (OutputZeroInv s₁ op k) ?_
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j hj t hI
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.wr, k₁.wr]; exact hout j hj
  have hax' : (t.gpr .x13).setWidth 8 = 0 := by rw [hI.keep.gpr .x13 (by decide), hax]; rfl
  have hp : BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x11, .x12] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .x11 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .x12 = BitVec.ofNat 64 (k - (j + 1)))
      (by brun [hI.r10, hI.r11, hst, hax', hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl)
      rfl rfl rfl) fun t' ⟨⟨hm, hsi', hcx'⟩, k'⟩ => ?_
  refine ⟨⟨(hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)
  · rw [hcx']
    exact VG.Proof.RsaOaep.AArch64.counter_ne (by omega) hk'

end VG.Proof.Dsa.AArch64.Generation
