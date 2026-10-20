module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_generate_key` on AArch64: the scalar's octets

`cut_ok`: the loop `GenerateKey.cutBody` writes the octets of `rand` cut at
the bound's first nonzero octet (`KeyScalar.cut`) to `x`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain VG.Impl.Ffdh.AArch64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.WriteBytes (writeW8_apply)

/-- The octet `j` of the cut. -/
def cb (rb : List Byte) (ld : Nat) (t : Byte) (j : Nat) : Byte :=
  if j < ld then 0 else if j = ld then rb.getD j 0 &&& t else rb.getD j 0

/-- The carry of `subs`: no borrow. -/
theorem subs_c (x y : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~y).toNat + (true).toNat) = decide (y.toNat ≤ x.toNat) := by
  have h1 : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := by rw [BitVec.toNat_not]
  rw [h1, Bool.toNat_true]
  have := x.isLt
  have := y.isLt
  by_cases h : y.toNat ≤ x.toNat <;> simp [h] <;> omega

theorem partB_ok {t : State} {j ld : Nat} (hj : j < 2 ^ 32) (hld : ld < 2 ^ 32)
    (h10 : t.gpr .x10 = BitVec.ofNat 64 j) (h11 : t.gpr .x11 = BitVec.ofNat 64 ld)
    (h13 : t.gpr .x13 = BitVec.ofNat 64 255) (h7 : t.gpr .x7 = 0) :
    WP isa (.block [.subs .x .x5 .x10 .x11, .csel .x .x6 .x13 .x7]) t fun u =>
      (u.gpr .x6 = (if ld ≤ j then BitVec.ofNat 64 255 else 0) ∧ u.mem = t.mem) ∧ Keep [.x5, .x6] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h10, h11, h13, h7, subs_c]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ld < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
  simp only [decide_eq_true_eq]

theorem partC_ok {t : State} {j ld : Nat} {msk v : BitVec 64} (hj : j < 2 ^ 32) (hld : ld < 2 ^ 32)
    (h10 : t.gpr .x10 = BitVec.ofNat 64 j) (h11 : t.gpr .x11 = BitVec.ofNat 64 ld) (h12 : t.gpr .x12 = msk)
    (h6 : t.gpr .x6 = v) :
    WP isa (.block [.logic .eor .x .x5 .x10 .x11, movi .x8 1, .subs .x .x5 .x5 .x8, .csel .x .x6 .x6 .x12]) t
      fun u => (u.gpr .x6 = (if j = ld then msk else v) ∧ u.mem = t.mem) ∧ Keep [.x5, .x6, .x8] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h10, h11, h12, h6, subs_c]
  have e1 : (BitVec.setWidth 64 1#16).toNat = 1 := by decide
  rw [e1]
  by_cases hjl : j = ld
  · subst hjl
    simp
  · rw [ite_eq_right hjl]
    have hne : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 ld := fun he => hjl (by
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show ld < 2 ^ 64 by omega)] at this)
    have hx : BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 ld ≠ 0 := fun he => hne (by
      have := congrArg (· ^^^ BitVec.ofNat 64 ld) he
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      exact this.trans (BitVec.eq_of_toNat_eq (by simp)))
    have : 1 ≤ (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 ld).toNat := by
      rcases Nat.eq_zero_or_pos (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 ld).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hx
      · exact h
    simp only [decide_eq_true this, ↓reduceIte]

theorem partD_ok {t : State} {xp : Addr} {j : Nat} {b : Byte} {v : BitVec 64}
    (h2 : t.gpr .x2 = xp + BitVec.ofNat 64 j) (h4 : t.gpr .x4 = BitVec.setWidth 64 (BitVec.setWidth 32 b))
    (h6 : t.gpr .x6 = v) (hwr : InRegions t.wr (xp + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.logic .and .x .x4 .x4 .x6, .strb .x4 .x2 0]) t
      fun u => (u.mem = t.mem.write (xp + BitVec.ofNat 64 j) 1 (b &&& v.setWidth 8)) ∧ Keep [.x4] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h2, h4, h6, hwr]
  congr 1
  ext i hi
  simp

theorem partA_ok {t : State} {rp : Addr} {j : Nat} {b : Byte}
    (h1 : t.gpr .x1 = rp + BitVec.ofNat 64 j) (hrd : InRegions (t.rd ++ t.wr) (rp + BitVec.ofNat 64 j) 1)
    (hv : t.mem (rp + BitVec.ofNat 64 j) = b) :
    WP isa (.block [.ldrb .x4 .x1 0]) t
      fun u => (u.gpr .x4 = BitVec.setWidth 64 (BitVec.setWidth 32 b) ∧ u.mem = t.mem) ∧ Keep [.x4] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h1, hrd, VG.Proof.MlKem.AArch64.read_one, hv]

theorem partE_ok {t : State} {rp xp : Addr} {j : Nat} (h1 : t.gpr .x1 = rp + BitVec.ofNat 64 j)
    (h2 : t.gpr .x2 = xp + BitVec.ofNat 64 j) (h10 : t.gpr .x10 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .addImm .x .x10 .x10 1, .subImm .x .x14 .x14 1]) t
      fun u => (u.gpr .x1 = rp + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = xp + BitVec.ofNat 64 (j + 1) ∧
        u.gpr .x10 = BitVec.ofNat 64 (j + 1) ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 ∧ u.mem = t.mem) ∧
        Keep [.x1, .x2, .x10, .x14] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h1, h2, h10]
  rw [BitVec.ofNat_add]


theorem cut_byte (b t : Byte) {j ld : Nat} (msk : BitVec 64) (ht : t = msk.setWidth 8) :
    b &&& (if j = ld then msk else if ld ≤ j then BitVec.ofNat 64 255 else 0).setWidth 8 =
      if j < ld then 0 else if j = ld then b &&& t else b := by
  subst ht
  by_cases h1 : j < ld
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h1]
    simp
  · rw [ite_eq_right h1]
    by_cases h2 : j = ld
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left (by omega)]
      have : (BitVec.ofNat 64 255).setWidth 8 = (255 : Byte) := by decide
      rw [this]
      exact BitVec.and_allOnes

/-- After `j` octets of the cut from `s₀`. -/
structure CInv (s₀ : State) (rp xp : Addr) (rb : List Byte) (ld : Nat) (msk : BitVec 64) (j : Nat) (t : State) :
    Prop where
  keep : Keep [.x1, .x2, .x4, .x5, .x6, .x8, .x10, .x14] s₀ t
  x1 : t.gpr .x1 = rp + BitVec.ofNat 64 j
  x2 : t.gpr .x2 = xp + BitVec.ofNat 64 j
  x10 : t.gpr .x10 = BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (xp + BitVec.ofNat 64 i) = cb rb ld (msk.setWidth 8) i
  frame : ∀ x, (∀ i < j, x ≠ xp + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem cutStep_ok {s₀ t : State} {rp xp : Addr} {rb : List Byte} {k ld j : Nat} {msk : BitVec 64}
    (hk : k < 2 ^ 31) (hj : j < k) (hld : ld < k)
    (h11 : s₀.gpr .x11 = BitVec.ofNat 64 ld) (h12 : s₀.gpr .x12 = msk)
    (h13 : s₀.gpr .x13 = BitVec.ofNat 64 255) (h7 : s₀.gpr .x7 = 0)
    (hrd : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (rp + BitVec.ofNat 64 i) 1)
    (hv : ∀ i < k, s₀.mem (rp + BitVec.ofNat 64 i) = rb.getD i 0)
    (hwr : ∀ i < k, InRegions s₀.wr (xp + BitVec.ofNat 64 i) 1)
    (hne : ∀ i < k, ∀ i' < k, rp + BitVec.ofNat 64 i ≠ xp + BitVec.ofNat 64 i')
    (hI : CInv s₀ rp xp rb ld msk j t) :
    WP isa (.block (cutBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      CInv s₀ rp xp rb ld msk (j + 1) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have k₀ := hI.keep
  have t11 : t.gpr .x11 = BitVec.ofNat 64 ld := (k₀.gpr .x11 (by decide)).trans h11
  have t12 : t.gpr .x12 = msk := (k₀.gpr .x12 (by decide)).trans h12
  have t13 : t.gpr .x13 = BitVec.ofNat 64 255 := (k₀.gpr .x13 (by decide)).trans h13
  have t7 : t.gpr .x7 = 0 := (k₀.gpr .x7 (by decide)).trans h7
  have trd : InRegions (t.rd ++ t.wr) (rp + BitVec.ofNat 64 j) 1 := by rw [k₀.rd, k₀.wr]; exact hrd j hj
  have tv : t.mem (rp + BitVec.ofNat 64 j) = rb.getD j 0 := by
    rw [hI.frame _ fun i hi => hne j hj i (by omega)]; exact hv j hj
  have twr : InRegions t.wr (xp + BitVec.ofNat 64 j) 1 := by rw [k₀.wr]; exact hwr j hj
  rw [show cutBody ++ [.subImm .x .x14 .x14 1] = [.ldrb .x4 .x1 0] ++ ([.subs .x .x5 .x10 .x11,
      .csel .x .x6 .x13 .x7] ++ ([.logic .eor .x .x5 .x10 .x11, movi .x8 1, .subs .x .x5 .x5 .x8,
      .csel .x .x6 .x6 .x12] ++ ([.logic .and .x .x4 .x4 .x6, .strb .x4 .x2 0] ++ [.addImm .x .x1 .x1 1,
      .addImm .x .x2 .x2 1, .addImm .x .x10 .x10 1, .subImm .x .x14 .x14 1]))) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (partA_ok hI.x1 trd tv) fun t₁ ⟨⟨h4₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (partB_ok (j := j) (ld := ld) (by omega) (by omega)
    ((k₁.gpr .x10 (by decide)).trans hI.x10) ((k₁.gpr .x11 (by decide)).trans t11)
    ((k₁.gpr .x13 (by decide)).trans t13) ((k₁.gpr .x7 (by decide)).trans t7)) fun t₂ ⟨⟨h6₂, hm₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (partC_ok (j := j) (ld := ld) (by omega) (by omega)
    ((k12.gpr .x10 (by decide)).trans hI.x10) ((k12.gpr .x11 (by decide)).trans t11)
    ((k12.gpr .x12 (by decide)).trans t12) h6₂) fun t₃ ⟨⟨h6₃, hm₃⟩, k₃⟩ => ?_)
  have k123 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (partD_ok (j := j) ((k123.gpr .x2 (by decide)).trans hI.x2)
    ((k₂.trans k₃).gpr .x4 (by decide) |>.trans h4₁) h6₃ (by rw [k123.wr]; exact twr))
    fun t₄ ⟨hm₄, k₄⟩ => ?_)
  have k1234 := k123.trans k₄
  refine WP.mono (partE_ok (rp := rp) (xp := xp) (j := j) ((k1234.gpr .x1 (by decide)).trans hI.x1)
    ((k1234.gpr .x2 (by decide)).trans hI.x2) ((k1234.gpr .x10 (by decide)).trans hI.x10))
    fun u ⟨⟨h1', h2', h10', h14', hm'⟩, k₅⟩ => ⟨⟨(k₀.trans (k1234.trans k₅)).mono (by decide), h1', h2', h10', ?_, ?_⟩,
      by rw [h14', k1234.gpr .x14 (by decide)]⟩
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro i hi
    rw [hm', hm₄, hm₃, hm₂, hm₁, hw8, writeW8_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, cut_byte _ _ msk rfl]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (by omega)))]
      exact hI.bytes i (by omega)
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro x hx
    rw [hm', hm₄, hm₃, hm₂, hm₁, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- The cut loop: `k` octets of `rand` (at `x1`) to `x` (at `x2`). -/
theorem cut_ok {s : State} {rp xp : Addr} {rb : List Byte} {k ld : Nat} {msk : BitVec 64}
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 31) (hld : ld < k) (h1 : s.gpr .x1 = rp) (h2 : s.gpr .x2 = xp)
    (h10 : s.gpr .x10 = 0) (h11 : s.gpr .x11 = BitVec.ofNat 64 ld) (h12 : s.gpr .x12 = msk)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 255) (h7 : s.gpr .x7 = 0) (h14 : s.gpr .x14 = BitVec.ofNat 64 k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (rp + BitVec.ofNat 64 i) 1)
    (hv : ∀ i < k, s.mem (rp + BitVec.ofNat 64 i) = rb.getD i 0)
    (hwr : ∀ i < k, InRegions s.wr (xp + BitVec.ofNat 64 i) 1)
    (hne : ∀ i < k, ∀ i' < k, rp + BitVec.ofNat 64 i ≠ xp + BitVec.ofNat 64 i') :
    WP isa (countLoop .x14 cutBody) s (CInv s rp xp rb ld msk k) :=
  wp_countdown (by omega) (by omega) (CInv s rp xp rb ld msk)
    (fun j hj t hI _ => cutStep_ok hk hj hld h11 h12 h13 h7 hrd hv hwr hne hI)
    ⟨Keep.refl _ _, by rw [h1]; simp, by rw [h2]; simp, by rw [h10]; rfl, fun i hi => absurd hi (by omega),
      fun _ _ => rfl⟩ h14

/-! ## The outputs masked -/

/-- After `j` octets of `maskOut` from `s₀`. -/
structure MInv (s₀ : State) (op : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x2, .x4] s₀ t
  x1 : t.gpr .x1 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if c then s₀.mem (op + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem maskB_ok {t : State} {op : Addr} {j : Nat} {c : Bool} (h1 : t.gpr .x1 = op + BitVec.ofNat 64 j)
    (h15 : t.gpr .x15 = mask c) (hwr : InRegions t.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.ldrb .x4 .x1 0, .logic .and .x .x4 .x4 .x15, .strb .x4 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u =>
      (u.mem = t.mem.write (op + BitVec.ofNat 64 j) 1 (if c then t.mem (op + BitVec.ofNat 64 j) else 0) ∧
        u.gpr .x1 = op + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1) ∧
      Keep [.x1, .x2, .x4] t u := by
  have hrd : InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 j) 1 :=
    let ⟨r, hr, hc⟩ := hwr; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h1, h15, hrd, hwr, VG.Proof.MlKem.AArch64.read_one]
  congr 1
  cases c
  · simp [mask]
  · rw [show mask true = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have := (t.mem (op + BitVec.ofNat 64 j)).isLt
    simp

theorem maskStep_ok {s₀ t : State} {op : Addr} {len j : Nat} {c : Bool} (hl : len < 2 ^ 31) (hj : j < len)
    (h15 : s₀.gpr .x15 = mask c) (hwr : ∀ i < len, InRegions s₀.wr (op + BitVec.ofNat 64 i) 1)
    (hI : MInv s₀ op c j t) :
    WP isa (.block [.ldrb .x4 .x1 0, .logic .and .x .x4 .x4 .x15, .strb .x4 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u => MInv s₀ op c (j + 1) u ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have k₀ := hI.keep
  refine WP.mono (maskB_ok hI.x1 ((k₀.gpr .x15 (by decide)).trans h15) (by rw [k₀.wr]; exact hwr j hj))
    fun u ⟨⟨hm, h1, h2⟩, k⟩ => ⟨⟨(k₀.trans k).mono (by decide), h1, ?_, ?_⟩, h2⟩
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro i hi
    rw [hm, hw8, writeW8_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hI.frame _ fun i' hi' => out_ne (by omega) (by omega) (by omega)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (by omega)))]
      exact hI.bytes i (by omega)
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro x hx
    rw [hm, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- `maskOut sPtr`: the `len` octets at the pointer in slot `sPtr` and'ed with
`mask c`. -/
theorem maskOut_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {sPtr len : Nat} {op : Addr} {c : Bool} (hP : sPtr < 32) (hO : word s.mem B (8 * sPtr) = op)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 len) (hk1 : 1 ≤ len) (hk' : len < 2 ^ 31)
    (h15 : s.gpr .x15 = mask c) (hwr : ∀ i < len, InRegions s.wr (op + BitVec.ofNat 64 i) 1) :
    WP isa (maskOut sPtr) s fun t =>
      (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = if c then s.mem (op + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < len, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.x1, .x2, .x4] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold maskOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 len ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc hP, hdr_enc (show sK < 32 by decide), hl sPtr hP, hl sK (by decide), hO, hK]) rfl rfl rfl)
    fun s₁ ⟨⟨h1, h2, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := len) (by omega) (by omega) (MInv s₁ op c)
    (fun j hj t hI _ => maskStep_ok hk' hj ((k₁.gpr .x15 (by decide)).trans h15)
      (fun i hi => by rw [k₁.wr]; exact hwr i hi) hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  exact ⟨fun i hi => by rw [hI.bytes i hi, hm₁], fun x hx => by rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono
    (by decide)⟩

end VG.Proof.Ffdh.AArch64.GenerateKey
