module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Ffdh.AArch64.Cached.OutputFrame`, which this module and modules that import it used -/

section

/-! Convert a precise output-byte frame to the API's region frame. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem outside_frame_member {rs : List Region} {ptr : Addr} {k : Nat} {m m' : Mem}
 (frame : Outside ptr 0 k m m') (member : (⟨ptr,k⟩ : Region)∈rs) : Frame rs m m' := by
 intro x hx
 apply frame x
 right
 have no := hx ⟨ptr,k⟩ member
 change ¬ofs ptr x+1≤k at no
 omega_using [no]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.GenerateKey.Cut`, which this module and modules that import it used -/

section

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
  by_cases h : y.toNat ≤ x.toNat <;> simp [h] <;> omega_arith

theorem partB_ok {t : State} {j ld : Nat} (hj : j < 2 ^ 32) (hld : ld < 2 ^ 32)
    (h10 : t.gpr .x10 = BitVec.ofNat 64 j) (h11 : t.gpr .x11 = BitVec.ofNat 64 ld)
    (h13 : t.gpr .x13 = BitVec.ofNat 64 255) (h7 : t.gpr .x7 = 0) :
    WP isa (.block [.subs .x .x5 .x10 .x11, .csel .x .x6 .x13 .x7]) t fun u =>
      (u.gpr .x6 = (if ld ≤ j then BitVec.ofNat 64 255 else 0) ∧ u.mem = t.mem) ∧ Keep [.x5, .x6] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h10, h11, h13, h7, subs_c]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ld < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith)]
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
      rwa [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show ld < 2 ^ 64 by omega_arith)] at this)
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
  · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left h1]
    simp
  · rw [ite_eq_right h1]
    by_cases h2 : j = ld
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left (by omega_arith)]
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
    rw [hI.frame _ fun i hi => hne j hj i (by omega_arith)]; exact hv j hj
  have twr : InRegions t.wr (xp + BitVec.ofNat 64 j) 1 := by rw [k₀.wr]; exact hwr j hj
  rw [show cutBody ++ [.subImm .x .x14 .x14 1] = [.ldrb .x4 .x1 0] ++ ([.subs .x .x5 .x10 .x11,
      .csel .x .x6 .x13 .x7] ++ ([.logic .eor .x .x5 .x10 .x11, movi .x8 1, .subs .x .x5 .x5 .x8,
      .csel .x .x6 .x6 .x12] ++ ([.logic .and .x .x4 .x4 .x6, .strb .x4 .x2 0] ++ [.addImm .x .x1 .x1 1,
      .addImm .x .x2 .x2 1, .addImm .x .x10 .x10 1, .subImm .x .x14 .x14 1]))) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (partA_ok hI.x1 trd tv) fun t₁ ⟨⟨h4₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (partB_ok (j := j) (ld := ld) (by omega_arith) (by omega_arith)
    ((k₁.gpr .x10 (by decide)).trans hI.x10) ((k₁.gpr .x11 (by decide)).trans t11)
    ((k₁.gpr .x13 (by decide)).trans t13) ((k₁.gpr .x7 (by decide)).trans t7)) fun t₂ ⟨⟨h6₂, hm₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (partC_ok (j := j) (ld := ld) (by omega_arith) (by omega_arith)
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
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_arith) (by omega_arith) (by omega_arith)))]
      exact hI.bytes i (by omega_arith)
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro x hx
    rw [hm', hm₄, hm₃, hm₂, hm₁, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_arith)))]
    exact hI.frame x fun i hi => hx i (by omega_arith)

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
  wp_countdown (by omega_arith) (by omega_arith) (CInv s rp xp rb ld msk)
    (fun j hj t hI _ => cutStep_ok hk hj hld h11 h12 h13 h7 hrd hv hwr hne hI)
    ⟨Keep.refl _ _, by rw [h1]; simp, by rw [h2]; simp, by rw [h10]; rfl, fun i hi => absurd hi (by omega_arith),
      fun _ _ => rfl⟩ h14

/-! ## The outputs masked -/

end VG.Proof.Ffdh.AArch64.GenerateKey

end

end

/-! ### `Ffdh.AArch64.Cached.MaskOutputLoop`, which only this module used -/

section

/-! A fixed-length scalar mask preserves success bytes and zeroes failure bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.WriteBytes (writeW8_apply)

structure MaskOutputInv (s₀ : State) (op : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x2, .x3] s₀ t
  x1 : t.gpr .x1 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if c then s₀.mem (op + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem maskOutputByte_ok {t : State} {op : Addr} {j : Nat} {c : Bool} (h1 : t.gpr .x1 = op + BitVec.ofNat 64 j)
    (h15 : t.gpr .x15 = mask c) (hwr : InRegions t.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x15, .strb .x3 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u =>
      (u.mem = t.mem.write (op + BitVec.ofNat 64 j) 1 (if c then t.mem (op + BitVec.ofNat 64 j) else 0) ∧
        u.gpr .x1 = op + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1) ∧
      Keep [.x1, .x2, .x3] t u := by
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

theorem maskOutputStep_ok {s₀ t : State} {op : Addr} {len j : Nat} {c : Bool} (hl : len < 2 ^ 31) (hj : j < len)
    (h15 : s₀.gpr .x15 = mask c) (hwr : ∀ i < len, InRegions s₀.wr (op + BitVec.ofNat 64 i) 1)
    (hI : MaskOutputInv s₀ op c j t) :
    WP isa (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x15, .strb .x3 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u => MaskOutputInv s₀ op c (j + 1) u ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have k₀ := hI.keep
  refine WP.mono (maskOutputByte_ok hI.x1 ((k₀.gpr .x15 (by decide)).trans h15) (by rw [k₀.wr]; exact hwr j hj))
    fun u ⟨⟨hm, h1, h2⟩, k⟩ => ⟨⟨(k₀.trans k).mono (by decide), h1, ?_, ?_⟩, h2⟩
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro i hi
    rw [hm, hw8, writeW8_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hI.frame _ fun i' hi' => out_ne (by omega_using [hl, hj]) (by omega_using [hl, hj, hi']) (by omega_using [hi'])]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hl, hj, hi]) (by omega_using [hl, hj]) (by omega_using [hij])))]
      exact hI.bytes i (by omega_using [hi, hij])
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro x hx
    rw [hm, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])

theorem maskOutputLoop_ok {s : State} {out : Addr} {k : Nat} {c : Bool}
 (positive : 0<k) (size : k<2^31) (pointer : s.gpr .x1=out) (count : s.gpr .x2=BitVec.ofNat 64 k)
 (maskValue : s.gpr .x15=mask c) (writable : ∀ i<k,InRegions s.wr (out+BitVec.ofNat 64 i) 1) :
 WP isa (countLoop .x2 [.ldrb .x3 .x1 0,.logic .and .x .x3 .x3 .x15,.strb .x3 .x1 0,.addImm .x .x1 .x1 1]) s fun t =>
 Spec.Rsa.bytesAt t.mem out k=(if c then Spec.Rsa.bytesAt s.mem out k else List.replicate k 0) ∧
 Outside out 0 k s.mem t.mem ∧ Keep [.x1,.x2,.x3] s t := by
 refine WP.mono (wp_countdown (N:=k) (by omega_using [size]) (by omega_using [positive]) (MaskOutputInv s out c)
  (fun j hj t inv _ =>maskOutputStep_ok size hj maskValue writable inv)
  ⟨Keep.refl _ _,by simpa only [show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using pointer,
   fun _ h =>by omega,fun _ _ =>rfl⟩ count) ?_
 intro t inv
 refine ⟨?_,?_,inv.keep⟩
 · cases c
   · change Spec.Rsa.bytesAt t.mem out k=List.replicate k 0
     apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,List.length_replicate]
     · intro i hi _
       have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range,List.getElem_replicate]
       simpa using inv.bytes i bound
   · change Spec.Rsa.bytesAt t.mem out k=Spec.Rsa.bytesAt s.mem out k
     apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
     · intro i hi _
       have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
       simpa using inv.bytes i bound
 · intro x hx
   apply inv.frame x
   intro i hi eq
   subst x
   rw [show ofs out (out+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at hx
   omega_using [hi, hx]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Serialize both outputs with the same success mask and return exactly 1 or 3. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/MaskX.lean`, which only this module imported.
section

/-! Mask the private output according to the final 0/1 public-result predicate. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem maskX_ok {s : State} {B out : Addr} {Z k : Nat} {c : Bool}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (positive : 0<k) (size : k<2^31)
 (pointer : word s.mem B (8*sX)=out) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (flag : word s.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat)
 (writable : ∀ i<k,InRegions s.wr (out+BitVec.ofNat 64 i) 1)
 (outside : ∀ i<k,Z≤ofs B (out+BitVec.ofNat 64 i)) :
 WP isa Generate.maskX s fun t =>
 Spec.Rsa.bytesAt t.mem out k=(if c then Spec.Rsa.bytesAt s.mem out k else List.replicate k 0) ∧
 t.gpr .x15=mask c ∧ Outside out 0 k s.mem t.mem ∧
 (∀ q,ofs B q<Z→t.mem q=s.mem q) ∧ Keep [.x1,.x2,.x3,.x7,.x15] s t := by
 have neg : (0#64 : Addr)-BitVec.ofNat 64 c.toNat=mask c := by cases c <;>rfl
 unfold Generate.maskX
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2,.x3,.x7,.x15] (Q:=fun a =>a.gpr .x1=out ∧
  a.gpr .x2=BitVec.ofNat 64 k ∧ a.gpr .x15=mask c ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [base,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sTmp<32 by decide),
    scratch.ld (d:=8*sX) (by unfold sX;omega_using [room]),scratch.ld (d:=8*sLen) (by unfold sLen;omega_using [room]),
    scratch.ld (d:=8*sTmp) (by unfold sTmp;omega_using [room]),pointer,length,flag,neg]
   exact neg
 · rintro a ⟨⟨ptrA,countA,maskA,memA⟩,restA⟩
   refine WP.mono (maskOutputLoop_ok positive size ptrA countA maskA
    (fun i hi =>by rw [restA.wr];exact writable i hi)) ?_
   rintro t ⟨bytes,frame,rest⟩
   have fullFrame : Outside out 0 k s.mem t.mem := by rw [←memA];exact frame
   refine ⟨by rw [memA] at bytes;exact bytes,(rest.gpr .x15 (by decide)).trans maskA,fullFrame,?_,
    (restA.trans rest).mono (by simp)⟩
   intro q hq
   exact fullFrame q (Or.inr (by have sep : k≤ofs out q :=le_ofs_of_sep outside hq;omega_using [sep]))

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem finish_ok {s : State} {B xp yp : Addr} {Z w k : Nat} {mi : BitVec 64} {c : Bool}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (x : word s.mem B (8*sX)=xp) (y : word s.mem B (8*sY)=yp) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (flag : word s.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat)
 (writeX : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (outsideY : ∀ i<k,Z≤ofs B (yp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,k≤ofs yp (xp+BitVec.ofNat 64 i)) :
 WP isa Generate.finish s fun t =>
 t.gpr .x0=(if c then 1#64 else 3#64) ∧
 Spec.Rsa.bytesAt t.mem xp k=(if c then Spec.Rsa.bytesAt s.mem xp k else List.replicate k 0) ∧
 Spec.Rsa.bytesAt t.mem yp k=Spec.Rsa.i2osp (if c then wv s.mem B (slot w 6) w else 0) k ∧
 Frame [⟨xp,k⟩,⟨yp,k⟩] s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 have room256 : 256≤Z := by unfold slot hdrBytes at room;omega_using [room]
 have yRoom := Nat.le_trans (slot_le (w:=w) (show 6<8 by decide)) room
 have wPositive : 0<w := by rw [words];omega_using [positive]
 unfold Generate.finish
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (maskX_ok good.scr room256 good.x0 positive size x length flag writeX outsideX) ?_
 rintro a ⟨bytesX,maskA,frameA,sameA,restA⟩
 have headerA (i : Nat) (hi : i<32) : word a.mem B (8*i)=word s.mem B (8*i) :=
  workspace_word (by have := good.scr.nowrap;omega_using [this]) sameA (by have := hdr_lt_slot w 8 hi;omega_using [room256, hi])
 have goodA : Good a B Z w mi :=
  ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,
   (headerA sW (by decide)).trans good.hdr.hw,(headerA sMinv (by decide)).trans good.hdr.hminv,
   fun i hi =>(headerA (sArr i) (by unfold sArr;omega_using [hi])).trans (good.hdr.harr i hi)⟩
 have arrayA : wv a.mem B (slot w 6) w=wv s.mem B (slot w 6) w := by
  apply wv_congr
  intro i hi
  exact workspace_word (by have := good.scr.nowrap;omega_using [this]) sameA (by omega_using [yRoom, hi])
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x8,.x1,.x9] (Q:=fun b =>b.gpr .x8=off B (slot w 6) ∧
  b.gpr .x1=yp+BitVec.ofNat 64 k ∧ b.gpr .x9=BitVec.ofNat 64 k ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sArr 6<32 by decide),hdr_enc (show sY<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read goodA room (show sArr 6<32 by decide),header_read goodA room (show sY<32 by decide),
    header_read goodA room (show sLen<32 by decide),goodA.hdr.harr 6 (by decide),
    (headerA sY (by decide)).trans y,(headerA sLen (by decide)).trans length]
 · rintro b ⟨⟨srcB,dstB,countB,memB⟩,restB⟩
   have before := restA.trans restB
   rw [WP.seq_iff]
   refine WP.mono (storeBE_ok (good.scr.congr before.wr) srcB dstB countB
    ((restB.gpr .x15 (by decide)).trans maskA) (by omega_using [positive]) size words (by omega_using [yRoom])
    (fun i hi =>by rw [before.wr];exact writeY i hi) outsideY) ?_
   rintro d ⟨bytesY,storeFrame,_,_,restD⟩
   have frameD : Outside yp 0 k b.mem d.mem := by
    intro q hq
    apply storeFrame q
    intro i hi eq
    subst q
    rw [show ofs yp (yp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega_using [size, hi])] at hq
    omega_using [room, words, positive, size, x, y, length, flag, room256, yRoom, wPositive, maskA, arrayA, srcB, dstB, countB, hi, hq]
   have sameD (q : Addr) (hq : ofs B q<Z) : d.mem q=s.mem q := by
    rw [frameD q (Or.inr (by have sep : k≤ofs yp q :=le_ofs_of_sep outsideY hq;omega_using [sep])),memB]
    exact sameA q hq
   have flagD : word d.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat :=
    (workspace_word (by have := good.scr.nowrap;omega_using [this]) sameD
     (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this])).trans flag
   have xD : Spec.Rsa.bytesAt d.mem xp k=(if c then Spec.Rsa.bytesAt s.mem xp k else List.replicate k 0) := by
    rw [←bytesX]
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
    · intro i hi _
      have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
      simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
      rw [frameD _ (Or.inr (by have := separate i bound;omega_using [this])),memB]
   have yD : Spec.Rsa.bytesAt d.mem yp k=Spec.Rsa.i2osp (if c then wv s.mem B (slot w 6) w else 0) k := by
    change (List.range k).map (fun i =>d.mem (yp+BitVec.ofNat 64 i))=_
    rw [bytesY,memB,arrayA]
   have total := before.trans restD
   have ret : (3#64 : Addr)-(BitVec.ofNat 64 c.toNat <<< 1)=(if c then 1#64 else 3#64) := by cases c <;>rfl
   refine WP.mono (WP.keep [.x9,.x0] (Q:=fun t =>t.gpr .x0=(if c then 1#64 else 3#64) ∧ t.mem=d.mem) ?_ rfl rfl rfl) ?_
   · brun [(total.gpr .x0 (by simp)).trans good.x0,hdr_enc (show sTmp<32 by decide),flagD,
      (good.scr.congr total.wr).ld (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this]),ret]
     exact ret
   · rintro t ⟨⟨status,mem⟩,rest⟩
     have lastFrame : Outside yp 0 k a.mem d.mem := by rw [←memB];exact frameD
     exact ⟨status,by rw [mem];exact xD,by rw [mem];exact yD,
      by rw [mem];exact (outside_frame_member frameA (by simp)).trans (outside_frame_member lastFrame (by simp)),
      (total.trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
