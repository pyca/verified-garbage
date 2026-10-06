import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS on AArch64: the encoding's parameters

From the modulus' first byte `n₀ ≠ 0` in `x10`, `smear` leaves
`2^⌊log₂ n₀⌋ - 1` in `x11`, 0 iff `n₀ = 1` (`smear_ok`); `emLen` stores the
mask `0xFF >>> z` and `lo = k - emLen` to their slots and leaves `emLen` in
`x9`, `x10` nonzero iff `emLen < hLen + 2` (`emLen_ok`); `saltFits` leaves
`emLen - hLen - 2` in `x9`, `x10` nonzero iff the salt is longer
(`saltFits_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_orr wp_strx wp_sub
  eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_addSp wp_mov setWidth_ofNat16 borrow_ne)

/-- What `smear` computes from `y`. -/
abbrev smearV (y : BitVec 64) : BitVec 64 :=
  y >>> 1 ||| y >>> 1 >>> 1 ||| (y >>> 1 ||| y >>> 1 >>> 1) >>> 2 |||
    (y >>> 1 ||| y >>> 1 >>> 1 ||| (y >>> 1 ||| y >>> 1 >>> 1) >>> 2) >>> 4

theorem smear_table : ∀ x < 256, x ≠ 0 → x ≠ 1 →
    ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ smearV (BitVec.ofNat 64 x) = BitVec.ofNat 64 (2 ^ j - 1) := by
  decide +kernel

theorem smear_val {x : Nat} (hx : x < 256) (h0 : x ≠ 0) :
    smearV (BitVec.ofNat 64 x) = if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1) := by
  by_cases h1 : x = 1
  · subst h1; decide
  · obtain ⟨j, _, hl, hu, he⟩ := smear_table x hx h0 h1
    rw [ite_eq_right h1, he, RsaPss.log2_eq h0 hl hu]

theorem smear_ok (u : State) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (h10 : u.gpr .x10 = BitVec.ofNat 64 x) :
    WP isa (.block smear) u fun u' => Only [.x11, .x12] u u' ∧
      u'.gpr .x11 = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)) := by
  unfold smear
  refine wp_lsr (by decide) fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => wp_orr fun u₃ o₃ e₃ =>
    wp_lsr (by decide) fun u₄ o₄ e₄ => wp_orr fun u₅ o₅ e₅ => wp_lsr (by decide) fun u₆ o₆ e₆ =>
    wp_orr fun u₇ o₇ e₇ => wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono, ?_⟩
  rw [e₇, e₆, o₆.get .x11, e₅, e₄, o₄.get .x11, e₃, e₂, o₂.get .x11, e₁, h10]
  exact smear_val hx h0

theorem mask_ne {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (h1 : x ≠ 1) : BitVec.ofNat 64 (2 ^ Nat.log2 x - 1) ≠ 0 := by
  have h2 : 2 ^ Nat.log2 x - 1 < 2 ^ 64 := by
    have : Nat.log2 x < 8 := (Nat.log2_lt h0).mpr hx
    have : 2 ^ Nat.log2 x ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h3 : 2 ^ Nat.log2 x - 1 ≠ 0 := by
    have := (Nat.le_log2 h0).mpr (show 2 ^ 1 ≤ x by omega)
    have : 2 ^ 1 ≤ 2 ^ Nat.log2 x := Nat.pow_le_pow_right (by decide) this
    omega
  intro h
  exact h3 (by have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt h2] using this)

/-- `lo = k - emLen`: 1 if `n₀ = 1`. -/
def loV (x : Nat) : Nat := if x = 1 then 1 else 0

/-- The mask `0xFF >>> z`, as a word. -/
def maskV (x : Nat) : BitVec 64 := if x = 1 then BitVec.ofNat 64 0xFF else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)

/-- A slot of the frame, written. -/
theorem st_slot {t : State} {F : Addr} {d : Nat} (hsp : t.sp = F) (hd : d % 8 = 0 ∧ d < 32768)
    (hw : InRegions t.wr (F + BitVec.ofNat 64 d) 8) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Keep [.x16] t t' → t'.mem = t.mem.writeW (F + BitVec.ofNat 64 d) (t.gpr r) →
      t'.gpr .x16 = F → WP isa (.block is) t' Q) (hr : r ≠ .x16) :
    WP isa (.block (st r d ++ is)) t Q := by
  unfold st
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine wp_strx hd (by rw [e₁]) (by rw [o₁.wr]; exact hw) fun u₂ m₂ => k u₂ (o₁.keep.trans m₂.keep).mono
    (by rw [m₂.mem, o₁.mem, o₁.get r (by simpa using hr)]) (by rw [m₂.gpr, e₁])

theorem emLen_ok (H : Hash) (hD : H.D + 2 < 4096) {u : State} {F : Addr} (hsp : u.sp = F) {x : Nat} (hx : x < 256)
    (h0 : x ≠ 0)
    (hwC : InRegions u.wr (F + BitVec.ofNat 64 sC) 8) (hwL : InRegions u.wr (F + BitVec.ofNat 64 sLo) 8)
    {k : Nat} (hk : u.gpr .x23 = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32)
    (h11 : u.gpr .x11 = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1))) :
    WP isa (emLen H) u fun u' => Keep [.x11, .x12, .x16, .x9, .x10] u u' ∧
      u'.mem = (u.mem.writeW (F + BitVec.ofNat 64 sC) (maskV x)).writeW (F + BitVec.ofNat 64 sLo)
        (BitVec.ofNat 64 (loV x)) ∧
      u'.gpr .x9 = BitVec.ofNat 64 (k - loV x) ∧ (u'.gpr .x10 != 0) = decide (k - loV x < H.D + 2) := by
  have hl : loV x ≤ 1 := by unfold loV; split <;> omega
  have hl' : loV x ≤ k := by omega
  unfold emLen
  refine WP.seq (WP.mono (Q := fun (v : State) => Only [.x11, .x12] u v ∧ v.gpr .x11 = maskV x ∧
      v.gpr .x12 = BitVec.ofNat 64 (loV x)) ?_ fun v ⟨O, h11', h12'⟩ => ?_)
  · refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · have h1 : x = 1 := by
        by_contra h; rw [h11, ite_eq_right h, beq_iff_eq] at hb; exact mask_ne hx h0 h hb
      exact wp_movz fun v₁ o₁ e₁ => wp_movz fun v₂ o₂ e₂ => wp_nil ⟨(o₁.trans o₂).mono,
        by rw [o₂.get .x11, e₁, maskV, ite_eq_left h1]; rfl, by rw [e₂, loV, ite_eq_left h1]; rfl⟩
    · have h1 : x ≠ 1 := fun h => by rw [h11, ite_eq_left h] at hb; exact absurd hb (by decide)
      exact wp_movz fun v₁ o₁ e₁ => wp_nil ⟨o₁.mono, by rw [o₁.get .x11, h11, maskV, ite_eq_right h1,
        ite_eq_right h1], by rw [e₁, loV, ite_eq_right h1]; rfl⟩
  rw [List.append_assoc]
  refine st_slot (by rw [O.sp, hsp]) (by decide) (by rw [O.wr]; exact hwC) (fun v₁ k₁ m₁ x₁ => ?_) (by decide)
  refine st_slot (by rw [k₁.sp, O.sp, hsp]) (by decide) (by rw [k₁.wr, O.wr]; exact hwL) (fun v₂ k₂ m₂ x₂ => ?_)
    (by decide)
  refine wp_sub fun v₃ o₃ e₃ => wp_subImm (by omega) fun v₄ o₄ e₄ => wp_lsr (by decide) fun v₅ o₅ e₅ => wp_nil
    ⟨(O.keep.trans (k₁.trans (k₂.trans (o₃.keep.trans (o₄.keep.trans o₅.keep))))).mono, ?_, ?_, ?_⟩
  · rw [o₅.mem, o₄.mem, o₃.mem, m₂, m₁, O.mem, k₁.get .x12, h12', h11']
  · rw [o₅.get .x9, o₄.get .x9, e₃, k₂.get .x23, k₁.get .x23, O.get .x23, hk, k₂.get .x12, k₁.get .x12, h12',
      Offset.ofNat_sub_ofNat hl']
  · rw [e₅, e₄, e₃, k₂.get .x23, k₁.get .x23, O.get .x23, hk, k₂.get .x12, k₁.get .x12, h12',
      Offset.ofNat_sub_ofNat hl']
    exact borrow_ne (by omega) (by omega)

theorem saltFits_ok (H : Hash) (hD : H.D + 2 < 4096) {u : State} {F : Addr} (hsp : u.sp = F)
    (hrS : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 sSaltLen) 8) {a sl : Nat}
    (ha : H.D + 2 ≤ a) (ha' : a < 2 ^ 32) (h9 : u.gpr .x9 = BitVec.ofNat 64 a)
    (hsl : u.mem.readW (F + BitVec.ofNat 64 sSaltLen) 64 = BitVec.ofNat 64 sl) (hsl' : sl < 2 ^ 62) :
    WP isa (.block ([ld .x12 sSaltLen] ++ saltFits H)) u fun u' => Only [.x12, .x9, .x10] u u' ∧
      u'.gpr .x9 = BitVec.ofNat 64 (a - (H.D + 2)) ∧ (u'.gpr .x10 != 0) = decide (a - (H.D + 2) < sl) := by
  unfold saltFits ld
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) (by rw [hsp]; exact hrS) fun u₁ o₁ e₁ => wp_subImm (by omega) fun u₂ o₂ e₂ =>
    wp_sub fun u₃ o₃ e₃ => wp_lsr (by decide) fun u₄ o₄ e₄ => wp_nil
      ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_⟩
  · rw [o₄.get .x9, o₃.get .x9, e₂, o₁.get .x9, h9, Offset.ofNat_sub_ofNat ha]
  · rw [e₄, e₃, e₂, o₁.get .x9, h9, Offset.ofNat_sub_ofNat ha, o₂.get .x12, e₁, hsp, hsl]
    exact borrow_ne (by omega) (by omega)

end VG.Proof.RsaPss.AArch64