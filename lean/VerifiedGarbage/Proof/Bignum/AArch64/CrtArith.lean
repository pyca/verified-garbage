import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-!
# Multiword arithmetic on AArch64: addition and subtraction modulo `m`

`addMod o a b`: `[o] := [a] + [b] mod m` (`addMod_ok`), as `double` does
for `2 [o]`. `subModArr o a b`: `[o] := [a] - [b] mod m` (`subModArr_ok`):
`subMod`'s loop into the accumulator, then `m` added under the mask of its
borrow (`borrowMask`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The value `borrowMask` selects: all ones iff the carry is clear. -/
theorem csel_mask_not (c : Bool) :
    (if c then (0 : BitVec 64) else 0 - BitVec.ofNat 64 1) = mask (!c) := by
  cases c <;> rfl

/-- The same, with `x7 := 0` by `movz`. -/
theorem csel_mask' (c : Bool) :
    (if c then BitVec.setWidth 64 (0#16) else BitVec.setWidth 64 (0#16) - 1#64) = mask (!c) := by
  cases c <;> rfl

/-- `borrowMask`: `x15 := mask (!C)`. -/
theorem borrowMask_ok (s : State) (h7 : s.gpr .x7 = 0) :
    WP isa (.block borrowMask) s fun t =>
      (t.gpr .x15 = mask (!s.c) ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [.x4, .x15] s t :=
  WP.keep [.x4, .x15] (by brun [borrowMask, h7, csel_mask_not]) (by decide) (by decide) (by decide +kernel)

/-! ## Addition -/

/-- After `j` words of `addMod`'s loop: `A_j + 2^(64 j) C = a_j + b_j` for
the carry flag `C`. -/
structure AddInv (s₀ : State) (B : Addr) (Z eA ea eb : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x9, .x14, .x16, .x17] s₀ t
  x9 : t.gpr .x9 = off B (ea + 8 * j)
  x17 : t.gpr .x17 = off B (eb + 8 * j)
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : wv t.mem B eA j + 2 ^ (64 * j) * t.c.toNat = wv s₀.mem B ea j + wv s₀.mem B eb j

theorem addStep_ok {s₀ : State} {B : Addr} {Z w eA ea eb : Nat}
    (hA : eA + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sa : ea + 8 * w ≤ eA ∨ eA + 8 * w ≤ ea) (sb : eb + 8 * w ≤ eA ∨ eA + 8 * w ≤ eb)
    {j : Nat} (hj : j < w) {t : State} (hI : AddInv s₀ B Z eA ea eb j t) :
    WP isa (.block ([ld .x3 .x9, ld .x4 .x17, .adcs .x .x3 .x3 .x4, st .x3 .x16, next .x9, next .x17,
        next .x16] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => AddInv s₀ B Z eA ea eb (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x9, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (word t.mem B (ea + 8 * j) + word t.mem B (eb + 8 * j) +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (ea + 8 * j)).toNat + (word t.mem B (eb + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x9 = off B (ea + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eb + 8 * j + 8) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8))
    (by brun [hI.x9, hI.x17, hI.x16, hI.scr.ld (show ea + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eb + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h9, h17, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (ea + 8 * j) = word s₀.mem B (ea + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eb + 8 * j) = word s₀.mem B (eb + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x9 (by decide), h9, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := adcs_toNat (word t.mem B (ea + 8 * j)) (word t.mem B (eb + 8 * j)) t.c
    rw [hx, hy] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy]
    grind

/-- Two arrays of the workspace, distinct, are apart. -/
theorem arr_sep {w j k : Nat} (h : j ≠ k) :
    slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := slot_sep h

/-- `[o] := [a] + [b] mod m`, for `[a], [b] < m = [aN]`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aTmp) (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w Public.aN) w)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w Public.aN) w) :
    WP isa (addMod o a b) s fun t =>
      wv t.mem B (slot w o) w = (wv s.mem B (slot w a) w + wv s.mem B (slot w b) w) %
        wv s.mem B (slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, Public.aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  have hacc : Public.aAcc < 8 := by decide
  have htmp : Public.aTmp < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  have d5 : Public.aAcc ≠ Public.aN := by decide
  have d6 : Public.aAcc ≠ Public.aTmp := by decide
  have d7 : Public.aTmp ≠ Public.aN := by decide
  unfold addMod
  refine WP.seq (WP.mono (WP.keep [.x3, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x9 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧ t.gpr .x10 = off B (slot w Public.aN) ∧
      t.gpr .x8 = off B (slot w Public.aAcc) ∧ t.gpr .x6 = off B (slot w Public.aTmp) ∧
      t.gpr .x5 = off B (slot w o) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.gpr .x16 = off B (slot w Public.aAcc) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = false ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc (sa a ha), hdr_enc (sa b hb), hdr_enc (sa _ hmo), hdr_enc (sa _ hacc),
      hdr_enc (sa _ htmp), hdr_enc (sa o ho), hdr_enc (show sW < 32 by decide), hl _ (sa a ha), hl _ (sa b hb),
      hl _ (sa _ hmo), hl _ (sa _ hacc), hl _ (sa _ htmp), hl _ (sa o ho), hl sW (by decide), hH.harr a ha,
      hH.harr b hb, hH.harr _ hmo, hH.harr _ hacc, hH.harr _ htmp, hH.harr o ho, hH.hw])
    rfl rfl rfl)
    fun s₁ ⟨⟨h9, h17, h10, h8, h6, h5, h12, h7, h16, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have h0' : AddInv s₁ B Z (slot w Public.aAcc) (slot w a) (slot w b) 0 s₁ :=
    ⟨hs₁, Keep.refl _ _, by rw [h9]; rfl, by rw [h17]; rfl, by rw [h16]; rfl, Outside.refl _ _ _ _,
      by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega)
    (AddInv s₁ B Z (slot w Public.aAcc) (slot w a) (slot w b))
    (fun j hj t hI _ => addStep_ok (by have := sl _ hacc; omega) (by have := sl a ha; omega)
      (by have := sl b hb; omega) (by have := arr_sep (w := w) d3; omega) (by have := arr_sep (w := w) d4; omega)
      hj hI) h0' h14) fun s₂ hI => ?_)
  have hval := hI.val
  have s₂7 : s₂.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (slot w Public.aAcc + 8 * w)) (BitVec.ofNat 64 s₂.c.toNat))
    (by brun [hI.x16, s₂7, hI.scr.st (show slot w Public.aAcc + 8 * w + 8 ≤ Z by have := sl _ hacc; omega)]
        simp only [add_zero64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨hm₃, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.wr
  have k13 := (hI.keep.trans k₃)
  have o3 : Outside B (slot w Public.aAcc) (8 * (w + 1)) s₁.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [writeW_outside s₂.mem B _ (by have := sl _ hacc; omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₁] at o3 hval
  have fN : wv s₃.mem B (slot w Public.aN) w = wv s.mem B (slot w Public.aN) w :=
    o3.wv (by have := arr_sep (w := w) d5; omega) (by have := sl _ hmo; omega)
  have hTl : wv s₃.mem B (slot w Public.aAcc) w = wv s₂.mem B (slot w Public.aAcc) w := by
    rw [hm₃]; exact (writeW_outside s₂.mem B _ (by have := sl _ hacc; omega)).wv (Or.inl (by omega))
      (by have := sl _ hacc; omega)
  have hTw : (word s₃.mem B (slot w Public.aAcc + 8 * w)).toNat = s₂.c.toNat := by
    rw [hm₃, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le s₂.c; omega)]
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr .x8 (by decide)).trans h8) ((k13.gpr .x10 (by decide)).trans h10)
    ((k13.gpr .x6 (by decide)).trans h6) ((k13.gpr .x12 (by decide)).trans h12)
    ((k13.gpr .x7 (by decide)).trans h7) (by omega) hw' (by have := sl _ hacc; omega)
    (by have := sl _ hmo; omega) (by have := sl _ htmp; omega) (by have := arr_sep (w := w) d6; omega)
    (by have := arr_sep (w := w) d7; omega)) fun s₄ ⟨c', hc₄, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.wr
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr .x8 (by decide)).trans h8) ((k14.gpr .x6 (by decide)).trans h6)
    ((k14.gpr .x5 (by decide)).trans h5) ((k14.gpr .x12 (by decide)).trans h12) hc₄ (by omega) hw'
    (by have := sl _ hacc; omega) (by have := sl _ htmp; omega) (by have := sl o ho; omega)
    (by have := arr_sep (w := w) (Ne.symm d1); omega) (by have := arr_sep (w := w) d2; omega))
    fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B (slot w Public.aAcc) w = wv s₃.mem B (slot w Public.aAcc) w :=
    ho₄.wv (by have := arr_sep (w := w) d6; omega) (by have := sl _ hacc; omega)
  rw [fN] at hD
  have hN0 : 0 < wv s.mem B (slot w Public.aN) w := by omega
  refine ⟨?_, ?_, ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · rw [hv', hacc₄, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w Public.aAcc) w) (Tw := s₂.c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B (slot w Public.aTmp) w) (m := wv s.mem B (slot w Public.aN) w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B (slot w Public.aN) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : s₂.c.toNat < c'.toNat <;> simp [h, hTl]
  · have a3 : Arrays B w [Public.aAcc, Public.aTmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := Public.aAcc) (by simp) o3 (Nat.le_refl _) (by omega)
    have a4 : Arrays B w [Public.aAcc, Public.aTmp, o] s₃.mem s₄.mem :=
      Arrays.of_outside (j := Public.aTmp) (by simp) ho₄ (Nat.le_refl _) (by omega)
    have a5 : Arrays B w [Public.aAcc, Public.aTmp, o] s₄.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a4).trans a5

/-! ## Subtraction -/

theorem and_mask (a : BitVec 64) (c : Bool) : (a &&& mask c).toNat = if c then a.toNat else 0 := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]

/-- After `j` words of the second loop of `subModArr`:
`O_j + 2^(64 j) C = (c ? m_j : 0) + A_j` for the carry flag `C`. -/
structure MaInv (s₀ : State) (B : Addr) (Z eo eN eA : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x8, .x10, .x14] s₀ t
  x10 : t.gpr .x10 = off B (eN + 8 * j)
  x8 : t.gpr .x8 = off B (eA + 8 * j)
  x5 : t.gpr .x5 = off B (eo + 8 * j)
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j + 2 ^ (64 * j) * t.c.toNat = (if c then wv s₀.mem B eN j else 0) + wv s₀.mem B eA j

theorem maStep_ok {s₀ : State} {B : Addr} {Z w eo eN eA : Nat} {c : Bool} (h15 : s₀.gpr .x15 = mask c)
    (ho : eo + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z)
    (sN : eN + 8 * w ≤ eo ∨ eo + 8 * w ≤ eN) (sA : eA + 8 * w ≤ eo ∨ eo + 8 * w ≤ eA)
    {j : Nat} (hj : j < w) {t : State} (hI : MaInv s₀ B Z eo eN eA c j t) :
    WP isa (.block ([ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5,
        next .x10, next .x8, next .x5] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MaInv s₀ B Z eo eN eA c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x8, .x10] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) ((word t.mem B (eN + 8 * j) &&& mask c) +
        word t.mem B (eA + 8 * j) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eN + 8 * j) &&& mask c).toNat + (word t.mem B (eA + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x10 = off B (eN + 8 * j + 8) ∧ t₁.gpr .x8 = off B (eA + 8 * j + 8) ∧
      t₁.gpr .x5 = off B (eo + 8 * j + 8))
    (by brun [hI.x10, hI.x8, hI.x5, t15, hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h10, h8, h5⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x10 (by decide), h10, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x5 (by decide), h5, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := adcs_toNat (word t.mem B (eN + 8 * j) &&& mask c) (word t.mem B (eA + 8 * j)) t.c
    rw [hx, hy, and_mask] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy, and_mask]
    cases c
    · simp only [ite_false, Bool.false_eq_true] at hs hval ⊢
      grind
    · simp only [ite_true] at hs hval ⊢
      grind

/-- `[o] := [a] - [b] mod m`, for `[a], [b] < m = [aN]`. -/
theorem subModArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aN) (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w Public.aN) w)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w Public.aN) w) :
    WP isa (seqs (subModArr o a b)) s fun t =>
      wv t.mem B (slot w o) w = (wv s.mem B (slot w a) w + wv s.mem B (slot w Public.aN) w -
        wv s.mem B (slot w b) w) % wv s.mem B (slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  have hacc : Public.aAcc < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  have d5 : Public.aAcc ≠ Public.aN := by decide
  unfold subModArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x12, .x13, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧ t.gpr .x13 = off B (slot w Public.aAcc) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧
      t.mem = s.mem)
    (by brun [h0, hdr_enc (sa a ha), hdr_enc (sa b hb), hdr_enc (sa _ hacc), hdr_enc (show sW < 32 by decide),
      hl _ (sa a ha), hl _ (sa b hb), hl _ (sa _ hacc), hl sW (by decide), hH.harr a ha, hH.harr b hb,
      hH.harr _ hacc, hH.hw])
    rfl rfl rfl)
    fun s₁ ⟨⟨h16, h17, h13, h12, h7, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have h0' : SubInv s₁ B Z (slot w a) (slot w b) (slot w Public.aAcc) 0 s₁ :=
    ⟨hs₁, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl, Outside.refl _ _ _ _,
      by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega)
    (SubInv s₁ B Z (slot w a) (slot w b) (slot w Public.aAcc))
    (fun j hj t hI _ => subStep_ok (by have := sl a ha; omega) (by have := sl b hb; omega)
      (by have := sl _ hacc; omega) (by have := arr_sep (w := w) d3; omega)
      (by have := arr_sep (w := w) d4; omega) hj hI) h0' h14) fun s₂ hI => ?_)
  have hval := hI.val
  rw [hm₁] at hval
  have k12 := k₁.trans hI.keep
  have s₂0 : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h0
  have s₂7 : s₂.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have s₂12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (hI.keep.gpr .x12 (by decide)).trans h12
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have fh : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [hI.out.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega)) (by
      have := hdr_lt_slot w 8 hi; omega), hm₁]
  -- The mask of the borrow, and the bases.
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x5, .x8, .x10, .x14, .x15] (Q := fun t =>
      t.gpr .x15 = mask (!s₂.c) ∧ t.gpr .x10 = off B (slot w Public.aN) ∧
      t.gpr .x8 = off B (slot w Public.aAcc) ∧ t.gpr .x5 = off B (slot w o) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.c = false ∧ t.mem = s₂.mem)
    (by brun [borrowMask, s₂0, s₂7, s₂12, csel_mask_not, hdr_enc (sa _ hmo), hdr_enc (sa _ hacc), hdr_enc (sa o ho),
      hl₂ _ (sa _ hmo), hl₂ _ (sa _ hacc), hl₂ _ (sa o ho), (fh _ (sa _ hmo)).trans (hH.harr _ hmo),
      (fh _ (sa _ hacc)).trans (hH.harr _ hacc), (fh _ (sa o ho)).trans (hH.harr o ho)])
    rfl rfl rfl)
    fun s₃ ⟨⟨h15, h10₃, h8₃, h5₃, h14₃, hc₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.wr
  have k13 := k12.trans k₃
  have h0'' : MaInv s₃ B Z (slot w o) (slot w Public.aN) (slot w Public.aAcc) (!s₂.c) 0 s₃ :=
    ⟨hs₃, Keep.refl _ _, by rw [h10₃]; rfl, by rw [h8₃]; rfl, by rw [h5₃]; rfl, Outside.refl _ _ _ _,
      by rw [hc₃]; cases s₂.c <;> rfl⟩
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega)
    (MaInv s₃ B Z (slot w o) (slot w Public.aN) (slot w Public.aAcc) (!s₂.c))
    (fun j hj t hI _ => maStep_ok h15 (by have := sl o ho; omega) (by have := sl _ hmo; omega)
      (by have := sl _ hacc; omega) (by have := arr_sep (w := w) (Ne.symm d2); omega)
      (by have := arr_sep (w := w) (Ne.symm d1); omega) hj hI) h0'' h14₃) fun t hI' => ?_
  have hv := hI'.val
  have oA : Outside B (slot w Public.aAcc) (8 * w) s.mem s₃.mem := by rw [hm₃, ← hm₁]; exact hI.out
  have fN : wv s₃.mem B (slot w Public.aN) w = wv s.mem B (slot w Public.aN) w :=
    oA.wv (by have := arr_sep (w := w) d5; omega) (by have := sl _ hmo; omega)
  have fA : wv s₃.mem B (slot w Public.aAcc) w = wv s₂.mem B (slot w Public.aAcc) w := by rw [hm₃]
  rw [fN, fA] at hv
  have hN := wv_lt s.mem B (slot w Public.aN) w
  have hR := wv_lt t.mem B (slot w o) w
  have hAc := wv_lt s₂.mem B (slot w Public.aAcc) w
  refine ⟨?_, ?_, ((k13.trans hI'.keep)).mono (by decide)⟩
  · generalize wv s₂.mem B (slot w Public.aAcc) w = D at *
    generalize wv s.mem B (slot w Public.aN) w = N at *
    generalize wv s.mem B (slot w a) w = x at *
    generalize wv s.mem B (slot w b) w = y at *
    generalize wv t.mem B (slot w o) w = r at *
    generalize (2 : Nat) ^ (64 * w) = R at *
    have hc2 := Bool.toNat_le t.c
    cases hcs : s₂.c <;> cases hct : t.c <;> simp only [hcs, hct, Bool.not_false, Bool.not_true, ite_true,
      ite_false, Bool.false_eq_true, Bool.toNat_true, Bool.toNat_false] at hv hval ⊢
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by omega)]; omega)
      | (rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
  · have a1 : Arrays B w [Public.aAcc, o] s.mem s₃.mem :=
      Arrays.of_outside (j := Public.aAcc) (by simp) oA (Nat.le_refl _) (by omega)
    have a2 : Arrays B w [Public.aAcc, o] s₃.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hI'.out (Nat.le_refl _) (by omega)
    exact a1.trans a2

end VG.Proof.Bignum.AArch64
