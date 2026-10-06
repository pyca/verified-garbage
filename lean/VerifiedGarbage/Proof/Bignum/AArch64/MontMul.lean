import VerifiedGarbage.Proof.Bignum.AArch64.Csub

/-!
# Multiword arithmetic on AArch64: Montgomery multiplication

The working space at `B` (`x0`) holds the header and, after it, eight
arrays of `w + 2` words (`slot w j`, `Proof/Bignum/Layout.lean`). The header
(`Hdr`) gives `w`, `-m⁻¹ mod 2⁶⁴` and the arrays' bases.
`montMul mo acc tmp o a b` leaves `[o] < m` with `[o] R ≡ [a] [b] (mod m)`
for `R = 2^(64 w)` and `m = [mo]` (`montMul_ok`), changing only the arrays
`acc`, `tmp` and `o`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A header slot's offset, for `ldr`. -/
theorem hdr_enc {i : Nat} (hi : i < 32) : 8 * i % 8 = 0 ∧ 8 * i < 32768 := ⟨Nat.mul_mod_right _ _, by omega⟩

/-- `bases o a b mo acc tmp`: the bases from the header, and `w`, `-m⁻¹` and 0. -/
theorem bases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b mo acc tmp : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) :
    WP isa (.block (bases o a b mo acc tmp)) s fun t =>
      (t.gpr .x8 = off B (slot w acc) ∧ t.gpr .x9 = off B (slot w b) ∧ t.gpr .x10 = off B (slot w mo) ∧
      t.gpr .x11 = off B (slot w a) ∧ t.gpr .x5 = off B (slot w o) ∧ t.gpr .x6 = off B (slot w tmp) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x15] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  refine WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x15] ?_ rfl rfl rfl
  unfold bases
  brun [h0, hdr_enc (sa acc hacc), hdr_enc (sa b hb), hdr_enc (sa mo hmo), hdr_enc (sa a ha),
    hdr_enc (sa o ho), hdr_enc (sa tmp htmp), hdr_enc (show sW < 32 by decide),
    hdr_enc (show sMinv < 32 by decide), hl _ (sa acc hacc), hl _ (sa b hb), hl _ (sa mo hmo),
    hl _ (sa a ha), hl _ (sa o ho), hl _ (sa tmp htmp), hl sW (by decide), hl sMinv (by decide),
    hH.harr acc hacc, hH.harr b hb, hH.harr mo hmo, hH.harr a ha, hH.harr o ho, hH.harr tmp htmp, hH.hw,
    hH.hminv]

/-- The registers `montMul` may change: all the caller-saved ones but `x0`. -/
def mmRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Montgomery multiplication: `[o] = [a] [b] R⁻¹ mod m` for `m = [mo]`, if
`[b] < m` and `-m⁻¹` is right. -/
theorem montMul_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d4 : acc ≠ a) (d5 : acc ≠ b)
    (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hinv : ((word s.mem B (slot w mo)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w mo) w) :
    WP isa (montMul mo acc tmp o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w mo) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w mo) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hN0 : 0 < wv s.mem B (slot w mo) w := by omega
  unfold montMul
  -- The bases.
  refine WP.seq (WP.mono (bases_ok hs h0 hH hZ ho ha hb hmo hacc htmp)
    fun s₁ ⟨⟨h8, h9, h10, h11, h5, h6, h12, h15, h7, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  -- The accumulator := 0.
  refine WP.seq (WP.mono (zeroAcc_ok hs₁ h8 h12 h7 hw' (sl acc hacc))
    fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have hs₂ := hs₁.congr k₂.wr
  have k12 := k₁.trans k₂
  have fr₂ : ∀ {j}, j < 8 → j ≠ acc → wv s₂.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun hj hne => ho₂.wv (by have := sp hne; omega) (by have := sl _ hj; omega)
  have fw₂ : word s₂.mem B (slot w mo) = word s.mem B (slot w mo) :=
    ho₂.word (by have := sp (Ne.symm d1); have := sl _ hmo; omega) (by have := sl _ hmo; omega)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok hs₂ ((k₂.gpr .x8 (by decide)).trans h8) ((k₂.gpr .x9 (by decide)).trans h9)
    ((k₂.gpr .x10 (by decide)).trans h10) ((k₂.gpr .x11 (by decide)).trans h11)
    ((k₂.gpr .x12 (by decide)).trans h12) ((k₂.gpr .x7 (by decide)).trans h7)
    hw hw' (sl acc hacc) (by have := sl b hb; omega) (by have := sl mo hmo; omega)
    (by have := sl a ha; omega) (by have := sp (Ne.symm d5); omega) (by have := sp (Ne.symm d1); omega)
    (by have := sp (Ne.symm d4); omega)
    (by rw [fw₂, (k₂.gpr .x15 (by decide) : s₂.gpr .x15 = s₁.gpr .x15), h15]; exact hinv) hz₂
    (by rw [fr₂ hb (Ne.symm d5), fr₂ hmo (Ne.symm d1)]; exact hB)) fun s₃ hR => ?_)
  have hTlt := hR.lt
  have hTc := hR.cong
  rw [fr₂ hmo (Ne.symm d1)] at hTlt hTc
  rw [fr₂ ha (Ne.symm d4), fr₂ hb (Ne.symm d5)] at hTc
  have hs₃ := hR.scr
  have fr₃ : ∀ {j}, j < 8 → j ≠ acc → wv s₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun hj hne =>
    (hR.out.wv (by have := sp hne; omega) (by have := sl _ hj; omega)).trans (fr₂ hj hne)
  have k14 := k₂.trans hR.keep
  -- `T - m`.
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k14.gpr .x8 (by decide)).trans h8)
    ((k14.gpr .x10 (by decide)).trans h10) ((k14.gpr .x6 (by decide)).trans h6)
    ((k14.gpr .x12 (by decide)).trans h12) ((k14.gpr .x7 (by decide)).trans h7) (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega)
    (by have := sp d2; omega) (by have := sp d6; omega)) fun s₅ ⟨c, hc₅, hD, ho₅, k₅⟩ => ?_)
  have k15 := k14.trans k₅
  -- The selection.
  have hs₅ := hs₃.congr k₅.wr
  refine WP.mono (selectAcc_ok hs₅ ((k15.gpr .x8 (by decide)).trans h8) ((k15.gpr .x6 (by decide)).trans h6)
    ((k15.gpr .x5 (by decide)).trans h5) ((k15.gpr .x12 (by decide)).trans h12) hc₅ (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv, hot, k₆⟩ => ?_
  -- The words of `T` in `s₅`, as after the rounds.
  have hacc₅ : wv s₅.mem B (slot w acc) w = wv s₃.mem B (slot w acc) w :=
    ho₅.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  have hD' : wv s₅.mem B (slot w tmp) w + wv s.mem B (slot w mo) w = wv s₃.mem B (slot w acc) w +
      2 ^ (64 * w) * c.toNat := by
    rw [← fr₃ hmo (Ne.symm d1)]; exact hD
  have hres : wv t.mem B (slot w o) w = wv s₃.mem B (slot w acc) (w + 2) % wv s.mem B (slot w mo) w := by
    rw [hv, hacc₅, wv_top2]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w acc) w)
      (Tw := (word s₃.mem B (slot w acc + 8 * w)).toNat)
      (Tw1 := (word s₃.mem B (slot w acc + 8 * w + 8)).toNat) (D := wv s₅.mem B (slot w tmp) w)
      (m := wv s.mem B (slot w mo) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w mo) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD'
    rw [← this]
    by_cases h : (word s₃.mem B (slot w acc + 8 * w)).toNat < c.toNat <;> simp [h]
  refine ⟨?_, ?_, ?_, ((k12.trans (hR.keep.trans k₅)).trans k₆).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hN0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, hTc]
  · have a3 : Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) (ho₂.trans hR.out) (Nat.le_refl _) (Nat.le_refl _)
    have a5 : Arrays B w [acc, tmp, o] s₃.mem s₅.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₅ (Nat.le_refl _) (by omega)
    have a6 : Arrays B w [acc, tmp, o] s₅.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a5).trans a6

end VG.Proof.Bignum.AArch64
