module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH on x86-64: comparisons over all words -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (copyArr)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev bit (p : Prop) [Decidable p] : BitVec 64 := if p then 1 else 0

/-- Load only public addresses and the public loop count. -/
theorem ptrs_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (.block (ptrs a b)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w a) ∧
      t.gpr .r10 = off B (slot w b) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.r12, .rbx, .r10, .rbp] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w a) ∧
      t.gpr .r10 = off B (slot w b) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem)
    (by unfold ptrs; xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide),
      hl (sArr a) (by unfold sArr; omega_arith), hl (sArr b) (by unfold sArr; omega_arith),
      hg.hdr.hw, hg.hdr.harr a ha, hg.hdr.harr b hb, mask]) rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩

/-- The borrow mask of the complete multiword subtraction. -/
theorem cmpArr_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (cmpArr a b)) s fun t =>
      t.gpr .rbp = mask (decide (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w)) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sb := Nat.le_trans (slot_le (w := w) hb) hZ
  unfold cmpArr
  simp only [seqs]
  refine WP.seq (WP.mono (ptrs_ok hg hZ ha hb) fun s₁ ⟨h12, hbx, h10, hbp, hm, k₁⟩ => ?_)
  refine WP.mono (cmpLoop_ok (hg.scr.congr k₁.2.2) hbx h10 h12 hbp hw hw' (by omega_arith) (by omega_arith))
    fun t ⟨hbp', hm', k'⟩ => ⟨by rw [hbp', hm], hm'.trans hm, (k₁.trans k').mono (by decide)⟩

private theorem mask_and_one (b : Bool) : mask b &&& (1 : BitVec 64) = (if b then 1 else 0) := by
  cases b <;> rfl

/-- A less-than comparison produces a Boolean without a branch. -/
theorem ltArr_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (ltArr a b)) s fun t =>
      t.gpr .rax = bit (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  unfold ltArr
  refine wp_seqs_append (by simp [cmpArr]) (by simp)
    (WP.mono (cmpArr_ok hg hZ hw hw' ha hb) fun s₁ ⟨hbp, hm, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = s₁.gpr .rbp &&& 1 ∧ t.mem = s₁.mem)
    (by xrun) rfl) fun t ⟨⟨hax, hm'⟩, k'⟩ => ⟨?_, hm'.trans hm, (k₁.trans k').mono (by decide)⟩
  rw [hax, hbp, mask_and_one]
  by_cases h : wv s.mem B (slot w a) w < wv s.mem B (slot w b) w <;> simp [bit, h]

/-- The complement of the borrow bit. -/
theorem geArr_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (geArr a b)) s fun t =>
      t.gpr .rax = bit (¬ wv s.mem B (slot w a) w < wv s.mem B (slot w b) w) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  unfold geArr
  refine wp_seqs_append (by simp [cmpArr]) (by simp)
    (WP.mono (cmpArr_ok hg hZ hw hw' ha hb) fun s₁ ⟨hbp, hm, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = (s₁.gpr .rbp &&& 1) ^^^ 1 ∧ t.mem = s₁.mem)
    (by xrun) rfl) fun t ⟨⟨hax, hm'⟩, k'⟩ => ⟨?_, hm'.trans hm, (k₁.trans k').mono (by decide)⟩
  rw [hax, hbp, mask_and_one]
  by_cases h : wv s.mem B (slot w a) w < wv s.mem B (slot w b) w <;> simp [bit, h]

theorem or1_toNat (x : BitVec 64) : (x ||| 1).toNat = x.toNat + (1 - x.toNat % 2) := by
  rw [BitVec.toNat_or, show (1 : BitVec 64).toNat = 1 from rfl]
  have h1 : (x.toNat ||| 1) / 2 = x.toNat / 2 := by
    have := Nat.or_div_two_pow (a := x.toNat) (b := 1) (n := 1); simpa using this
  have h2 : (x.toNat ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega_arith

/-- Equality examines all words; only the final Boolean depends on them. -/
theorem eqArr_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (eqArr a b)) s fun t =>
      t.gpr .rax = bit (wv s.mem B (slot w a) w = wv s.mem B (slot w b) w) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sb := Nat.le_trans (slot_le (w := w) hb) hZ
  unfold eqArr
  simp only [seqs]
  refine WP.seq (WP.mono (ptrs_ok hg hZ ha hb) fun s₁ ⟨h12, hbx, h10, hbp, hm₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      OrInv s₁ B Z (fun j => ∀ i < j, word s₁.mem B (slot w a + 8 * i) = word s₁.mem B (slot w b + 8 * i)) 0 t :=
    fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw' _ h0
    (fun j _ hj t hI => xorStep_ok hbx h10 h12 (by omega_arith) (by omega_arith) (by omega_arith) hj hI)) fun s₂ hI => ?_)
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      t.gpr .rax = mask (decide (s₂.gpr .rbp = 0)) &&& 1 ∧ t.mem = s₂.mem)
    (by xrun [decide_lt_one]; rfl) rfl) fun t ⟨⟨hax, hm'⟩, k'⟩ => ⟨?_, by rw [hm', hI.mem, hm₁],
      ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  have heq : s₂.gpr .rbp = 0 ↔ wv s.mem B (slot w a) w = wv s.mem B (slot w b) w := by
    rw [hI.val, hm₁]
    exact ⟨fun h => wv_congr2 h, fun h => wv_inj w h⟩
  rw [hax, mask_and_one]
  by_cases h : wv s.mem B (slot w a) w = wv s.mem B (slot w b) w
  · simp [bit, h, heq.mpr h]
  · have hz : s₂.gpr .rbp ≠ 0 := fun hz => h (heq.mp hz)
    simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte, bit, h]

/-- Preserve the Montgomery header after a change past it. -/
theorem _root_.VG.Proof.Bignum.X86_64.Good.of_outside {s t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64}
    (hg : Good s G Zx w mi) {o n : Nat} (ho : 8 * 16 ≤ o) (hout : Outside G o n s.mem t.mem)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : Good t G Zx w mi := by
  have hn := hg.scr.nowrap
  have hh : ∀ i < 16, word t.mem G (8 * i) = word s.mem G (8 * i) := fun i hi =>
    hout.word (Or.inl (by omega_arith)) (by omega_arith)
  exact ⟨hg.scr.congr hwr, hdi.trans hg.rdi, ⟨(hh _ (by decide)).trans hg.hdr.hw,
    (hh _ (by decide)).trans hg.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hg.hdr.harr j hj)⟩⟩

/-- `ltP a` (`a ≠ aTmp`): `rax := 2 ⌊[a] / 2⌋ + 1 < m`; only the temporary array
changes. -/
theorem ltP_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) :
    WP isa (seqs (ltP a)) t fun t' =>
      t'.gpr .rax = bit (2 * (wv t.mem G (slot w a) w / 2) + 1 < wv t.mem G (slot w aN) w) ∧
      Outside G (slot w aTmp) (8 * w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  have sN := slot_sep (w := w) (show aN ≠ aTmp by decide)
  have sa := slot_sep (w := w) haT
  have sa8 := Nat.le_trans (slot_le (w := w) ha) hZ
  unfold ltP
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hg hZ hw hw' (show aTmp < 8 by decide) ha
    (Ne.symm haT)) fun t₁ ⟨hv₁, ho₁, k₁⟩ => ?_)
  have hT0 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have hg₁ : Good t₁ G Zx w mi := hg.of_outside (by omega_arith) ho₁ k₁.2.2 (k₁.gpr (by decide))
  simp only [List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (WP.keep [.rbx] (Q := fun t' => t'.gpr .rbx = off G (slot w aTmp) ∧ t'.mem = t₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (show 8 * sArr aTmp + 8 ≤ Zx by have := hdr_lt_slot w 8 (show sArr aTmp < 32 by decide); omega_arith),
      hg₁.hdr.harr aTmp (by decide)]) rfl) fun t₂ ⟨⟨h16, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hg.scr.congr (k₁.trans k₂).2.2
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off G (slot w aTmp))
      (word t₂.mem G (slot w aTmp) ||| 1))
    (by xrun [State.ea, at0, h16, show off G (slot w aTmp) + BitVec.ofInt 64 0 = off G (slot w aTmp) from by simp, hs₂.ld (show slot w aTmp + 8 ≤ Zx by omega_arith), hs₂.st (show slot w aTmp + 8 ≤ Zx by omega_arith)])
    rfl) fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have o₃ := writeW_outside t₂.mem G (d := slot w aTmp) (word t₂.mem G (slot w aTmp) ||| 1) (by omega_arith)
  rw [← hm₃] at o₃
  have K := (k₁.trans k₂).trans k₃
  have hg₃ : Good t₃ G Zx w mi := hg₁.of_outside (o := slot w aTmp) (n := 8) (by omega_arith)
    (by rw [hm₂] at o₃; exact o₃) (by rw [k₃.2.2, k₂.2.2]) (by rw [k₃.gpr (by decide), k₂.gpr (by decide)])
  refine WP.mono (ltArr_ok hg₃ hZ hw hw' (show aTmp < 8 by decide) (show aN < 8 by decide)) fun t' ⟨h9, hm', k'⟩ => ?_
  -- The temporary array is `[a]` with its low bit set.
  have hT : wv t₃.mem G (slot w aTmp) w = 2 * (wv t.mem G (slot w a) w / 2) + 1 := by
    have e₁ := wv_split t₃.mem G (slot w aTmp) (n := 1) (k := w - 1) (show 1 + (w - 1) = w by omega_arith)
    have e₂ := wv_split t₁.mem G (slot w aTmp) (n := 1) (k := w - 1) (show 1 + (w - 1) = w by omega_arith)
    have hh : wv t₃.mem G (slot w aTmp + 8 * 1) (w - 1) = wv t₁.mem G (slot w aTmp + 8 * 1) (w - 1) := by
      rw [o₃.wv (Or.inr (by omega_arith)) (by omega_arith), hm₂]
    have hl₃ : wv t₃.mem G (slot w aTmp) 1 = (word t₁.mem G (slot w aTmp)).toNat + (1 - (word t₁.mem G (slot w aTmp)).toNat % 2) := by
      simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
      rw [hm₃, word_writeW_self, hm₂, or1_toNat]
    have hl₁ : wv t₁.mem G (slot w aTmp) 1 = (word t₁.mem G (slot w aTmp)).toNat := by
      simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    rw [e₁, hh, hl₃, ← hv₁, e₂, hl₁]
    have h64 : 2 ^ (64 * 1) = 2 * 2 ^ 63 := by decide
    rw [h64, Nat.mul_assoc]
    generalize 2 ^ 63 * wv t₁.mem G (slot w aTmp + 8 * 1) (w - 1) = M
    generalize (word t₁.mem G (slot w aTmp)).toNat = x
    omega_arith
  have hN : wv t₃.mem G (slot w aN) w = wv t.mem G (slot w aN) w := by
    have sN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
    rw [o₃.wv (by omega_arith) (by omega_arith), hm₂, ho₁.wv (by omega_arith) (by omega_arith)]
  refine ⟨by rw [h9, hT, hN], ?_, (K.trans k').mono (by decide)⟩
  intro x hx
  rw [hm', o₃ x (by omega_arith), hm₂, ho₁ x hx]

/-- The low bit of the complete multiword value. -/
theorem isOdd_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) {a : Nat} (ha : a < 8) :
    WP isa (seqs (isOdd a)) s fun t =>
      t.gpr .rax = bit (wv s.mem B (slot w a) w % 2 = 1) ∧ t.mem = s.mem ∧ Keep [.rax, .rbx] s t := by
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have hH := hdr_lt_slot w 8 (show sArr a < 32 by unfold sArr; omega_arith)
  unfold isOdd
  simp only [seqs]
  refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t =>
      t.gpr .rax = word s.mem B (slot w a) &&& 1 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sArr a) (by omega_arith), hg.hdr.harr a ha,
      show off B (slot w a) + BitVec.ofInt 64 0 = off B (slot w a) from by simp,
      hg.scr.ld (show slot w a + 8 ≤ Z by omega_arith)]) rfl) fun t ⟨⟨hax, hm⟩, k⟩ => ⟨?_, hm, k⟩
  rw [hax]
  have e : (word s.mem B (slot w a)).toNat % 2 = wv s.mem B (slot w a) w % 2 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, e]
  by_cases h : wv s.mem B (slot w a) w % 2 = 1
  · simp [bit, h]
  · have : wv s.mem B (slot w a) w % 2 = 0 := by omega_arith
    simp [bit, this]

/-- `range a` (`a ≠ aTmp`, with the number 1 in `aOne`): `rax` and the slot
`sF` hold `1 < [a] < m − 1`, as `1 < [a]` and `2 ⌊[a] / 2⌋ + 1 < m`. -/
theorem range_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8) (haT : a ≠ aTmp)
    (hone : wv t.mem G (slot w aOne) w = 1) :
    WP isa (seqs (range a)) t fun t' =>
      t'.gpr .rax = bit (1 < wv t.mem G (slot w a) w ∧
        2 * (wv t.mem G (slot w a) w / 2) + 1 < wv t.mem G (slot w aN) w) ∧
      word t'.mem G (8 * sF) = t'.gpr .rax ∧
      Frm G [(slot w aTmp, 8 * w), (8 * sF, 8)] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  have hT0 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have hF := hdr_lt_slot w 0 (show sF < 32 by decide)
  have hFa := hdr_lt_slot w a (show sF < 32 by decide)
  have hFN := hdr_lt_slot w aN (show sF < 32 by decide)
  have hFT := hdr_lt_slot w aTmp (show sF < 32 by decide)
  have h8 := hdr_lt_slot w 8 (show sF < 32 by decide)
  have eF : sF = 30 := rfl
  have sa := Nat.le_trans (slot_le (w := w) ha) hZ
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sTa := slot_sep (w := w) haT
  have sTN := slot_sep (w := w) (show aN ≠ aTmp by decide)
  have sO := slot_le (w := w) (show aOne < 8 by decide)
  unfold range gt1
  rw [List.append_assoc, List.append_assoc]
  refine wp_seqs_append (by simp [ltArr, cmpArr]) (by simp) (WP.mono (ltArr_ok hg hZ hw hw' (show aOne < 8 by decide) ha)
    fun t₁ ⟨h9₁, hm₁, k₁⟩ => ?_)
  rw [hone] at h9₁
  have hg₁ : Good t₁ G Zx w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine wp_seqs_append (by simp) (by simp [ltP, copyArr]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₁.mem.writeW (off G (8 * sF)) (t₁.gpr .rax))
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith)])
    rfl) fun t₂ ⟨hm₂, k₂⟩ => ?_
  have o₂ := writeW_outside t₁.mem G (d := 8 * sF) (t₁.gpr .rax) (by omega_arith)
  rw [← hm₂] at o₂
  have hg₂ : Good t₂ G Zx w mi := hg₁.of_outside (o := 8 * sF) (n := 8) (by omega_arith) o₂ k₂.2.2
    (k₂.gpr (by decide))
  refine wp_seqs_append (by simp [ltP, copyArr]) (by simp) (WP.mono (ltP_ok hg₂ hZ hw hw' ha haT)
    fun t₃ ⟨h9₃, ho₃, k₃⟩ => ?_)
  have hA₂ : wv t₂.mem G (slot w a) w = wv t.mem G (slot w a) w := by
    rw [o₂.wv (by omega_arith) (by omega_arith), hm₁]
  have hN₂ : wv t₂.mem G (slot w aN) w = wv t.mem G (slot w aN) w := by
    rw [o₂.wv (by omega_arith) (by omega_arith), hm₁]
  rw [hA₂, hN₂] at h9₃
  have hg₃ : Good t₃ G Zx w mi := hg₂.of_outside (by omega_arith) ho₃ k₃.2.2 (k₃.gpr (by decide))
  have hF₃ : word t₃.mem G (8 * sF) = t₁.gpr .rax := by
    rw [ho₃.word (Or.inl (by omega_arith)) (by omega_arith), hm₂]; exact word_writeW_self _ _ _ _
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = t₃.gpr .rax &&& t₁.gpr .rax ∧
      t'.mem = t₃.mem.writeW (off G (8 * sF)) (t₃.gpr .rax &&& t₁.gpr .rax))
    (by unfold andF; xrun [State.ea, hdr, hg₃.rdi, hdrOff, hg₃.scr.ld (show 8 * sF + 8 ≤ Zx by omega_arith),
      hg₃.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith), hF₃])
    rfl) fun t' ⟨⟨h9, hm'⟩, k'⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [h9, h9₃, h9₁]
    by_cases h1 : 1 < wv t.mem G (slot w a) w <;>
      by_cases h2 : 2 * (wv t.mem G (slot w a) w / 2) + 1 < wv t.mem G (slot w aN) w <;> simp [bit, h1, h2]
  · rw [hm', h9]; exact word_writeW_self _ _ _ _
  · intro x hx
    have o' := writeW_outside t₃.mem G (d := 8 * sF) (t₃.gpr .rax &&& t₁.gpr .rax) (by omega_arith)
    rw [hm', o' x (hx (8 * sF, 8) (by simp)), ho₃ x (hx (slot w aTmp, 8 * w) (by simp)),
      o₂ x (hx (8 * sF, 8) (by simp)), hm₁]
  · exact (((k₁.trans k₂).trans k₃).trans k').mono (by decide)

end VG.Proof.Ffdh.X86_64
