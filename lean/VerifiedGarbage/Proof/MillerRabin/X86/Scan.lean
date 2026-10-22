module

public import VerifiedGarbage.Proof.MillerRabin.X86.Mask
public import VerifiedGarbage.Proof.MillerRabin.X86.StageSelect
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.StageCopy

/-! # Select a secret digit through a scan of all public table entries -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

private theorem advance_selection {T : Nat → Nat} {d j : Nat} :
    (if d = j then T j else if d < j then T d else T 0) =
      (if d < j + 1 then T d else T 0) := by
  by_cases eq : d = j
  · subst j; simp
  · by_cases lt : d < j <;> simp [eq, lt, show d < j + 1 ↔ d < j by omega]

theorem scan_from {σ : State} {base : Addr} {bytes w d : Nat} {T : Nat → Nat}
    (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes) (hd : d < 16)
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    ∀ n j, j + n = 16 → 1 ≤ j → ∀ s,
      Stage base bytes w σ s →
      (∀ i, i < 16 → numAt s.mem base w (11 + i) = T i) →
      s.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d →
      numAt s.mem base w 5 = (if d < j then T d else T 0) →
      WP isa (scanFrom j n) s fun t =>
        numAt t.mem base w 5 = T d ∧ Stage base bytes w σ t ∧
        Frame [⟨off base (arrAt w 5), 8 * w⟩] s.mem t.mem := by
  intro n
  induction n with
  | zero =>
    intro j total _ s h table digit selected
    have jj : j = 16 := by omega
    exact WP.block_nil ⟨by simpa only [jj, hd, ite_true] using selected, h, Frame.refl _ _⟩
  | succ n ih =>
    intro j total lower s h table digit selected
    have upper : j < 16 := by omega
    rw [scanFrom]
    refine WP.seq (WP.mono (mask_ok h hf hd upper digit) ?_)
    rintro s₁ ⟨mask, h₁, m₁, _⟩
    refine WP.seq (WP.mono (h₁.select (o := 5) (a := 11 + j) hw hu hf (by decide) (by omega)
      (by omega) (.inl rfl) width mask) ?_)
    rintro s₂ ⟨value, h₂, outside, _⟩
    have fit := array_fits_bytes hf (show 5 < 28 by decide)
    have nw := h.context.ws.nowrap
    have frame₁ : Frame [⟨off base (arrAt w 5), 8 * w⟩] s₁.mem s₂.mem :=
      VG.Proof.Bignum.outside_frame outside (by omega)
    have frame : Frame [⟨off base (arrAt w 5), 8 * w⟩] s.mem s₂.mem := by rw [m₁] at frame₁; exact frame₁
    simp only [← candidate_words, decide_eq_true_eq] at value
    have selection : numAt s₂.mem base w 5 = (if d < j + 1 then T d else T 0) := by
      rw [m₁, table j upper, selected] at value
      exact value.trans advance_selection
    have table₂ : ∀ i, i < 16 → numAt s₂.mem base w (11 + i) = T i := by
      intro i hi
      exact (array_frame_num nw hf (by omega) (by decide) (by omega) frame).trans (table i hi)
    have digit₂ : s₂.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d := by
      rw [array_frame_header nw hf (by decide) (by decide : sV + 4 ≤ 256) frame, digit]
    refine WP.mono (ih (j + 1) (by omega) (by omega) s₂ h₂ table₂ digit₂ selection) ?_
    rintro t ⟨result, ht, rest⟩
    exact ⟨result, ht, frame.trans rest⟩

theorem scan_ok {σ s : State} {base : Addr} {bytes w d : Nat} {T : Nat → Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes) (hd : d < 16)
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (table : ∀ i, i < 16 → numAt s.mem base w (11 + i) = T i)
    (digit : s.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d) :
    WP isa scan s fun t => numAt t.mem base w 5 = T d ∧ Stage base bytes w σ t ∧
      Frame [⟨off base (arrAt w 5), 8 * w⟩] s.mem t.mem := by
  unfold scan
  refine WP.seq (WP.mono (h.copy (o := 5) (a := 11) hw hu hf (by decide) (by decide) (by decide)
    (.inl rfl) width) ?_)
  rintro u ⟨value, huStage, frame, _⟩
  have nw := h.context.ws.nowrap
  have tableU : ∀ i, i < 16 → numAt u.mem base w (11 + i) = T i := by
    intro i hi
    exact (array_frame_num nw hf (by omega) (by decide) (by omega) frame).trans (table i hi)
  have digitU : u.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d := by
    rw [array_frame_header nw hf (by decide) (by decide : sV + 4 ≤ 256) frame, digit]
  have selected : numAt u.mem base w 5 = (if d < 1 then T d else T 0) := by
    rw [table 0 (by decide)] at value
    by_cases zero : d = 0
    · simpa [zero] using value
    · simpa only [show ¬d < 1 by omega, ite_false] using value
  refine WP.mono (scan_from hw hu hf hd width 15 1 rfl (by decide) u huStage tableU digitU selected) ?_
  rintro t ⟨result, ht, rest⟩
  exact ⟨result, ht, frame.trans rest⟩

end VG.Proof.MillerRabin.X86
