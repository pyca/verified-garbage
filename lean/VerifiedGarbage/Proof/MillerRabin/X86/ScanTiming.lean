module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingContext
public import VerifiedGarbage.Proof.MillerRabin.X86.Scan

/-! # Table selection visits every table entry independently of the digit -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem digit_exists (s : State) (base : Addr) :
    ∃ d : Nat, d < 16 ∧ s.mem.readW (off base sV) 32 >>> 28 = BitVec.ofNat 32 d := by
  let v := s.mem.readW (off base sV) 32
  refine ⟨(v >>> 28).toNat, ?_, ?_⟩
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := v.isLt
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (v >>> 28).isLt).symm

theorem scan_entry_stage {σ s : State} {base : Addr} {bytes w j : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s) (hj : j < 16) :
    WP isa (.seq (.block (maskJ j)) (select 5 (11 + j))) s (Stage base bytes w σ) := by
  obtain ⟨d, hd, digit⟩ := digit_exists s base
  refine WP.seq (WP.mono (mask_ok h facts.fit hd hj digit) ?_)
  rintro u ⟨mask, stage, _, _⟩
  exact WP.mono (stage.select facts.lower facts.upper facts.fit (by decide) (by omega)
    (by omega) (.inl rfl) facts.width mask) (fun _ ⟨_, ht, _, _⟩ => ht)

theorem scan_from_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    ∀ n j, j + n = 16 → 1 ≤ j →
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t)
      (scanFrom j n) (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) := by
  intro n
  induction n with
  | zero => intro j _ _; exact RelCT.nil (fun _ _ h => h)
  | succ n ih =>
    intro j total lo
    have hi : j < 16 := by omega
    have entry := (C.pieces (scan_entry_cert lo hi)).wp
      (fun _ _ ⟨h₁, h₂⟩ => ⟨scan_entry_stage C.facts₁ h₁ hi, scan_entry_stage C.facts₂ h₂ hi⟩)
    exact RelCT.assoc (entry.seq ((ih (j + 1) (by omega) (by omega)).mono
      (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ h => h)))

theorem scan_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t)
      scan (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) := by
  have initial := (C.pieces copy_scan_cert).wp (fun _ _ ⟨h₁, h₂⟩ =>
    ⟨WP.mono (h₁.copy C.facts₁.lower C.facts₁.upper C.facts₁.fit (by decide) (by decide)
        (by decide) (.inl rfl) C.facts₁.width) (fun _ ⟨_, ht, _, _⟩ => ht),
     WP.mono (h₂.copy C.facts₂.lower C.facts₂.upper C.facts₂.fit (by decide) (by decide)
        (by decide) (.inl rfl) C.facts₂.width) (fun _ ⟨_, ht, _, _⟩ => ht)⟩)
  exact initial.seq ((scan_from_ct C 15 1 rfl (by decide)).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ h => h))

structure SelectedReady (σ : State) (base : Addr) (bytes w k : Nat) (s : State) : Prop
    extends WindowReady σ base bytes w k s where
  selected : numAt s.mem base w 5 < val32 σ.mem base 256 (2 * w)

theorem scan_ready {σ s : State} {base : Addr} {bytes w k : Nat}
    (facts : RoundFacts σ base bytes w) (h : WindowReady σ base bytes w k s) :
    WP isa scan s (SelectedReady σ base bytes w k) := by
  obtain ⟨d, hd, digit⟩ := digit_exists s base
  refine WP.mono (scan_ok h.stage facts.lower facts.upper facts.fit hd facts.width
    (fun _ _ => rfl) digit) ?_
  rintro t ⟨value, stage, frame⟩
  have arrays (a : Nat) (ha : a < 28) (ne : a ≠ 5) :=
    array_frame_num h.stage.context.ws.nowrap facts.fit ha (by decide : 5 < 28) ne frame
  have headers (d : Nat) (hd : d + 4 ≤ 256) :=
    array_frame_header h.stage.context.ws.nowrap facts.fit (by decide : 5 < 28) hd frame
  refine ⟨⟨⟨stage, by rw [arrays 6 (by decide) (by decide)]; exact h.reduced, ?_⟩, ?_, ?_⟩, ?_⟩
  · simpa only [w32, headers sF (by decide)] using h.flag
  · simpa only [w32, headers sK (by decide)] using h.count
  · intro i hi
    rw [arrays (11 + i) (by omega) (by omega)]
    exact h.table i hi
  · rw [value]
    exact h.table d hd

end VG.Proof.MillerRabin.X86
