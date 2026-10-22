module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.WordTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.Arithmetic

/-! # Timing composition for the complete prepared arithmetic round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem RunState.window_ready {σ s : State} {base : Addr} {bytes w n : Nat}
    (facts : RoundFacts σ base bytes w) (h : RunState σ base bytes w n s) :
    WindowReady σ base bytes w (16 * w - n) s := by
  refine ⟨⟨h.stage, h.reduced, ⟨_, h.flag⟩⟩, h.count, ?_⟩
  intro i hi
  rw [h.table i hi]
  exact VG.Proof.MillerRabin.Math.tp_lt (by have := facts.odd; omega) facts.witness facts.one i

theorem window_init_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => TableState σ₁ base bytes w 14 s ∧ TableState σ₂ base bytes w 14 t) winInit
      (fun s t => RunState σ₁ base bytes w 0 s ∧ RunState σ₂ base bytes w 0 t) := by
  have minus := copy_stage_ct C (by decide) (by decide) (by decide) (.inr (.inr (.inl rfl))) copy_minus_cert
  have acc := copy_stage_ct C (by decide) (by decide) (by decide) (.inr (.inl rfl)) copy_start_cert
  have core : RelCT isa (fun s t => TableState σ₁ base bytes w 14 s ∧ TableState σ₂ base bytes w 14 t)
      winInit (fun _ _ => True) := by
    unfold winInit seqs
    simp only [List.foldr_cons, List.foldr_nil]
    exact (minus.mono (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ h => h)).seq
      (acc.seq ((C.pieces window_counters_cert).seq (RelCT.nil (fun _ _ _ => trivial))))
  exact (core.wp (F₁ := RunState σ₁ base bytes w 0) (F₂ := RunState σ₂ base bytes w 0)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨window_init C.facts₁ h₁, window_init C.facts₂ h₂⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩)

theorem low_bits_ready {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : BaseReady σ base bytes w s)
    (tail : σ.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ.mem base 256 (2 * w) - 1)).1 % 64)) :
    WP isa (.block lowBits) s (SquareReady σ base bytes w 3) := by
  refine WP.mono (low_bits facts h.stage) ?_
  rintro t ⟨stage, count, threshold, frame⟩
  have fold := tail_fold (Nat.mod_lt _ (by decide : 0 < 64)) tail
  rw [fold, VG.Proof.RsaKeyGen.sigOf_mod, BitVec.toNat_ofNat] at threshold
  exact square_headers_ready facts h stage count (by rw [threshold]; omega) frame

theorem final_squares_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len)
    (tail₁ : σ₁.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ₁.mem base 256 (2 * w) - 1)).1 % 64))
    (tail₂ : σ₂.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ₂.mem base 256 (2 * w) - 1)).1 % 64)) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w 0 s ∧ WindowReady σ₂ base bytes w 0 t)
      (.seq (.block lowBits) sqLoop) (fun _ _ => True) := by
  have lowCT := ((C.pieces low_bits_cert).mono
    (P' := fun s t => WindowReady σ₁ base bytes w 0 s ∧ WindowReady σ₂ base bytes w 0 t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ _ => trivial)).wp
    (F₁ := SquareReady σ₁ base bytes w 3) (F₂ := SquareReady σ₂ base bytes w 3)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨low_bits_ready C.facts₁ h₁.toBaseReady tail₁,
      low_bits_ready C.facts₂ h₂.toBaseReady tail₂⟩)
  exact lowCT.seq ((square_loop_ct C (q0 := 3) (by decide)).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial))

theorem arithmetic_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len)
    (h₁ : Stage base bytes w σ₁ σ₁) (h₂ : Stage base bytes w σ₂ σ₂)
    (tail₁ : σ₁.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ₁.mem base 256 (2 * w) - 1)).1 % 64))
    (tail₂ : σ₂.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ₂.mem base 256 (2 * w) - 1)).1 % 64)) :
    RelCT isa (fun s t => s = σ₁ ∧ t = σ₂) arithmetic
      (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) := by
  have start := ((table_init_ct C).mono (P' := fun s t => s = σ₁ ∧ t = σ₂)
    (fun s t ⟨hs, ht⟩ => by subst s; subst t; exact ⟨h₁, h₂⟩) (fun _ _ _ => trivial)).wp
    (F₁ := TableState σ₁ base bytes w 0) (F₂ := TableState σ₂ base bytes w 0)
    (fun s t ⟨hs, ht⟩ => by subst s; subst t; exact ⟨table_start C.facts₁ h₁, table_start C.facts₂ h₂⟩)
  have core : RelCT isa (fun s t => s = σ₁ ∧ t = σ₂) arithmetic (fun _ _ => True) :=
    start.seq (((table_loop_ct C).mono (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩) (fun _ _ h => h)).seq
      ((window_init_ct C).seq (((words_ct C).mono
        (fun _ _ ⟨a, b⟩ => ⟨a.window_ready C.facts₁, b.window_ready C.facts₂⟩)
        (fun _ _ h => h)).seq (final_squares_ct C tail₁ tail₂))))
  exact (core.wp (F₁ := fun (s : State) => Stage base bytes w σ₁ s ∧ w32 s.mem base sF = (finalFlag σ₁ base w).toNat)
    (F₂ := fun (s : State) => Stage base bytes w σ₂ s ∧ w32 s.mem base sF = (finalFlag σ₂ base w).toNat)
    (fun s t ⟨hs, ht⟩ => by subst s; subst t; exact ⟨arithmetic_ok C.facts₁ h₁ tail₁, arithmetic_ok C.facts₂ h₂ tail₂⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, ⟨a, _⟩, ⟨b, _⟩⟩ => ⟨a, b⟩)

end VG.Proof.MillerRabin.X86
