module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.FourSquares

/-! # Timing of the four squarings in each exponent window -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem square_headers_ready {σ s t : State} {base : Addr} {bytes w q : Nat}
    (facts : RoundFacts σ base bytes w) (h : BaseReady σ base bytes w s)
    (stage : Stage base bytes w σ t) (count : w32 t.mem base sQ = q)
    (threshold : w32 t.mem base sR < 2 ^ 31)
    (frame : Frame ([sR, sQ].map (fun d => ⟨off base d, 4⟩)) s.mem t.mem) :
    SquareReady σ base bytes w q t := by
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have bounds : ∀ d ∈ [sR, sQ], d + 4 ≤ bytes := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact Nat.le_trans (by decide) hdrFit
  have flagEq := headers_frame_word h.stage.context.ws.nowrap
    (Nat.le_trans (by decide : sF + 4 ≤ 256) hdrFit) bounds
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> decide : ∀ d ∈ [sR, sQ], sF + 4 ≤ d ∨ d + 4 ≤ sF) frame
  have valueEq := headers_frame_num h.stage.context.ws.nowrap facts.fit (by decide : 6 < 28)
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> decide : ∀ d ∈ [sR, sQ], d + 4 ≤ 256) frame
  refine ⟨⟨stage, by rw [valueEq]; exact h.reduced, ?_⟩, count, threshold⟩
  simpa only [w32, flagEq] using h.flag

theorem square_four_ready {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : BaseReady σ base bytes w s) :
    WP isa (.block sqFour) s (SquareReady σ base bytes w 4) := by
  refine WP.mono (square_four_init h.stage facts.fit) ?_
  rintro t ⟨stage, threshold, count, frame⟩
  exact square_headers_ready facts h stage count (by rw [threshold]; decide) frame

theorem four_squares_ready {σ s : State} {base : Addr} {bytes w k : Nat}
    (facts : RoundFacts σ base bytes w) (h : WindowReady σ base bytes w k s) :
    WP isa (.seq (.block sqFour) sqLoop) s (WindowReady σ base bytes w k) := by
  obtain ⟨F, flag⟩ := h.flag
  refine WP.mono (four_squares facts h.stage flag h.reduced) ?_
  rintro t ⟨stage, _, flagT, reduced, arrays, headers⟩
  refine ⟨⟨stage, reduced, ⟨_, flagT⟩⟩, ?_, ?_⟩
  · change (t.mem.readW (off base sK) 32).toNat = k
    rw [headers sK (.inr rfl)]
    exact h.count
  · intro i hi
    rw [arrays (11 + i) (by omega) (by omega) (by omega)]
    exact h.table i hi

theorem four_squares_ct {σ₁ σ₂ : State} {base : Addr} {bytes w k : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => WindowReady σ₁ base bytes w k s ∧ WindowReady σ₂ base bytes w k t)
      (.seq (.block sqFour) sqLoop)
      (fun s t => WindowReady σ₁ base bytes w k s ∧ WindowReady σ₂ base bytes w k t) := by
  have init := ((C.pieces square_four_cert).mono
    (P' := fun s t => WindowReady σ₁ base bytes w k s ∧ WindowReady σ₂ base bytes w k t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨h₁.stage, h₂.stage⟩) (fun _ _ _ => trivial)).wp
    (F₁ := SquareReady σ₁ base bytes w 4) (F₂ := SquareReady σ₂ base bytes w 4)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨square_four_ready C.facts₁ h₁.toBaseReady, square_four_ready C.facts₂ h₂.toBaseReady⟩)
  have core := init.seq ((square_loop_ct C (q0 := 4) (by decide)).mono
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ _ => trivial))
  exact (core.wp (fun _ _ ⟨h₁, h₂⟩ => ⟨four_squares_ready C.facts₁ h₁, four_squares_ready C.facts₂ h₂⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩)

end VG.Proof.MillerRabin.X86
