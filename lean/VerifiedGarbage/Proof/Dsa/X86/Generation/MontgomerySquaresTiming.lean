module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryTiming
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySquares

/-! A fixed number of Montgomery squares may use different secret moduli. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def SquareReady (base : Addr) (sp : BitVec 32) (n m : Nat) (s : State) : Prop :=
  Context n m base montgomeryBytes s ∧ CallRoom (s.gpr .esp) base montgomeryBytes ∧
    s.gpr .esp = sp ∧ val32 s.mem base (slot n 4) (2 * n) < m

theorem SquareReady.input {base : Addr} {sp : BitVec 32} {n m : Nat} {s : State}
    (H : SquareReady base sp n m s) : MontgomeryInput base sp n 4 s := by
  have modulus : val32 s.mem base (slot n 0) (2 * n) = m := by
    rw [← wordsVal_eq_val32]; exact H.1.modulus.val
  exact ⟨H.1.scr, H.2.1, H.2.2.1, by rw [modulus]; exact H.1.inverse,
    by rw [modulus]; exact H.2.2.2⟩

theorem square_ready {base : Addr} {sp : BitVec 32} {n m : Nat} {s : State}
    (H : SquareReady base sp n m s) (hn : 0 < n) (hn' : n ≤ 48) :
    WP isa (montgomery n 4 4 4) s (SquareReady base sp n m) := by
  have input := H.input
  refine WP.mono (montgomery_ok input.scr input.room hn hn' (by decide) (by decide)
    (by decide) (by decide) input.inverse input.reduced) fun t ⟨cs, rd, wr, F, bound, _⟩ => ?_
  refine ⟨montgomery_context_keep H.1 H.2.1 hn hn' (by decide) (by decide) cs rd wr F,
    ?_, (cs .esp (by decide)).trans H.2.2.1, ?_⟩
  · rw [cs .esp (by decide)]; exact H.2.1
  · have modulus : val32 s.mem base (slot n 0) (2 * n) = m := by
      rw [← wordsVal_eq_val32]; exact H.1.modulus.val
    rwa [modulus] at bound

theorem montgomery_squares_ct {base : Addr} {sp : BitVec 32} {n m₁ m₂ : Nat}
    (count : Nat) (hn : 0 < n) (hn' : n ≤ 48) :
    RelCT isa (fun s t => SquareReady base sp n m₁ s ∧ SquareReady base sp n m₂ t)
      (montgomerySquares n count) (fun _ _ => True) := by
  induction count with
  | zero => exact VG.X86.RelCT.nil (fun _ _ _ => trivial)
  | succ count ih =>
    have step := (montgomery_ct hn hn' (show 4 < 9 by decide) (show 4 < 9 by decide)
      (show 4 < 9 by decide) (show 4 ≠ 0 by decide)).mono
      (fun _ _ (H : SquareReady base sp n m₁ _ ∧ SquareReady base sp n m₂ _) =>
        ⟨H.1.input, H.2.input⟩) (fun _ _ _ => trivial)
    have ready := step.wp (F₁ := SquareReady base sp n m₁) (F₂ := SquareReady base sp n m₂)
      (fun _ _ H => ⟨square_ready H.1 hn hn', square_ready H.2 hn hn'⟩)
    exact RelCT.seq ready (ih.mono (fun _ _ ⟨_, hs, ht⟩ => ⟨hs, ht⟩) (fun _ _ _ => trivial))

end VG.Proof.Dsa.X86.Generation
