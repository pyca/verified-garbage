module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowRun
public import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowRun
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of the validation reducer and its workspace adapter -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure Pub where
  B : Addr
  Z : Nat
  w : Nat

def Pre (p : Pub) (s : State) : Prop := ∃ minv, Good s p.B p.Z p.w minv ∧
  4 ≤ p.w ∧ p.w < 2 ^ 24 ∧ start p.w + span p.w ≤ p.Z

def Mid (p : Pub) (s : State) : Prop := Scr s p.B p.Z ∧
  VG.Proof.Rsa.X86_64.Ws s (off p.B (start p.w)) (span p.w) p.w ∧
  4 ≤ p.w ∧ p.w < 2 ^ 24 ∧ start p.w + span p.w ≤ p.Z

def enterVal (p : Pub) : Reg → BitVec 64
  | .rdi => p.B
  | .rsi => off p.B (slot p.w aAcc)
  | .r10 => off p.B (slot p.w CheckKey.aM)
  | .r12 => BitVec.ofNat 64 p.w
  | .r9 => BitVec.ofNat 64 (8 * (p.w + 2))
  | _ => 0

/-- Only the public header dimensions determine the source and destination addresses. -/
theorem inputs_ct : RelCT isa (Two Pre) WordValidation.inputs (Two Mid) := by
  unfold WordValidation.inputs
  change RelCT isa _ (.seq (.block WordValidation.enter) (.seq (.block setBases)
    (.seq (.block WordValidation.productSetup) (.seq copyWords (.seq (.block WordValidation.modulusSetup) copyWords))))) _
  unfold WordValidation.enter
  rw [List.append_assoc]
  apply VG.Proof.Rsa.X86_64.RelCT.block_seq
  refine VG.Proof.Rsa.X86_64.pin_ct [.rdi] [.rdi, .rsi, .r10, .r12, .r9] enterVal ?_ (by taint_decide) ?_
    (by taint_decide) ?_
  · rintro p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]
  · rintro p s ⟨_, h, hw, hw', hz⟩
    refine WP.mono (enterLoad_ok h hz) fun t ⟨⟨hsi, h10, h12, h9, _⟩, hk⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hk.gpr (by decide)).trans h.rdi
    · exact hsi
    · exact h10
    · exact h12
    · exact h9
  · rintro p s ⟨_, h, hw, hw', hz⟩
    apply VG.Proof.Rsa.X86_64.WP.block_seq_iff.mp
    exact WP.mono (inputs_ok h hz hw hw') fun t ⟨hws, _, _, _, hk⟩ =>
      ⟨h.scr.congr hk.2.2, hws, hw, hw', hz⟩

/-- Normalization is unconditional; no private factor controls a branch. -/
theorem fast_ct : RelCT isa (Two Mid) (.seq (.block WordDivide.normalize) WordDivide.code) (Two Mid) := by
  refine two_post (two_map (fun p : Pub =>
    (⟨off p.B (start p.w), span p.w, p.w, 0⟩ : VG.Proof.Rsa.X86_64.WordDivide.Pub))
    (fun _ _ h => ⟨h.2.1, Nat.le_refl _, h.2.2.1⟩) VG.Proof.Rsa.X86_64.WordDivide.fast_ct) ?_
  intro p s h
  exact WP.mono (VG.Proof.Rsa.X86_64.WordDivide.fast_ok h.2.1 (Nat.le_refl _) h.2.2.1)
    fun t ⟨_, hf, hk⟩ => ⟨h.1.congr hk.2.2,
      h.2.1.congr hf (fun _ hr => norm_mut hr) hk (by decide), h.2.2⟩

/-- Recovering the original base uses public arithmetic, then copies a public word count. -/
theorem result_ct : RelCT isa (Two Mid) (.seq (.block WordValidation.resultSetup) copyWords) fun _ _ => True := by
  unfold WordValidation.resultSetup
  simp only [List.append_assoc]
  refine (VG.Proof.Rsa.X86_64.ws_ct (Ψ := fun (_ : Pub) (_ : State) => True)
    (fun p => off p.B (start p.w)) (fun p => span p.w) Pub.w (fun _ _ h => h.2.1)
    (by taint_decide) ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p s h
  have hn := h.1.nowrap
  have hw := h.2.2.1
  have hw' := h.2.2.2.1
  have hz := h.2.2.2.2
  refine WP.seq (WP.mono (resultSetup_ok h.2.1) fun t ⟨_, hsi, hbx, h12, _, hk⟩ => ?_)
  refine WP.mono (copy_ok (w := p.w) (h.1.congr hk.2.2) hsi hbx h12
    (by omega_using [hw]) (by omega_using [hw']) ?_ ?_ (Or.inr ?_)) fun _ _ => trivial
  · simp only [start, span, slot, WordDivide.aR] at hz ⊢; omega_using [hz]
  · simp only [start, span, slot, CheckKey.aR] at hz ⊢; omega_using [hz]
  · simp only [start, slot, WordDivide.aR, CheckKey.aR]; omega_arith

theorem code_ct : RelCT isa (Two Pre) WordValidation.code fun _ _ => True := by
  unfold WordValidation.code
  exact RelCT.seq inputs_ct (RelCT.seq fast_ct result_ct)

end VG.Proof.Rsa.X86_64.WordValidation
