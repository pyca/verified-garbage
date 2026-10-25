module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Correct
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.PublicState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.PrefixTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation

/-! The fast path and the selected general fallback preserve the API's timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

theorem Start.recognized_eq {a s : State} (h : Start a s) : recognized s = recognized a := by
  unfold recognized
  rw [h.args 2 (by decide), h.domain]

theorem anchored_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) code (fun _ _ => True) := by
  let R := fun s : State => After a s ∧ s.zf = some (recognized a == 0)
  have scanWP (s : State) (h : Start a s) : WP isa recognize s (After a) :=
    WP.mono (recognize_ok h.pre) (fun t result => ⟨s, h, result⟩)
  have scanStage : RelCT isa (fun s t => Start a s ∧ Start a t) recognize
      (fun s t => After a s ∧ After a t) := ((recognize_ct a).wp (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have testCT : RelCT isa (fun s t => After a s ∧ After a t)
      (.block [.alu .test .eax (.reg .eax)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) _ (by taint_decide)
    intro _ _ _
    exact agree_regs (by simp)
  have testWP (s : State) (h : After a s) :
      WP isa (.block [.alu .test .eax (.reg .eax)]) s R := by
    obtain ⟨u, start, result⟩ := h
    refine WP.mono (test_result result) ?_
    rintro t ⟨resultT, zero⟩
    rw [start.recognized_eq] at zero
    exact ⟨⟨u, start, resultT⟩, zero⟩
  have testStage : RelCT isa (fun s t => After a s ∧ After a t)
      (.block [.alu .test .eax (.reg .eax)]) (fun s t => R s ∧ R t) := (testCT.wp (fun s t h => ⟨testWP s h.1, testWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have fallbackCT := fallback_ct.mono (P' := fun s t => After a s ∧ After a t)
    (fun _ _ h => ⟨h.1.pre, h.2.pre, After.public h.1 h.2⟩) (fun _ _ h => h)
  have choice : RelCT isa (fun s t => R s ∧ R t)
      (.ite .ne (.block [.mov .eax (.imm 1)]) VG.Impl.Ffdh.X86.CheckDomain.code)
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
    · apply RelCT.taint (A := taint) (τr []) _ (by taint_decide)
      intro _ _ _
      exact agree_regs (by simp)
    · exact fallbackCT.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  exact scanStage.seq (testStage.seq choice)

theorem constantTime : ConstantTime isa contract.pre contract.pub code := by
  intro s t ts tt u w hs ht hp es et
  have left : Start s s := ⟨hs, rfl, fun _ _ => rfl, rfl, rfl⟩
  exact (anchored_ct s s t ts tt u w ⟨left, start_of_pub ht hp⟩ es et).1

end VG.Proof.Ffdh.X86.VettedValidation
