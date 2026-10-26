module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Correct
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.PublicState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.PrefixTiming
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
import Mathlib.Basic.IsEmpty.Defs

/-! The fast path and the selected general fallback preserve the API's timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

theorem Start.recognized_eq {a s : State} (h : Start a s) : recognized s = recognized a := by
  unfold recognized
  rw [h.regs .rdx (by decide), h.domain]

theorem After.base {a s : State} (h : After a s) : s.gpr .r9 = a.gpr .rcx := by
  obtain ⟨u, start, result⟩ := h
  exact result.context.baseReg.trans (start.regs .rcx (by decide))

theorem anchored_ct (v : RoundImpl) (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) (emittedCode v) (fun _ _ => True) := by
  let R := fun s : State => After a s ∧ s.zf = some (recognized a == 0)
  have scanWP (s : State) (h : Start a s) : WP isa recognizeCode s (After a) :=
    WP.mono (recognize_ok (geometry h.pre)) (fun t result => ⟨s, h, result⟩)
  have scanStage : RelCT isa (fun s t => Start a s ∧ Start a t) recognizeCode
      (fun s t => After a s ∧ After a t) := ((recognize_ct a).wp (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have testCT : RelCT isa (fun s t => After a s ∧ After a t)
      (.block [.alu .test .rax (.reg .rax)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  have testWP (s : State) (h : After a s) :
      WP isa (.block [.alu .test .rax (.reg .rax)]) s R := by
    obtain ⟨u, start, result⟩ := h
    refine WP.mono (test_result result) ?_
    rintro t ⟨resultT, zero⟩
    rw [start.recognized_eq] at zero
    exact ⟨⟨u, start, resultT⟩, zero⟩
  have testStage : RelCT isa (fun s t => After a s ∧ After a t)
      (.block [.alu .test .rax (.reg .rax)]) (fun s t => R s ∧ R t) := (testCT.wp (fun s t h => ⟨testWP s h.1, testWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have restoreCT : RelCT isa (fun s t => After a s ∧ After a t) (.block restore) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r9]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.base.trans h.2.base.symm
  have restoreWP (s : State) (h : After a s) : WP isa (.block restore) s (Ready a) := by
    obtain ⟨u, start, result⟩ := h
    exact WP.mono (restore_ok result) (fun t restored => ⟨u, start, restored⟩)
  have fallbackCT := (fallback_ct v).mono (P' := fun s t => Ready a s ∧ Ready a t)
    (fun _ _ h => ⟨h.1.pre, h.2.pre, Ready.public h.1 h.2⟩) (fun _ _ h => h)
  have fallbackStage := ((restoreCT.wp (fun s t h => ⟨restoreWP s h.1, restoreWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq fallbackCT
  have choice : RelCT isa (fun s t => R s ∧ R t)
      (.ite .ne (.block [.mov32 .rax (.imm 1)]) (.seq (.block restore) (CheckDomain.domainCode v)))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by simp only [eval, h.1.2, h.2.2])
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _
      exact Taint.agree_ofRegs (by simp)
    · exact fallbackStage.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  exact scanStage.seq (testStage.seq choice)

theorem constantTime (v : RoundImpl) : ConstantTime isa contract.pre contract.pub (emittedCode v) := by
  intro s t ts tt u w hs ht hp es et
  have left : Start s s := ⟨hs, fun _ _ => rfl, rfl, rfl⟩
  exact (anchored_ct v s s t ts tt u w ⟨left, start_of_pub ht hp⟩ es et).1

end VG.Proof.Ffdh.X86_64.VettedValidation
