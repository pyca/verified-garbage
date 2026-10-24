module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.PrefixTiming
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.RecordTiming
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation

/-! The success branch and complete fallback obey the original public-domain timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation

theorem Start.recognized_eq {a s : State} (h : Start a s) : recognized s = recognized a := by
  unfold recognized
  rw [h.regs .r5 (by decide), h.domain]

theorem After.value {a t : State} (h : After a t) : t.gpr .r8 = recognized a := by
  obtain ⟨s, start, result, _⟩ := h
  exact result.value.trans start.recognized_eq

theorem anchored_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) code (fun _ _ => True) := by
  have scanWP (s : State) (h : Start a s) : WP isa recognize s (After a) :=
    WP.mono (withSp (recognize_ok h.pre)) (fun t ⟨result, sp⟩ => ⟨s, h, result, sp⟩)
  have scanStage : RelCT isa (fun s t => Start a s ∧ Start a t) recognize
      (fun s t => After a s ∧ After a t) := ((recognize_ct a).wp
        (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono
          (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)
  have choice : RelCT isa (fun s t => After a s ∧ After a t)
      (.ite (.nonzero .d .r8) (.block [.li .r3 1]) VG.Impl.Ffdh.PPC64LE.Domain.checkDomain)
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by
      rw [VG.Proof.RsaPkcs1Sig.PPC64LE.eval_nonzero, VG.Proof.RsaPkcs1Sig.PPC64LE.eval_nonzero,
        h.1.value, h.2.value])
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t h
      exact ⟨h.1.1.sp.trans h.1.2.sp.symm, by simp [Taint.ofRegs]⟩
    · exact fallback_ct.mono (fun _ _ h => ⟨h.1.1.pre, h.1.2.pre, After.public h.1.1 h.1.2⟩)
        (fun _ _ h => h)
  exact scanStage.seq choice

theorem constantTime : ConstantTime isa contract.pre contract.pub code := by
  intro s t ts tt u w hs ht hp es et
  have left : Start s s := ⟨hs, fun _ _ => rfl, rfl, rfl, rfl⟩
  exact (anchored_ct s s t ts tt u w ⟨left, start_of_pub ht hp⟩ es et).1

end VG.Proof.Ffdh.PPC64LE.VettedValidation
