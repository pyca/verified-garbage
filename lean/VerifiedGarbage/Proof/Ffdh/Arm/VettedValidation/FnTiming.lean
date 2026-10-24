module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Fn
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.BodyTiming
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntry
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-! The frame and recognition introduce no secret-dependent trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups)

theorem fn_ct {p : Inputs} :
    RelCT isa (fun s t => Input p s ∧ Input p t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      VG.Impl.Ffdh.Arm.VettedValidation.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, Input p s ∧ a = entered s
  let Q := fun a : State => Context p [0, 32, 28, 24] a ∧
    VettedGroups.TableAt (a.syms tableSym) groups a
  have wp (a : State) (h : P a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) a Q := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono_syms (withAllRest (domainEntry_ok (entered s) input.args
      input.domain input.domainLength input.count input.scratch)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    have table := input.table.after_frame input.safe frame rest
    rw [← syms] at table
    exact ⟨context, table⟩
  have entry : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      (fun s t => Q s ∧ Q t ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := domainEntry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, hu⟩ := wp s h.1
    obtain ⟨_, v', ev, hv⟩ := wp t h.2.1
    obtain ⟨_, rfl⟩ := Exec.det e1 eu
    obtain ⟨_, rfl⟩ := Exec.det e2 ev
    exact ⟨timing.1, hu, hv, by rw [(Exec.rdwr eu).2.2, (Exec.rdwr ev).2.2]; exact h.2.2.1,
      by rw [Exec.syms eu, Exec.syms ev]; exact h.2.2.2⟩
  have body := entry.seq (body_ct (by decide) (by decide) (by decide) (by decide) (by decide))
  unfold VG.Impl.Ffdh.Arm.VettedValidation.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2.1)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2.1], related.2.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm.VettedValidation
