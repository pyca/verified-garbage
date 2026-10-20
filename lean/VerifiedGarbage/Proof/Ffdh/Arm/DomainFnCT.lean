module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! The callable domain check reveals only the public domain. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainFn_ct {p : Inputs} :
    RelCT isa (fun s t => DomainFnInput p s ∧ DomainFnInput p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, DomainFnInput p s ∧ a = entered s
  have entry := domainEntry_ct.mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) a
      (Context p [0, 32, 28, 24]) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (domainEntry_ok (entered s) input.args
      input.domain input.domainLength input.count input.scratch)) ?_
    rintro u ⟨⟨context, _⟩, _⟩
    exact context
  have body := relCT_chain entry wp wp
    (domainBody_ct (by decide) (by decide) (by decide) (by decide) (by decide))
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
