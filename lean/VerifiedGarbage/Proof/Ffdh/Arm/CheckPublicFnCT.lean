module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntry

/-! The complete callable public check reveals only public FFDH inputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicFn_ct {p : Inputs} {yb : List Byte} (length : yb.length = p.k) :
    RelCT isa (fun s t => CheckPublicFnInput p yb s ∧ CheckPublicFnInput p yb t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPublic.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, CheckPublicFnInput p yb s ∧ a = entered s
  have entry := checkPublicEntry_ct.mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) a
      (PublicMainInput p [0, 36, 32, 28, 24] yb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (checkPublicEntry_ok (entered s) input.args input.incoming
      input.domain input.domainLength input.count input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    refine ⟨context, input.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact input.valueStack), ?_⟩
    rw [rest.sp]; exact input.valueStack
  have body := relCT_chain entry wp wp
    (checkPublicBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) length)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
