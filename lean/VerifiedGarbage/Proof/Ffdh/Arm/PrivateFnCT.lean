module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! The imported-private-key callable reveals only public inputs and its scalar validity class. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem privateFn_ct {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => PrivateFnInput p yb xb1 s ∧ PrivateFnInput p yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, PrivateFnInput p yb xb s ∧ a = entered s
  have entry := privateEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) a
        (PrivateMainInput p [0, 44, 40, 36, 32, 28, 24] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (privateEntry_ok (entered s) input.args input.incoming input.domain input.domainLength input.count input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨context, input.value.after_frame frame rest (sourceSep input.valueStack),
      input.scalar.after_frame frame rest (sourceSep input.scalarStack),
      by rw [rest.sp]; exact input.valueStack, by rw [rest.sp]; exact input.scalarStack,
      ⟩
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (privateBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      related.1.length related.1.positive related.1.scalarLength related.1.scalarCount length classification)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
