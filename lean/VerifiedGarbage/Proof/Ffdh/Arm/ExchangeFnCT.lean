module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! The complete callable shared-secret computation is constant time in the private scalar. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchangeFn_ct {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => ExchangeFnInput p yb xb1 s ∧ ExchangeFnInput p yb xb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.Exchange.code (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, ExchangeFnInput p yb xb s ∧ a = entered s
  have entry := exchangeEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) a
        (ExchangeMainInput p [0, 36, 44, 40, 32, 28, 24, 4] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (exchangeEntry_ok (entered s) input.args input.incoming input.out input.domain input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨context, input.peer.after_frame frame rest (sourceSep input.peerStack),
      input.scalar.after_frame frame rest (sourceSep input.scalarStack), input.output.after rest,
      by rw [rest.sp]; exact input.peerStack, by rw [rest.sp]; exact input.scalarStack,
      input.workspaceSep, by rw [rest.sp]; exact input.stackSep⟩
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (exchangeBody_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) related.1.peerLength related.1.positive related.1.scalarFit related.1.scalarCount length)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
