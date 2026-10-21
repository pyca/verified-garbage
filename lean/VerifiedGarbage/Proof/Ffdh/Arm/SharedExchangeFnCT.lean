module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeFn
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! The complete callable shared-secret computation is constant time in the private scalar. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem fn_ct (backend : MontBackend) {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => FnInput p yb xb1 s ∧ FnInput p yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, FnInput p yb xb s ∧ a = entered s
  have entry := exchangeEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) a
        (MainInput p [0, 36, 44, 40, 32, 28, 24, 4] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (exchangeEntry_ok (entered s) input.input.args input.input.incoming input.input.out input.input.domain input.input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, input.input.peer.after_frame frame rest (sourceSep input.input.peerStack),
      input.input.scalar.after_frame frame rest (sourceSep input.input.scalarStack), input.input.output.after rest,
      by rw [rest.sp]; exact input.input.peerStack, by rw [rest.sp]; exact input.input.scalarStack,
      input.input.workspaceSep, by rw [rest.sp]; exact input.input.stackSep⟩, input.calls.after rest⟩
  unfold VG.Impl.Ffdh.Arm.SharedExchange.code
  apply framed_ct (fun _ _ h => ⟨h.1.input.stackFits, h.2.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) related.1.input.peerLength related.1.input.positive related.1.input.scalarFit related.1.input.scalarCount length)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm.SharedExchange
