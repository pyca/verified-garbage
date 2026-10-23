module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveMain
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveBody
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! The AAPCS derivation of an imported scalar's public value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem entered_ok (backend : MontBackend) (s : State) {p : Inputs} {xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : DeriveIncoming p s) (calls : SharedExchange.CallMemory p xb.length s)
    (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.SharedDerive.entry)
      (VG.Impl.Ffdh.Arm.Domain.head
        (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s
      fun t => (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) ∧
        Frame (SharedExchange.writes p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (deriveEntry_ok s h incoming out domain domainLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  refine WP.mono (body_ok backend u context (calls.after rest) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    (scalar.after_frame frame rest (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact scalarStack))
    positive scalarLength scalarCount (by rw [rest.sp]; exact scalarStack) (output.after rest)
    workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
  rintro t ⟨res, frameT⟩
  have entryFrame : Frame (SharedExchange.writes p s) s.mem u.mem :=
    frame.mono (by simp [SharedExchange.writes, exchangeWrites])
  exact ⟨res, entryFrame.trans (by simpa only [SharedExchange.writes, exchangeWrites, rest.sp] using frameT)⟩

structure FnInput (p : Inputs) (xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : DeriveIncoming p (entered s)
  calls : SharedExchange.CallMemory p xb.length (entered s)
  out : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarLength : xb.length ≤ p.k
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  output : OutputBuffer p.output p.k (entered s)
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr (entered s).sp, 72⟩ ⟨State.addr p.output, p.k⟩
  saved : ∀ r ∈ SharedExchange.writes p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem fn_ok (backend : MontBackend) (s : State) {p : Inputs} {xb : List Byte} (h : FnInput p xb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
      fun t => abiPreserved s t ∧ (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) := by
  unfold VG.Impl.Ffdh.Arm.SharedDerive.code
  refine framed_of_separate _ s h.stackFits (SharedExchange.writes p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true → status = SharedDerive.status p xb ∧
      Spec.Rsa.bytesAt m (State.addr p.output) p.k =
        (open Classical in if accepted p xb then Spec.Rsa.i2osp (sharedValue p (gOctets p) xb) p.k
          else List.replicate p.k 0)) h.saved ?_
  refine WP.mono (entered_ok backend (entered s) h.args h.incoming h.calls h.out h.domain h.domainLength
    h.scalar h.positive h.scalarLength h.scalarCount h.scalarStack h.output h.workspaceSep h.stackSep) ?_
  rintro t ⟨res, frame⟩
  exact ⟨frame, res⟩

end VG.Proof.Ffdh.Arm.SharedDerive
