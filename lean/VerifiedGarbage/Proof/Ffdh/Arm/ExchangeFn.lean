module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! AAPCS shared-secret computation with native validation and output handling. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchangeEntered_ok (s : State) {p : Inputs} {yb xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : ExchangeIncoming p s)
    (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length)
    (peer : Octets p.base p.publicValue p.len yb s) (peerLength : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (scalarFit : xb.length < 2 ^ 32)
    (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.Exchange.main)) s fun t =>
        (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) ∧
        Frame (exchangeWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (exchangeEntry_ok s h incoming out domain domainLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte}
      (separate : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    rw [List.mem_singleton] at hr; subst r; exact separate
  refine WP.mono (exchangeBody_ok u context (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    (peer.after_frame frame rest (sourceSep peerStack)) peerLength
    (scalar.after_frame frame rest (sourceSep scalarStack)) positive scalarFit scalarCount
    (by rw [rest.sp]; exact peerStack) (by rw [rest.sp]; exact scalarStack) (output.after rest)
    workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (exchangeWrites p s) s.mem u.mem := frame.mono (by simp [exchangeWrites])
  exact ⟨result, entryFrame.trans (by simpa only [exchangeWrites, rest.sp] using frameT)⟩

structure ExchangeFnInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : ExchangeIncoming p (entered s)
  out : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  peer : Octets p.base p.publicValue p.len yb (entered s)
  peerLength : yb.length = p.k
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarFit : xb.length < 2 ^ 32
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  output : OutputBuffer p.output p.k (entered s)
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr (entered s).sp, 72⟩ ⟨State.addr p.output, p.k⟩
  saved : ∀ r ∈ exchangeWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem exchangeFn_ok (s : State) {p : Inputs} {yb xb : List Byte} (h : ExchangeFnInput p yb xb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.code s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) := by
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.code
  refine framed_of_separate _ s h.stackFits (exchangeWrites p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true → status = (if sharedAccepted p yb xb then 1 else 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.output) p.k =
        (if sharedAccepted p yb xb then Spec.Rsa.i2osp (sharedValue p yb xb) p.k else List.replicate p.k 0)) h.saved ?_
  refine WP.mono (exchangeEntered_ok (entered s) h.args h.incoming h.out h.domain h.domainLength
    h.peer h.peerLength h.scalar h.positive h.scalarFit h.scalarCount h.peerStack h.scalarStack h.output
    h.workspaceSep h.stackSep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
