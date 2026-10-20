module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyEntered_ok (s : State) {p : Inputs} {rb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : KeyIncoming p s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.GenerateKey.main)) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → keyResult p rb t) ∧
      Frame (keyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (keyEntry_ok s h incoming privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  have entropyU := entropy.after_frame frame rest (by simpa [size] using entropyStack)
  refine WP.mono (keyBody_ok u context (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    entropyU size (by rw [rest.sp]; exact entropyStack) (outputs.after rest) entropySep privateLength outputY) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (keyWrites p s) s.mem u.mem := frame.mono (by simp [keyWrites])
  exact ⟨result, entryFrame.trans (by simpa only [keyWrites, rest.sp] using frameT)⟩

structure KeyFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : KeyIncoming p (entered s)
  privateValue : s.gpr .r0 = p.privateValue
  publicValue : s.gpr .r2 = p.publicValue
  outputY : p.output = p.publicValue
  privateLength : p.privateLength = p.k
  entropy : Octets p.base p.entropy p.len rb (entered s)
  size : rb.length = p.k
  entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr (entered s).sp, 72⟩
  outputs : KeyOutputs p (entered s)
  entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩
  saved : ∀ r ∈ keyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem keyFn_ok (s : State) {p : Inputs} {rb : List Byte} (h : KeyFnInput p rb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.code s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → keyResult p rb t) := by
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.code
  refine framed_of_separate _ s h.stackFits (keyWrites p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true →
      status = keyMainFlag p rb ∧ Spec.Rsa.bytesAt m (State.addr p.privateValue) p.k =
        (if keySuccess p rb then scalarOctets p rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.publicValue) p.k =
        (if keySuccess p rb then Spec.Rsa.i2osp (keyPower p (scalarOctets p rb)) p.k else List.replicate p.k 0)) h.saved ?_
  refine WP.mono (keyEntered_ok (entered s) h.args h.incoming h.privateValue h.publicValue h.outputY h.privateLength
    h.entropy h.size h.entropyStack h.outputs h.entropySep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
