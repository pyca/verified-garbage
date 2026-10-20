module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateBody
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBody
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerateEntered_ok (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) (s : State) {p : Inputs} {rb : List Byte}
    (h : ArgumentMemory p [] s) (calls : KeyCallMemory p s) (incoming : KeyIncoming p s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail))) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → keyResult p rb t) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (keyEntry_ok s h incoming privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  have entropyU := entropy.after_frame frame rest (by simpa [size] using entropyStack)
  refine WP.mono (keyGenerateBody_ok prepare tail prep law u context (calls.after rest) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    entropyU size (by rw [rest.sp]; exact entropyStack) (outputs.after rest) entropySep privateLength outputY) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (keyCallWrites p s) s.mem u.mem := frame.mono (by simp [keyCallWrites, keyWrites])
  exact ⟨result, entryFrame.trans (by simpa only [keyCallWrites, keyWrites, rest.sp] using frameT)⟩

structure KeyGenerateFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop extends KeyFnInput p rb s where
  calls : KeyCallMemory p (entered s)
  savedCall : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint (FrameStack.belowA (entered s).sp 48)

theorem keyGenerateFn_ok (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) (s : State) {p : Inputs} {rb : List Byte} (h : KeyGenerateFnInput p rb s) :
    WP isa (VG.Impl.Ffdh.Arm.KeyGenerate.code prepare tail) s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → keyResult p rb t) := by
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.code
  refine framed_of_separate _ s h.stackFits (keyCallWrites p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true →
      status = keyMainFlag p rb ∧ Spec.Rsa.bytesAt m (State.addr p.privateValue) p.k =
        (if keySuccess p rb then scalarOctets p rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.publicValue) p.k =
        (if keySuccess p rb then Spec.Rsa.i2osp (keyPower p (scalarOctets p rb)) p.k else List.replicate p.k 0)) ?_ ?_
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.saved r hr
    · have eq := List.mem_singleton.mp hr; subst r; exact h.savedCall
  refine WP.mono (keyGenerateEntered_ok prepare tail prep law (entered s) h.args h.calls h.incoming h.privateValue h.publicValue h.outputY h.privateLength
    h.entropy h.size h.entropyStack h.outputs h.entropySep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
