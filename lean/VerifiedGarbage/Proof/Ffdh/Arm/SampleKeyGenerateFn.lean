module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGenerateBody
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sampleKeyGenerateEntered_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) (s : State) {p : Inputs} {rb : List Byte}
    (h : ArgumentMemory p [] s) (environment : env.holds p s) (calls : KeyCallMemory p s) (incoming : KeyIncoming p s)
    (privateValue : s.gpr .r0 = p.privateValue) (publicValue : s.gpr .r2 = p.publicValue)
    (outputY : p.output = p.publicValue) (privateLength : p.privateLength = p.k)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SampleKeyGenerate.main prepare sample tail))) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (layout p) rb t) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (keyEntry_ok s h incoming privateValue publicValue outputY privateLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩ syms
  have entryFrame : Frame (keyCallWrites p s) s.mem u.mem := frame.mono (by simp [keyCallWrites, keyWrites])
  have environmentU := env.stable environment entryFrame (rest.mono (by simp [roundClobbers])) syms
  have entropyU := entropy.after_frame frame rest (by simpa [size] using entropyStack)
  refine WP.mono (sampleKeyGenerateBody_ok prepare sample tail env layout prep sampler law u context environmentU (calls.after rest) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide) (by intro d hd; revert d; decide)
    entropyU size (by rw [rest.sp]; exact entropyStack) (outputs.after rest) entropySep privateLength outputY) ?_
  rintro t ⟨result, frameT⟩
  exact ⟨result, entryFrame.trans (by simpa only [keyCallWrites, keyWrites, rest.sp] using frameT)⟩

theorem sampleKeyGenerateFn_ok (prepare sample tail : Prog isa) (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env layout sample) (law : SampleTailLaw tail) (s : State) {p : Inputs} {rb : List Byte} (h : KeyGenerateFnInput p rb s) (environment : env.holds p (entered s)) :
    WP isa (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → sampleResult p (layout p) rb t) := by
  unfold VG.Impl.Ffdh.Arm.SampleKeyGenerate.code
  refine framed_of_separate _ s h.stackFits (keyCallWrites p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true →
      status = sampleMainFlag p (layout p) rb ∧ Spec.Rsa.bytesAt m (State.addr p.privateValue) p.k =
        (if sampleSuccess p (layout p) rb then (layout p).encode rb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.publicValue) p.k =
        (if sampleSuccess p (layout p) rb then Spec.Rsa.i2osp (keyPower p ((layout p).encode rb)) p.k else List.replicate p.k 0)) ?_ ?_
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.saved r hr
    · have eq := List.mem_singleton.mp hr; subst r; exact h.savedCall
  refine WP.mono (sampleKeyGenerateEntered_ok prepare sample tail env layout prep sampler law (entered s) h.args environment h.calls h.incoming h.privateValue h.publicValue h.outputY h.privateLength
    h.entropy h.size h.entropyStack h.outputs h.entropySep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
