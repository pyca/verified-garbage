module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBody
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateMain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
/-! AAPCS key generation from caller-provided entropy with native rejection. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyGenerateBody.lean`, which only this module imported.
section

/-! The native key-generation body is safe for every domain encoding and
returns the specified key-generation result for valid public moduli. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerateBody_ok (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail)) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → keyResult p rb t) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨context, zero, frame, rest⟩
  have entryFrame : Frame (keyCallWrites p s) s.mem u.mem := frame.mono (by simp [keyCallWrites, keyWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
    have stable' : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | rfl | hd
      · left; decide
      · left; decide
      · exact saved d hd
    have entropyU := entropy.after_frame frame rest (by simpa [size] using entropyStack)
    refine WP.mono (keyGenerateMain_ok prepare tail prep law u context (calls.after rest) stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
      (by simp [h28]) (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48])
      (by simp) (by simp) saved' facts.2.1 facts.1 facts.2.2 entropyU size (by rw [rest.sp]; exact entropyStack)
      (outputs.after rest) entropySep privateLength outputY) ?_
    rintro t ⟨result, privateT, publicT, frameT⟩
    exact ⟨fun _ => ⟨result, privateT, publicT⟩, entryFrame.trans (by simpa only [keyCallWrites, keyWrites, rest.sp] using frameT)⟩
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨_, mem⟩, _⟩
    exact ⟨fun hv => (valid hv).elim, by rw [mem]; exact entryFrame⟩

end VG.Proof.Ffdh.Arm
end

end

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
