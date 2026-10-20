module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! The native key-generation body is safe for every domain encoding and
returns the specified key-generation result for valid public moduli. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def keyResult (p : Inputs) (rb : List Byte) (s : State) : Prop :=
  s.gpr .r0 = keyMainFlag p rb ∧
  Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.k =
    (if keySuccess p rb then scalarOctets p rb else List.replicate p.k 0) ∧
  Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k =
    (if keySuccess p rb then Spec.Rsa.i2osp (keyPower p (scalarOctets p rb)) p.k else List.replicate p.k 0)

theorem keyBody_ok (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.GenerateKey.main) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → keyResult p rb t) ∧
      Frame (keyWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨context, zero, frame, rest⟩
  have entryFrame : Frame (keyWrites p s) s.mem u.mem := frame.mono (by simp [keyWrites])
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
    refine WP.mono (keyMain_ok u context stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
      (by simp [h28]) (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48])
      (by simp) (by simp) saved' facts.2.1 facts.1 entropyU size (by rw [rest.sp]; exact entropyStack)
      (outputs.after rest) entropySep privateLength outputY) ?_
    rintro t ⟨result, privateT, publicT, frameT⟩
    exact ⟨fun _ => ⟨result, privateT, publicT⟩, entryFrame.trans (by simpa only [keyWrites, rest.sp] using frameT)⟩
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨_, mem⟩, _⟩
    exact ⟨fun hv => (valid hv).elim, by rw [mem]; exact entryFrame⟩

end VG.Proof.Ffdh.Arm
