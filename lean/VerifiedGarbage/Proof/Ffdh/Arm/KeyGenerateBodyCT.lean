module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateMain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

/-! Key generation's public modulus gate and documented retry-status class
account for every branch before native exponentiation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem keyGenerateBody_ct (prepare tail : Prog isa) (prep : KeyPrepareLaw prepare) (law : KeyTailLaw tail) {p : Inputs} {slots : List Nat} {rb1 rb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h48 : 48 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : rb1.length = p.k) (size2 : rb2.length = p.k)
    (classification : Spec.Rsa.modulusValid p.P p.k = true → (keyScalarValid p rb1 ↔ keyScalarValid p rb2))
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (privateLength : p.privateLength = p.k) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => (KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ (KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail)) (fun _ _ => True) := by
  let Q := fun (rb : List Byte) (s : State) => (KeyScalarInput p (60 :: 56 :: slots) rb s ∧ KeyCallMemory p s) ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => (KeyScalarInput p slots rb1 s ∧ KeyCallMemory p s) ∧ (KeyScalarInput p slots rb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1.context, h.2.1.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {rb : List Byte} (size : rb.length = p.k) (h : KeyScalarInput p slots rb s ∧ KeyCallMemory p s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q rb) := by
    refine WP.mono (head_ok s h.1.context stable h0 h24 h32) ?_
    rintro t ⟨context, zero, frame, rest⟩
    exact ⟨⟨⟨context, h.1.entropy.after_frame frame rest (by simpa [size] using h.1.entropyStack),
      h.1.outputs.after rest, by rw [rest.sp]; exact h.1.entropyStack⟩, h.2.after rest⟩, zero⟩
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
  have branches : RelCT isa (fun s t => Q rb1 s ∧ Q rb2 t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.KeyGenerate.main prepare tail) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact keyGenerateMain_ct prepare tail prep law stable' (by simp [h0]) (by simp [h4]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp [h48]) (by simp) (by simp)
        saved' size1 size2 (classification valid) entropySep privateLength outputY facts.2.1 facts.1
        s t tr1 tr2 u v ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (wp · size1) (wp · size2) branches

end VG.Proof.Ffdh.Arm
