module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.State
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Key generation as checking, sampling, then deriving -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

abbrev checked (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

abbrev draw (s₀ : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (rQBytes s₀)) 128 (rInput s₀).rand

theorem result_eq {s₀ : State} (A : KeyABI s₀) :
    rResult s₀ = if checked s₀ then
      match (draw s₀).scalar with
      | none => ⟨none, VG.Proof.Dsa.Random.sampleStatus (draw s₀), (draw s₀).used, (draw s₀).trace⟩
      | some x =>
        let res := Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
          (Spec.Dsa.encodeBE (rInput s₀).qLen x)
        ⟨res, Spec.Dsa.signStatus res, (draw s₀).used, (draw s₀).trace ++ [if res.isSome then 5 else 6]⟩
      else ⟨none, 0, 0, [4]⟩ := by
  have len : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length]; exact A.keyLength
  rw [rResult, VG.Proof.Dsa.generateKeyBytes_eq (pLen := (rInput s₀).pLen) (qLen := (rInput s₀).qLen) A.lengths len]
  change (if checked s₀ then match (draw s₀).scalar with
    | none => (⟨none, if (draw s₀).trace.getLast? == some 2 then 2 else 0, (draw s₀).used, (draw s₀).trace⟩ : Spec.Dsa.GenerateKeyResult)
    | some x => _ else _) = _
  cases hx : (draw s₀).scalar with
  | none => simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
  | some x => rfl

theorem checked_q {s₀ : State} (H : checked s₀ = true) : 1 < rq s₀ := by
  unfold checked Spec.Dsa.checkParametersBytes at H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  have B := (VG.Proof.Dsa.supported_bounds H.2.1).2.1
  change 1 < Spec.Dsa.decodeBE (rQBytes s₀)
  rw [rQ_decode]
  change 255 < (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q at B
  omega

theorem draw_spl (s₀ : State) : draw s₀ = spl s₀ 128 0 := by
  simp only [draw, spl, List.drop_zero, rq]

theorem result_status_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [result_eq A]
  split
  · cases hx : (draw s₀).scalar with
    | none => exact sampleStatus_le _
    | some x =>
      dsimp only
      unfold Spec.Dsa.signStatus
      split <;> omega
  · decide

theorem result_key {s₀ : State} (A : KeyABI s₀) :
    (rResult s₀).status ≠ 1 → (rResult s₀).key = none := by
  rw [result_eq A]
  split
  · cases hx : (draw s₀).scalar with
    | none => intro _; rfl
    | some x =>
      dsimp only
      generalize Spec.Dsa.deriveKeyBytes _ _ _ _ = result
      cases result <;> simp [Spec.Dsa.signStatus]
  · intro _; rfl

theorem result_used_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).used ≤ (rInput s₀).rand.length := by
  rw [result_eq A]
  split
  · cases hx : (draw s₀).scalar <;> exact VG.Proof.Dsa.Random.sample_used_le _ _ _
  · exact Nat.zero_le _

end VG.Proof.Dsa.X86.KeyRandom
