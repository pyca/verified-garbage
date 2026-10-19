module

public import VerifiedGarbage.Proof.Dsa.RandomResult
public import VerifiedGarbage.Spec.Dsa.RandomSign
import VerifiedGarbage.Proof.Framework.Omega

/-! One-step equations for the bounded randomized-signing loop. -/
@[expose] public section
namespace VG.Proof.Dsa
open VG.Spec.Dsa

/-- A failed sampler terminates signing without another attempt. -/
theorem randomSignLoop_sample_none (p q fuel : Nat) (key digest rand : List VG.Byte)
    (h : (VG.Spec.Dsa.Random.sample (privateKeyBytes p q key).params.q 128 rand).scalar = none) :
    randomSignLoop p q key digest (fuel + 1) rand =
      let draw := VG.Spec.Dsa.Random.sample (privateKeyBytes p q key).params.q 128 rand
      ⟨none, Random.sampleStatus draw, draw.used, draw.trace⟩ := by
  simp only [randomSignLoop, h, Random.sampleStatus]

/-- A successful supplied-nonce call terminates with its signature. -/
theorem randomSignLoop_step_success (p q fuel k : Nat) (key digest rand sig : List VG.Byte)
    (hd : (VG.Spec.Dsa.Random.sample (privateKeyBytes p q key).params.q 128 rand).scalar = some k)
    (hs : signBytes p q key (encodeBE q k) digest = some sig) :
    randomSignLoop p q key digest (fuel + 1) rand =
      let draw := VG.Spec.Dsa.Random.sample (privateKeyBytes p q key).params.q 128 rand
      ⟨some sig, 1, draw.used, draw.trace ++ [5]⟩ := by
  simp only [randomSignLoop, hd, hs]

/-- Failed signing consumes this nonce and continues on the remaining tape. -/
theorem randomSignLoop_retry (p q fuel k : Nat) (key digest rand : List VG.Byte)
    (hd : (VG.Spec.Dsa.Random.sample (privateKeyBytes p q key).params.q 128 rand).scalar = some k)
    (hs : signBytes p q key (encodeBE q k) digest = none) :
    randomSignLoop p q key digest (fuel + 1) rand =
      let draw := VG.Spec.Dsa.Random.sample (privateKeyBytes p q key).params.q 128 rand
      let next := randomSignLoop p q key digest fuel (rand.drop draw.used)
      { next with used := draw.used + next.used, trace := draw.trace ++ [6] ++ next.trace } := by
  simp only [randomSignLoop, hd, hs]

theorem randomSignLoop_status_le (p q fuel : Nat) (key digest rand : List VG.Byte) :
    (randomSignLoop p q key digest fuel rand).status ≤ 2 := by
  induction fuel generalizing rand with
  | zero => change 0 ≤ 2; decide
  | succ fuel ih =>
    simp only [randomSignLoop]
    split
    · split <;> (dsimp only; decide)
    · split
      · dsimp only; decide
      · exact ih _

end VG.Proof.Dsa
