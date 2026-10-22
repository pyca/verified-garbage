module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec

/-! Reuse RSA's exact witness-loop unfolding with DSA's uniform-round target. -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

def candidateLoop (candidate checks i uniform : Nat) (r : List Byte) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep candidate checks
    (Spec.Rsa.splitTwos (candidate - 1)).1 (Spec.Rsa.splitTwos (candidate - 1)).2) (i, uniform) r

theorem bool_count (b : Bool) : (if b then 1 else 0) = b.toNat := by cases b <;> rfl

theorem candidate_loop_step {candidate checks i uniform drawBytes : Nat} (r : List Byte)
    (go : i ≤ 16 ∨ uniform < checks) (width : Spec.RsaKeyGen.witnessBytes candidate = drawBytes)
    (positive : 0 < drawBytes) :
    candidateLoop candidate checks i uniform r =
      if drawBytes ≤ r.length then
        let w := Spec.RsaKeyGen.witness (candidate - 1) (Spec.Rsa.os2ip (r.take drawBytes))
        if Spec.MillerRabin.round candidate w.1 then
          candidateLoop candidate checks (i + 1) (uniform + w.2.toNat) (r.drop drawBytes)
        else some (false, r.drop drawBytes)
      else none := by
  cases decomposition : Spec.Rsa.splitTwos (candidate - 1) with
  | mk a m =>
    simpa only [candidateLoop, Spec.RsaKeyGen.blindedChecks, VG.Proof.RsaKeyGen.seg, List.drop_zero,
      Nat.zero_add, Spec.MillerRabin.round, decomposition, bool_count] using
      VG.Proof.RsaKeyGen.mrLoop_step candidate checks a m drawBytes r i uniform 0 go width positive

theorem candidate_loop_done {candidate checks i uniform : Nat} (r : List Byte)
    (done : ¬ (i ≤ 16 ∨ uniform < checks)) : candidateLoop candidate checks i uniform r = some (true, r) :=
  VG.Proof.RsaKeyGen.mrLoop_done candidate checks (Spec.Rsa.splitTwos (candidate - 1)).1
    (Spec.Rsa.splitTwos (candidate - 1)).2 r i uniform done

end VG.Proof.Dsa.Generation
