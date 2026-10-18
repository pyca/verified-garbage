module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Octets

/-! # Combining padding validity with a checked RSA output -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc
open VG

theorem written_mask32 {m m' : Mem} {p : Addr} {k : Nat} {r r' : BitVec 32}
    {result : Option (List Byte)} (bad : Bool)
    (written : Spec.Rsa.written m p k r result)
    (status : r' = (r &&& (BitVec.ofNat 32 bad.toNat - 1)) &&& 1)
    (bytes : Spec.Rsa.bytesAt m' p k = (Spec.Rsa.bytesAt m p k).map
      (fun b => b &&& (BitVec.ofNat 32 bad.toNat - 1).setWidth 8)) :
    Spec.Rsa.written m' p k r' (if bad then none else result) := by
  cases bad
  · have mask : BitVec.ofNat 32 false.toNat - 1 = BitVec.allOnes 32 := by decide
    rw [mask, BitVec.and_allOnes] at status
    rw [mask, show (BitVec.allOnes 32).setWidth 8 = BitVec.allOnes 8 from rfl] at bytes
    simp only [BitVec.and_allOnes, List.map_id'] at bytes
    cases result with
    | none =>
      change r = 0 ∧ _ at written
      change r' = 0 ∧ _
      rw [status, written.1]
      constructor
      · decide
      · exact bytes.trans written.2
    | some y =>
      change r = 1 ∧ _ at written
      change r' = 1 ∧ _
      rw [status, written.1, BitVec.and_self]
      exact ⟨rfl, bytes.trans written.2⟩
  · have mask : BitVec.ofNat 32 true.toNat - 1 = 0#32 := by decide
    rw [mask, BitVec.and_zero, BitVec.zero_and] at status
    rw [mask, show (0#32).setWidth 8 = 0#8 from rfl] at bytes
    simp only [BitVec.and_zero, List.map_const', VG.Proof.Bignum.bytesAt_length] at bytes
    exact ⟨status, bytes⟩

end VG.Proof.RsaPkcs1Enc
