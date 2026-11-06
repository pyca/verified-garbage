module

public import VerifiedGarbage.Spec.RsaPkcs1Enc

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection: what it returns

For any private-key operation `rsadp` (`decryptWith`):

* `decryptWith_of_ok`: for a ciphertext of `k` octets (and `k ≥ 11`) for
  which `rsadp` returns `EM`, decryption returns `implicitDecode dB C EM`.
  `decryptWith_of_invalid`, `decryptWith_of_fault`: its errors are those of
  `rsadp`.
* `altLength_le`: the alternative length is at most `k - 11`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc

open Spec.RsaPkcs1Enc
open Spec.Rsa (Outcome)

theorem decryptWith_of_ok {rsadp : List Byte → Outcome} {k : Nat} {dB C EM : List Byte}
    (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .ok EM) :
    decryptWith rsadp k dB C = .ok (implicitDecode dB C EM) := by
  simp only [decryptWith, hC, hk, and_self, ite_true, hEM]

theorem decryptWith_of_invalid {rsadp : List Byte → Outcome} {k : Nat} {dB C : List Byte}
    (hEM : rsadp C = .invalid) : decryptWith rsadp k dB C = .invalid := by
  unfold decryptWith
  split <;> simp only [hEM]

theorem decryptWith_of_fault {rsadp : List Byte → Outcome} {k : Nat} {dB C : List Byte}
    (hC : C.length = k) (hk : 11 ≤ k) (hEM : rsadp C = .fault) :
    decryptWith rsadp k dB C = .fault := by
  simp only [decryptWith, hC, hk, and_self, ite_true, hEM]

/-- The alternative length is at most `k - 11`. -/
theorem altLength_le (k : Nat) (CL : List Byte) : altLength k CL ≤ k - 11 := by
  unfold altLength
  generalize List.range 128 = is
  suffices ∀ al, al ≤ k - 11 → is.foldl (fun al i =>
      let c := Spec.Rsa.os2ip [CL.getD (2 * i) 0, CL.getD (2 * i + 1) 0] % 2 ^ bitLength (k - 11)
      if c ≤ k - 11 then c else al) al ≤ k - 11 from this 0 (Nat.zero_le _)
  induction is with
  | nil => exact fun _ h => h
  | cons i is ih =>
    intro al hal
    refine ih _ ?_
    dsimp only
    split
    · rename_i hc; exact hc
    · exact hal


theorem i2osp_length (x n : Nat) : (Spec.Rsa.i2osp x n).length = n := by simp [Spec.Rsa.i2osp]

end VG.Proof.RsaPkcs1Enc
