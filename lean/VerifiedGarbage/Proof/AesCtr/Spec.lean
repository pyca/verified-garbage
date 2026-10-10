import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCtr.Counter
import VerifiedGarbage.Spec.Ctr.Contract

/-!
# CTR: the mode one block at a time

Untrusted: everything here is checked by Lean. The functions implemented in
assembly encipher a copy of the counter block, XOR it into the next data
block and increment the counter block: CTR of the first `k + 1` blocks is
CTR of the first `k`, followed by the block XORed with `CIPH_K` of the
counter block to continue from after them (`crypt_snoc`), whose increment
is the counter block to continue from after `k + 1` (`next_succ`).
`ctrMode` is CTR as a `Mode`, for the loop the targets share with CBC.
-/

namespace VG.Proof.AesCtr

open VG Spec.Ctr
open VG.Proof.AesCbc (Mode)

theorem length_crypt (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs : List (List Byte)) :
    (crypt ciph t xs).length = xs.length := by
  simp [crypt, length_counters]

theorem crypt_snoc (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs : List (List Byte)) (x : List Byte) :
    crypt ciph t (xs ++ [x]) = crypt ciph t xs ++ [Spec.Cbc.xor x (ciph (next t xs.length))] := by
  rw [crypt, List.length_append, List.length_singleton, counters_succ, List.map_append,
    List.zipWith_append (by simp [length_counters])]
  rfl

/-- CTR, as a `Mode`. -/
def ctrMode : Mode where
  out R w t xs := crypt (Spec.Cbc.aesWith R w) t xs
  chain _ _ t xs := next t xs.length
  length_out _ _ _ _ := length_crypt _ _ _
  out_nil _ _ _ := rfl
  chain_nil _ _ _ := rfl

theorem ctrMode_out (R : Nat) (w t : List Byte) (xs : List (List Byte)) :
    ctrMode.out R w t xs = crypt (Spec.Cbc.aesWith R w) t xs := rfl

theorem ctrMode_chain (R : Nat) (w t : List Byte) (xs : List (List Byte)) :
    ctrMode.chain R w t xs = next t xs.length := rfl

end VG.Proof.AesCtr
