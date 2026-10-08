import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Spec.Ofb.Contract

/-!
# OFB: the mode one block at a time

Untrusted: everything here is checked by Lean. The functions implemented in
assembly encipher the block to continue from in place (`next`), then XOR it
into the next data block: OFB of the first `k + 1` blocks is OFB of the
first `k`, followed by the block XORed with `CIPH_K` of the block to
continue from after them (`crypt_snoc`), which is the block to continue
from after `k + 1` (`next_succ`). `ofbMode` is OFB as a `Mode`, for the
loop the targets share with CBC.
-/

namespace VG.Proof.AesOfb

open VG Spec.Ofb
open VG.Proof.AesCbc (Mode)

theorem length_outputs (ciph : Spec.Cbc.Cipher) (iv : List Byte) (n : Nat) :
    (outputs ciph iv n).length = n := by
  induction n generalizing iv with
  | zero => rfl
  | succ n ih => simp [outputs, ih]

theorem outputs_succ (ciph : Spec.Cbc.Cipher) (iv : List Byte) (n : Nat) :
    outputs ciph iv (n + 1) = outputs ciph iv n ++ [ciph (next ciph iv n)] := by
  induction n generalizing iv with
  | zero => rfl
  | succ n ih =>
    rw [outputs, ih]
    simp only [outputs, next, List.cons_append, List.getLastD_cons]

theorem next_succ (ciph : Spec.Cbc.Cipher) (iv : List Byte) (n : Nat) :
    next ciph iv (n + 1) = ciph (next ciph iv n) := by
  rw [next, outputs_succ]; simp

theorem length_crypt (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) :
    (crypt ciph iv xs).length = xs.length := by
  simp [crypt, length_outputs]

theorem crypt_snoc (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) (x : List Byte) :
    crypt ciph iv (xs ++ [x]) = crypt ciph iv xs ++ [Spec.Cbc.xor x (ciph (next ciph iv xs.length))] := by
  rw [crypt, List.length_append, List.length_singleton, outputs_succ,
    List.zipWith_append (by simp [length_outputs])]
  rfl

/-- OFB, as a `Mode`. -/
def ofbMode : Mode where
  out R w iv xs := crypt (Spec.Cbc.aesWith R w) iv xs
  chain R w iv xs := next (Spec.Cbc.aesWith R w) iv xs.length
  length_out _ _ _ _ := length_crypt _ _ _
  out_nil _ _ _ := rfl
  chain_nil _ _ _ := rfl

theorem ofbMode_out (R : Nat) (w iv : List Byte) (xs : List (List Byte)) :
    ofbMode.out R w iv xs = crypt (Spec.Cbc.aesWith R w) iv xs := rfl

theorem ofbMode_chain (R : Nat) (w iv : List Byte) (xs : List (List Byte)) :
    ofbMode.chain R w iv xs = next (Spec.Cbc.aesWith R w) iv xs.length := rfl

end VG.Proof.AesOfb
