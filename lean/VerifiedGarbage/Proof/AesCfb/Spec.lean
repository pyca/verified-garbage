import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Spec.Cfb.Contract

/-!
# CFB128: the mode one block at a time

Untrusted: everything here is checked by Lean. The functions implemented in
assembly encipher the block to continue from in place, XOR it into the next
data block, and make the ciphertext block the one to continue from: CFB of
the first `k + 1` blocks is CFB of the first `k`, followed by the block
XORed with `CIPH_K` of the last ciphertext block of those (`encrypt_snoc`,
`decrypt_snoc`). `cfbMode enc` is CFB128 in a direction as a `Mode`, for
the loop the targets share with CBC, whose chaining value (`Cbc.next` of
the ciphertext blocks) it is.
-/

namespace VG.Proof.AesCfb

open VG Spec.Cfb
open VG.Proof.AesCbc (Mode cts next_cons)

theorem length_encrypt (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) :
    (encrypt ciph iv xs).length = xs.length := by
  induction xs generalizing iv with
  | nil => rfl
  | cons _ _ ih => simp [encrypt, ih]

theorem length_decrypt (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) :
    (decrypt ciph iv xs).length = xs.length := by
  induction xs generalizing iv with
  | nil => rfl
  | cons _ _ ih => simp [decrypt, ih]

theorem encrypt_snoc (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) (x : List Byte) :
    encrypt ciph iv (xs ++ [x]) =
      encrypt ciph iv xs ++ [Spec.Cbc.xor x (ciph (Spec.Cbc.next iv (encrypt ciph iv xs)))] := by
  induction xs generalizing iv with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, encrypt, ih, next_cons]

theorem decrypt_snoc (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) (x : List Byte) :
    decrypt ciph iv (xs ++ [x]) = decrypt ciph iv xs ++ [Spec.Cbc.xor x (ciph (Spec.Cbc.next iv xs))] := by
  induction xs generalizing iv with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, decrypt, ih, next_cons]

/-- XORing `o` back into `x ⊕ o` gives `x`: decryption in place leaves the
ciphertext block in `iv`. -/
theorem xor_xor_cancel {o x : List Byte} (h : x.length = o.length) :
    Spec.Cbc.xor o (Spec.Cbc.xor x o) = x := by
  apply List.ext_getElem (by simp [Spec.Cbc.xor, h])
  intro i h₁ h₂
  simp only [Spec.Cbc.xor, List.getElem_zipWith]
  rw [BitVec.xor_comm, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- CFB128 in a direction. -/
def cfb (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv : List Byte) (xs : List (List Byte)) : List (List Byte) :=
  if enc then encrypt ciph iv xs else decrypt ciph iv xs

/-- CFB128 in a direction, as a `Mode`. -/
def cfbMode (enc : Bool) : Mode where
  out R w iv xs := cfb enc (Spec.Cbc.aesWith R w) iv xs
  chain R w iv xs := Spec.Cbc.next iv (cts enc xs (cfb enc (Spec.Cbc.aesWith R w) iv xs))
  length_out R w iv xs := by cases enc <;> simp [cfb, length_encrypt, length_decrypt]
  out_nil R w iv := by cases enc <;> rfl
  chain_nil R w iv := by cases enc <;> rfl

theorem cfbMode_out (enc : Bool) (R : Nat) (w iv : List Byte) (xs : List (List Byte)) :
    (cfbMode enc).out R w iv xs = cfb enc (Spec.Cbc.aesWith R w) iv xs := rfl

theorem cfbMode_chain (enc : Bool) (R : Nat) (w iv : List Byte) (xs : List (List Byte)) :
    (cfbMode enc).chain R w iv xs = Spec.Cbc.next iv (cts enc xs ((cfbMode enc).out R w iv xs)) := rfl

end VG.Proof.AesCfb
