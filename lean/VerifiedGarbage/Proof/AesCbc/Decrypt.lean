module

public import VerifiedGarbage.Proof.AesCbc.Spec

/-! # Indexed CBC decryption, for implementations that decipher blocks in parallel -/

@[expose] public section

namespace VG.Proof.AesCbc

open VG.Spec.Cbc

theorem decrypt_getD (ciph : Cipher) (iv : List Byte) (xs : List (List Byte))
    (k : Nat) (hk : k < xs.length) :
    (decrypt ciph iv xs).getD k [] =
      xor (ciph (xs.getD k [])) (next iv (xs.take k)) := by
  induction xs generalizing iv k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [decrypt, List.getD_cons_succ, List.take_succ_cons, next_cons] using
        ih x k (by simpa using hk)

theorem next_take_succ (iv : List Byte) (xs : List (List Byte)) (k : Nat)
    (hk : k < xs.length) : next iv (xs.take (k+1)) = xs.getD k [] := by
  induction xs generalizing iv k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [List.take_succ_cons, next_cons, List.getD_cons_succ] using
        ih x k (by simpa using hk)

end VG.Proof.AesCbc
