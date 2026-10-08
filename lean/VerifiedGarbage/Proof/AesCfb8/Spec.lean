import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCbc.Spec

/-!
# CFB8: the mode one byte at a time

Untrusted: everything here is checked by Lean. The functions implemented in
assembly encrypt or decrypt one byte at a time: CFB8 of the first `k + 1`
bytes is CFB8 of the first `k`, followed by the byte from the input block
after those (`encrypt_snoc`, `decrypt_snoc`), which is the one before it
shifted left by a byte, with the last ciphertext byte shifted in
(`next_snoc`). On every target, where the proofs cover both directions at
once: `cfb8 enc` is encryption or decryption, and `cts enc` its ciphertext
bytes (the output or the input).
-/

namespace VG.Proof.AesCfb8

open VG Spec.Cfb8

/-- CFB8 in a direction. -/
def cfb8 (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv xs : List Byte) : List Byte :=
  if enc then encrypt ciph iv xs else decrypt ciph iv xs

/-- The ciphertext bytes of a direction: the output, or the input. -/
def cts (enc : Bool) (xs ys : List Byte) : List Byte := if enc then ys else xs

theorem length_encrypt (ciph : Spec.Cbc.Cipher) (iv xs : List Byte) :
    (encrypt ciph iv xs).length = xs.length := by
  induction xs generalizing iv with
  | nil => rfl
  | cons _ _ ih => simp [encrypt, ih]

theorem length_decrypt (ciph : Spec.Cbc.Cipher) (iv xs : List Byte) :
    (decrypt ciph iv xs).length = xs.length := by
  induction xs generalizing iv with
  | nil => rfl
  | cons _ _ ih => simp [decrypt, ih]

theorem length_cfb8 (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv xs : List Byte) :
    (cfb8 enc ciph iv xs).length = xs.length := by
  cases enc <;> simp [cfb8, length_encrypt, length_decrypt]

theorem next_nil (iv : List Byte) : next iv [] = iv := by simp [next]

theorem length_next (iv cs : List Byte) : (next iv cs).length = iv.length := by
  simp [next]

theorem next_cons {iv : List Byte} (h : iv ≠ []) (c : Byte) (cs : List Byte) :
    next iv (c :: cs) = next (iv.tail ++ [c]) cs := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [next]

/-- The input block after one more ciphertext byte. -/
theorem next_snoc {iv : List Byte} (h : iv ≠ []) (cs : List Byte) (c : Byte) :
    next iv (cs ++ [c]) = (next iv cs).tail ++ [c] := by
  induction cs generalizing iv with
  | nil =>
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
    simp [next]
  | cons d ds ih =>
    rw [List.cons_append, next_cons h, next_cons h, ih (by simp)]

theorem encrypt_snoc (ciph : Spec.Cbc.Cipher) {iv : List Byte} (h : iv ≠ []) (xs : List Byte) (x : Byte) :
    encrypt ciph iv (xs ++ [x]) =
      encrypt ciph iv xs ++ [x ^^^ (ciph (next iv (encrypt ciph iv xs))).headD 0] := by
  induction xs generalizing iv with
  | nil => simp [encrypt, next]
  | cons p ps ih =>
    simp only [List.cons_append, encrypt, next_cons h]
    rw [ih (by simp)]

theorem decrypt_snoc (ciph : Spec.Cbc.Cipher) {iv : List Byte} (h : iv ≠ []) (xs : List Byte) (x : Byte) :
    decrypt ciph iv (xs ++ [x]) = decrypt ciph iv xs ++ [x ^^^ (ciph (next iv xs)).headD 0] := by
  induction xs generalizing iv with
  | nil => simp [decrypt, next]
  | cons p ps ih =>
    simp only [List.cons_append, decrypt, next_cons h]
    rw [ih (by simp)]

/-- The input block of byte `k`, after the first `k` bytes of either
direction. -/
abbrev inK (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv xs : List Byte) : List Byte :=
  next iv (cts enc xs (cfb8 enc ciph iv xs))

theorem cfb8_nil (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv : List Byte) : cfb8 enc ciph iv [] = [] := by
  cases enc <;> rfl

theorem inK_nil (enc : Bool) (ciph : Spec.Cbc.Cipher) (iv : List Byte) : inK enc ciph iv [] = iv := by
  cases enc <;> simp [inK, cts, cfb8_nil, next_nil]

theorem cfb8_snoc (enc : Bool) (ciph : Spec.Cbc.Cipher) {iv : List Byte} (h : iv ≠ []) (xs : List Byte)
    (x : Byte) :
    cfb8 enc ciph iv (xs ++ [x]) = cfb8 enc ciph iv xs ++ [x ^^^ (ciph (inK enc ciph iv xs)).headD 0] := by
  cases enc
  · simp only [cfb8, cts, inK, Bool.false_eq_true, ↓reduceIte, decrypt_snoc ciph h]
  · simp only [cfb8, cts, inK, ↓reduceIte, encrypt_snoc ciph h]

/-- The input block after one more byte: the byte shifted in is the output
(encryption) or the input (decryption). -/
theorem inK_snoc (enc : Bool) (ciph : Spec.Cbc.Cipher) {iv : List Byte} (h : iv ≠ []) (xs : List Byte)
    (x : Byte) :
    inK enc ciph iv (xs ++ [x]) =
      (inK enc ciph iv xs).tail ++ [if enc then x ^^^ (ciph (inK enc ciph iv xs)).headD 0 else x] := by
  cases enc
  · simp only [inK, cts, Bool.false_eq_true, ↓reduceIte, next_snoc h]
  · simp only [inK, cts, ↓reduceIte, cfb8_snoc true ciph h, next_snoc h]

end VG.Proof.AesCfb8
