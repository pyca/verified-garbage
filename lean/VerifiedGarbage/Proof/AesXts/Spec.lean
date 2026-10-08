import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Spec.Xts.Contract

/-!
# XTS: the mode one block at a time

Untrusted: everything here is checked by Lean. The functions implemented in
assembly XOR the tweak into the next data block, encipher (or decipher) it
in place, XOR the tweak in again and multiply the tweak by `α`: XTS of the
first `k + 1` blocks is XTS of the first `k`, followed by the block with the
tweak to continue from after them (`crypt_snoc`), whose product with `α` is
the tweak to continue from after `k + 1` (`next_succ`). `xtsMode enc` is
XTS in a direction as a `Mode`, for the loop the targets share with CBC.
-/

namespace VG.Proof.AesXts

open VG Spec.Xts
open VG.Proof.AesCbc (Mode ciphOf)

theorem length_tweaks (t : List Byte) (n : Nat) : (tweaks t n).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [tweaks, ih]

theorem next_succ (t : List Byte) (n : Nat) : next t (n + 1) = mulAlpha (next t n) := rfl

theorem next_succ' (t : List Byte) (n : Nat) : next t (n + 1) = next (mulAlpha t) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [next_succ, ih, ← next_succ]

theorem tweaks_succ (t : List Byte) (n : Nat) : tweaks t (n + 1) = tweaks t n ++ [next t n] := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [tweaks, ih, tweaks, next_succ']; rfl

theorem length_crypt (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs : List (List Byte)) :
    (crypt ciph t xs).length = xs.length := by
  simp [crypt, length_tweaks]

theorem crypt_snoc (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs : List (List Byte)) (x : List Byte) :
    crypt ciph t (xs ++ [x]) = crypt ciph t xs ++ [block ciph (next t xs.length) x] := by
  rw [crypt, List.length_append, List.length_singleton, tweaks_succ,
    List.zipWith_append (by simp [length_tweaks])]
  rfl

/-- XTS in a direction, as a `Mode`: encryption with `AES-enc(Key1, ·)`,
decryption with `AES-dec(Key1, ·)`. -/
def xtsMode (enc : Bool) : Mode where
  out R w t xs := crypt (ciphOf enc R w) t xs
  chain _ _ t xs := next t xs.length
  length_out _ _ _ _ := length_crypt _ _ _
  out_nil _ _ _ := rfl
  chain_nil _ _ _ := rfl

theorem xtsMode_out (enc : Bool) (R : Nat) (w t : List Byte) (xs : List (List Byte)) :
    (xtsMode enc).out R w t xs = crypt (ciphOf enc R w) t xs := rfl

theorem xtsMode_chain (enc : Bool) (R : Nat) (w t : List Byte) (xs : List (List Byte)) :
    (xtsMode enc).chain R w t xs = next t xs.length := rfl

end VG.Proof.AesXts
