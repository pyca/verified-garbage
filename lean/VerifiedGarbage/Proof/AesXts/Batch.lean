import VerifiedGarbage.Proof.AesXts.Spec

/-!
# XTS: all the blocks in one call

Untrusted: everything here is checked by Lean. The functions implemented in
assembly XOR each block's tweak into it in one pass (`xored`: after `i`
blocks, the first `i` have their tweaks XORed in, `xored_step`), encipher (or
decipher) all the blocks in one call, and XOR the tweaks in again in a second
pass: XTS of the blocks (`crypt_eq`).
-/

namespace VG.Proof.AesXts

open VG Spec.Xts
open VG.Proof.AesCbc (set_prefix)

/-- The blocks `ys` with the tweaks of the first `i` XORed in. -/
def xored (t : List Byte) (ys : List (List Byte)) (i : Nat) : List (List Byte) :=
  List.zipWith Spec.Cbc.xor (ys.take i) (tweaks t i) ++ ys.drop i

theorem xored_zero (t : List Byte) (ys : List (List Byte)) : xored t ys 0 = ys := by
  simp [xored, tweaks]

theorem length_prefix (t : List Byte) {ys : List (List Byte)} {i : Nat} (hi : i ≤ ys.length) :
    (List.zipWith Spec.Cbc.xor (ys.take i) (tweaks t i)).length = i := by
  simp [length_tweaks]; omega

/-- Block `i` is still the original one. -/
theorem xored_getElem (t : List Byte) {ys : List (List Byte)} {i : Nat} (hi : i < ys.length) :
    (xored t ys i)[i]? = ys[i]? := by
  rw [xored, List.getElem?_append_right (by rw [length_prefix t (by omega)]), length_prefix t (by omega),
    Nat.sub_self, List.getElem?_drop, Nat.add_zero]

/-- Block `i` with its tweak XORed in. -/
theorem xored_step (t : List Byte) {ys : List (List Byte)} {i : Nat} (hi : i < ys.length) :
    (xored t ys i).set i (Spec.Cbc.xor ys[i] (next t i)) = xored t ys (i + 1) := by
  rw [xored, set_prefix _ _ _ (length_prefix t (by omega)) hi, xored, List.take_add_one,
    List.getElem?_eq_getElem hi, tweaks_succ]
  simp only [Option.toList_some]
  rw [List.zipWith_append (by rw [List.length_take, length_tweaks]; omega)]
  rfl

/-- All the blocks with their tweaks XORed in. -/
theorem xored_all (t : List Byte) {ys : List (List Byte)} {n : Nat} (h : ys.length = n) :
    xored t ys n = List.zipWith Spec.Cbc.xor ys (tweaks t n) := by
  rw [xored, List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]

/-- The tweaks XORed in, the blocks enciphered (or deciphered), and the
tweaks XORed in again. -/
theorem zipWith_eq (ciph : Spec.Cbc.Cipher) :
    ∀ (xs ts : List (List Byte)),
      List.zipWith Spec.Cbc.xor ((List.zipWith Spec.Cbc.xor xs ts).map ciph) ts =
        List.zipWith (block ciph) ts xs
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, t :: ts => by
    simp only [List.zipWith_cons_cons, List.map_cons, zipWith_eq ciph xs ts]
    rfl

theorem crypt_eq (ciph : Spec.Cbc.Cipher) (t : List Byte) (xs : List (List Byte)) :
    List.zipWith Spec.Cbc.xor ((List.zipWith Spec.Cbc.xor xs (tweaks t xs.length)).map ciph)
      (tweaks t xs.length) = crypt ciph t xs :=
  zipWith_eq ciph xs _

end VG.Proof.AesXts
