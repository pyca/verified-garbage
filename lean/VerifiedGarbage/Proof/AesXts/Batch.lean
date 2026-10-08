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

/-- The blocks after a frame outside them. -/
theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ j < n, ∀ r ∈ rs, (⟨p + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  simp only [Spec.Cbc.blocksAt]
  exact List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf (hd j (List.mem_range.mp hj)) (by decide)

/-- The blocks after a call of a block function on all of them. -/
theorem blocksAt_of_out {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    {c : List Byte → List Byte} (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g)
    (hc : ∀ p, (g (Spec.Aes.stateAt m p)).toList = c (Spec.Aes.bytesAt m p 16)) :
    Spec.Cbc.blocksAt m' D n = (Spec.Cbc.blocksAt m D n).map c := by
  simp only [Spec.Cbc.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hs := congrArg (·[j]?) h
  simp only [Spec.Aes.statesAt, List.getElem?_map, List.getElem?_range (List.mem_range.mp hj),
    Option.map_some, Option.some.injEq] at hs
  simp only [Function.comp]
  rw [Proof.AesCbc.bytesAt_toList, hs, hc]

end VG.Proof.AesXts
