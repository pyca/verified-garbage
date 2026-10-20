module

public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# One-shot Merkle–Damgård digests: facts that do not depend on the target

A one-shot digest builds the last block or two of the padded message in
memory: the bytes after the message's whole blocks, `0x80`, zeros and the
length field (`Md.hash_one`, `Md.hash_two`). These are the bytes of those
blocks, one at a time, and of memory written at offsets from a base.
-/

@[expose] public section

namespace VG.Proof.MdStream.OneShot

open VG.Proof.Sha256.Stream (writeBytes getD_append_left getD_append_right)

theorem itp {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a :=
  by simp [h]

theorem itn {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp [h]

theorem getD_congr {xs : List Byte} {a b : Nat} (h : a = b) : xs.getD a 0 = xs.getD b 0 := h ▸ rfl

/-! ## Bytes at offsets from a base -/

theorem write_off (m : Mem) (b : Addr) {o j n : Nat} (v : BitVec (8 * n)) (ho : o + n < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.write (b + BitVec.ofNat 64 o) n v (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + n then v.extractLsb' (8 * (j - o)) 8 else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.write]
  rw [Offset.sub_toNat' b (by omega) hj]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + n
    · simp only [show j - o < n by omega, ite_true, h']
    · simp only [show ¬ j - o < n by omega, ite_false, h']
  · simp only [h, ite_false, false_and, show ¬ 2 ^ 64 + j - o < n by omega]

theorem writeW64_off (m : Mem) (b : Addr) {o j : Nat} (v : BitVec 64) (ho : o + 8 < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.writeW (b + BitVec.ofNat 64 o) v (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 8 then v.extractLsb' (8 * (j - o)) 8 else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW]
  exact write_off m b _ ho hj

theorem writeW128_off (m : Mem) (b : Addr) {o j : Nat} (v : BitVec 128) (ho : o + 16 < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.writeW (b + BitVec.ofNat 64 o) v (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 16 then v.extractLsb' (8 * (j - o)) 8 else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW]
  exact write_off m b _ ho hj

theorem writeW8_off (m : Mem) (b : Addr) {o j : Nat} (v : BitVec 8) (ho : o + 1 < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    m.writeW (b + BitVec.ofNat 64 o) v (b + BitVec.ofNat 64 j) =
      if j = o then v else m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW]
  rw [write_off m b _ ho hj]
  by_cases h : j = o
  · subst h; simp
  · simp only [show ¬ (o ≤ j ∧ j < o + 1) by omega, ite_false, h]

theorem writeBytes_off (m : Mem) (b : Addr) {o j : Nat} (xs : List Byte) (ho : o + xs.length < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    writeBytes m (b + BitVec.ofNat 64 o) xs (b + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + xs.length then xs.getD (j - o) 0 else m (b + BitVec.ofNat 64 j) := by
  simp only [writeBytes]
  rw [Offset.sub_toNat' b (by omega) hj]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + xs.length
    · simp only [show j - o < xs.length by omega, ite_true, h']
    · simp only [show ¬ j - o < xs.length by omega, ite_false, h']
  · simp only [h, ite_false, false_and, show ¬ 2 ^ 64 + j - o < xs.length by omega]

/-- Byte `i` of a little-endian 16-byte read. -/
theorem readW128_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 16) :
    (m.readW a 128).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 16) hi]
  rfl

/-! ## The last block or two -/

theorem getD_app (xs ys : List Byte) (k : Nat) :
    (xs ++ ys).getD k 0 = if k < xs.length then xs.getD k 0 else ys.getD (k - xs.length) 0 := by
  by_cases h : k < xs.length
  · rw [itp h, getD_append_left h]
  · rw [itn h]
    have := getD_append_right (p := xs) (q := ys) (j := k - xs.length)
    rwa [show xs.length + (k - xs.length) = k by omega] at this

theorem getD_rep (n k : Nat) : (List.replicate n (0 : Byte)).getD k 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_single (b : Byte) (k : Nat) : [b].getD k 0 = if k = 0 then b else 0 := by
  cases k <;> simp

section
variable (B : Nat) (xs : List Byte)

/-- The bytes of `xs` after its whole blocks. -/
abbrev rem : Nat := xs.length % B
/-- Where they start. -/
abbrev whl : Nat := B * (xs.length / B)

theorem rest_getD {k : Nat} : (Md.rest B xs).getD k 0 = xs.getD (whl B xs + k) 0 := by
  simp only [Md.rest, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem whl_rem : whl B xs + rem B xs = xs.length := Nat.div_add_mod _ _

/-- Byte `k < B` of the last block, if one: the bytes left, `0x80`, zeros and
the length field `lb`. -/
theorem pad1_getD {L : Nat} (hr : rem B xs + L < B) {k : Nat} (lb : List Byte) (hlb : lb.length = L) :
    (Md.rest B xs ++ [0x80] ++ List.replicate (B - L - 1 - rem B xs) 0 ++ lb).getD k 0 =
      if k < B - L then
        (if k < rem B xs then xs.getD (whl B xs + k) 0 else if k = rem B xs then 0x80 else 0)
      else lb.getD (k - (B - L)) 0 := by
  simp only [getD_app, List.length_append, Md.rest_length, List.length_singleton, List.length_replicate,
    getD_single, getD_rep, rest_getD]
  by_cases h1 : k < rem B xs
  · rw [itp (show k < rem B xs + 1 + (B - L - 1 - rem B xs) by omega), itp (show k < rem B xs + 1 by omega),
      itp h1, itp (show k < B - L by omega), itp h1]
  by_cases h2 : k = rem B xs
  · subst h2
    rw [itp (show rem B xs < rem B xs + 1 + (B - L - 1 - rem B xs) by omega),
      itp (show rem B xs < rem B xs + 1 by omega), itn h1, itp (show rem B xs - rem B xs = 0 by omega),
      itp (show rem B xs < B - L by omega), itn h1, itp rfl]
  by_cases h3 : k < B - L
  · rw [itp (show k < rem B xs + 1 + (B - L - 1 - rem B xs) by omega), itn (show ¬ k < rem B xs + 1 by omega),
      itp h3, itn h1, itn h2]
  · rw [itn (show ¬ k < rem B xs + 1 + (B - L - 1 - rem B xs) by omega), itn h3,
      show k - (rem B xs + 1 + (B - L - 1 - rem B xs)) = k - (B - L) by omega]

/-- Byte `k < B` of the first of two last blocks. -/
theorem pad2a_getD {k : Nat} :
    (Md.rest B xs ++ [0x80] ++ List.replicate (B - 1 - rem B xs) 0).getD k 0 =
      if k < rem B xs then xs.getD (whl B xs + k) 0 else if k = rem B xs then 0x80 else 0 := by
  simp only [getD_app, List.length_append, Md.rest_length, List.length_singleton, getD_single, getD_rep,
    rest_getD]
  by_cases h1 : k < rem B xs
  · rw [itp (show k < rem B xs + 1 by omega), itp h1, itp h1]
  by_cases h2 : k = rem B xs
  · subst h2
    rw [itp (show rem B xs < rem B xs + 1 by omega), itn h1, itp (show rem B xs - rem B xs = 0 by omega), itn h1,
      itp rfl]
  · rw [itn (show ¬ k < rem B xs + 1 by omega), itn h1, itn h2]

end

/-- Byte `k` of the second of two last blocks. -/
theorem pad2b_getD (B L : Nat) {k : Nat} (lb : List Byte) :
    (List.replicate (B - L) 0 ++ lb).getD k 0 = if k < B - L then 0 else lb.getD (k - (B - L)) 0 := by
  simp only [getD_app, List.length_replicate, getD_rep]

end VG.Proof.MdStream.OneShot
