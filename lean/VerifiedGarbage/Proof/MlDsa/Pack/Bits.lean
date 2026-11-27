module

public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA: bit packing as numbers, for every target

`SimpleBitPack` and `BitPack` (Algorithms 16 and 17) write the coefficients as
`d`-bit fields through arrays of bits (`IntegerToBits`, `BitsToBytes`), and
`SimpleBitUnpack` and `BitUnpack` (Algorithms 18 and 19) read them back
(`BytesToBits`, `BitsToInteger`). Here they are restated without bits, as
ML-KEM's `ByteEncode` and `ByteDecode` are (`Proof/MlKem/Bits.lean`, whose
`digits` this uses): a list of integers less than `2ᵈ` is the digits of a
little-endian number in base `2ᵈ`, and

* byte `k` of the packing of `L` is byte `k` of the number whose base-`2ᵈ`
  digits are `L` (`pack_getElem`), and group by group: when `d · c = 8 · nb`,
  byte `t` of group `g` (`nb` bytes) is byte `t` of the number whose digits
  are the `c` integers of group `g` (`pack_group`);
* field `i` of bytes `v` is base-`2ᵈ` digit `i` of the number whose bytes
  are `v` (`field_eq`), and group by group (`digits_group`);
* hence `simpleBitPack`, `bitPack`, `simpleBitUnpack` and `bitUnpack`
  (`simpleBitPack_eq`, `bitPack_eq`, `simpleBitUnpack_get`,
  `bitUnpack_get`);
* packing and unpacking a polynomial with coefficients in `[-a, b]` returns
  that polynomial (`bitUnpack_bitPack`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa
open VG.Proof.MlKem (digits digits_bit sum_bits ofNat8_mod getElem?_flatMap_const length_flatMap_const
  digits_chunk mod_pow_div_mod map_bytes_lt)

theorem t1Max_eq : t1Max = 1023 := by decide

/-! ## Packing -/

/-- The bits of the `d`-bit fields of `L`. -/
abbrev fieldBits (d : Nat) (L : List Nat) : Array Bool := (L.flatMap fun a => integerToBits a d).toArray

theorem fieldBits_size (d : Nat) (L : List Nat) : (fieldBits d L).size = d * L.length := by
  simp only [fieldBits, List.size_toArray]
  exact length_flatMap_const _ (fun a => by simp [integerToBits]) L

private theorem toNat_decide (x : Nat) : (decide (x % 2 = 1)).toNat = x % 2 := by
  cases Nat.mod_two_eq_zero_or_one x with
  | inl h => rw [h]; rfl
  | inr h => rw [h]; rfl

/-- Bit `p` of the fields of `L`: bit `p mod d` of `L[⌊p / d⌋]`, as a
number (0 past the end). -/
theorem fieldBits_getD {d : Nat} (hd : 0 < d) (L : List Nat) (p : Nat) :
    ((fieldBits d L).getD p false).toNat = L.getD (p / d) 0 / 2 ^ (p % d) % 2 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    getElem?_flatMap_const _ (d := d) hd _ (fun a _ => by simp [integerToBits]), List.getD_eq_getElem?_getD]
  cases h : L[p / d]? with
  | none => simp
  | some a =>
    simp only [Option.bind_some, Option.getD_some, integerToBits,
      List.getElem?_map, List.getElem?_range (Nat.mod_lt _ hd), Option.map_some]
    exact toNat_decide _

theorem pack_length (d : Nat) (L : List Nat) (hL : L.length = 256) :
    (bitsToBytes (fieldBits d L)).length = 32 * d := by
  simp only [bitsToBytes, List.length_map, List.length_range, fieldBits_size, hL]
  omega_using []

/-- Byte `k` of the packing of `L` is byte `k` of the number whose
base-`2ᵈ` digits are `L`. -/
theorem pack_getElem {d : Nat} (hd : 0 < d) {L : List Nat} (hL : L.length = 256)
    (hF : ∀ a ∈ L, a < 2 ^ d) {k : Nat} (hk : k < 32 * d) :
    (bitsToBytes (fieldBits d L))[k]! = BitVec.ofNat 8 (digits d L / 2 ^ (8 * k)) := by
  rw [getElem!_pos _ _ (by rw [pack_length d L hL]; exact hk)]
  simp only [bitsToBytes, List.getElem_map, List.getElem_range]
  rw [← ofNat8_mod (digits d L / 2 ^ (8 * k))]
  refine congrArg (BitVec.ofNat 8) ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← sum_bits (digits d L / 2 ^ (8 * k)) 8]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  rw [fieldBits_getD hd L (8 * k + j), ← digits_bit hd hF, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- Byte `nb · g + t` of the packing of `L` when each group of `nb` bytes
holds `c` fields (`d · c = 8 · nb`): byte `t` of the number whose base-`2ᵈ`
digits are the `c` integers of group `g`. -/
theorem pack_group {d c nb : Nat} (hd : 0 < d) (hdc : d * c = 8 * nb) {L : List Nat}
    (hL : L.length = 256) (hF : ∀ a ∈ L, a < 2 ^ d) {g t : Nat} (ht : t < nb)
    (hk : nb * g + t < 32 * d) :
    (bitsToBytes (fieldBits d L))[nb * g + t]! =
      BitVec.ofNat 8 (digits d ((L.drop (c * g)).take c) / 2 ^ (8 * t)) := by
  have hx : 8 * (nb * g + t) = d * (c * g) + 8 * t := by
    rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, hdc]
  rw [pack_getElem hd hL hF hk, hx, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    ← ofNat8_mod (_ / 2 ^ (8 * t)), ← ofNat8_mod (digits d _ / 2 ^ (8 * t)), ← digits_chunk hF,
    show (256 : Nat) = 2 ^ 8 from rfl, mod_pow_div_mod _ (show 8 * t + 8 ≤ d * c by omega_using [hdc, ht])]

theorem simpleBitPack_eq (w : Vector Nat n) (b : Nat) :
    simpleBitPack w b = bitsToBytes (fieldBits (bitlen b) w.toList) := rfl

theorem bitPack_eq (w : IPoly) (a b : Nat) :
    bitPack w a b = bitsToBytes (fieldBits (bitlen (a + b)) (w.toList.map fun wi => ((b : Int) - wi).toNat)) := by
  simp only [bitPack, fieldBits, List.flatMap_map]

/-! ## Unpacking -/

private theorem sum_map_two_mul (g : Nat → Nat) :
    ∀ l : List Nat, (l.map fun x => 2 * g x).sum = 2 * (l.map g).sum
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, sum_map_two_mul g l]; omega_using []

/-- `BitsToInteger` of `c` bits. -/
theorem bitsToInteger_range (f : Nat → Bool) :
    ∀ c, bitsToInteger ((List.range c).map f) = ((List.range c).map fun j => (f j).toNat * 2 ^ j).sum
  | 0 => rfl
  | c + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons, List.map_map,
      List.sum_cons]
    simp only [bitsToInteger, List.foldr_cons] at *
    rw [show List.foldr (fun b x => 2 * x + b.toNat) 0 (List.map (f ∘ Nat.succ) (List.range c)) =
      bitsToInteger ((List.range c).map fun j => f (j + 1)) from rfl, bitsToInteger_range _ c]
    have e : (List.map ((fun j => (f j).toNat * 2 ^ j) ∘ Nat.succ) (List.range c)) =
        (List.range c).map fun j => 2 * ((f (j + 1)).toNat * 2 ^ j) :=
      List.map_congr_left fun j _ => by
        simp only [Function.comp_apply, Nat.pow_succ, Nat.succ_eq_add_one]; rw [Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.mul_assoc]
    rw [e, sum_map_two_mul, Nat.pow_zero, Nat.mul_one, Nat.add_comm]

/-- Bit `p` of `BytesToBits(v)`, as a number: bit `p mod 8` of byte
`⌊p / 8⌋` (0 past the end). -/
theorem bytesToBits_getD (v : List Byte) (p : Nat) :
    ((bytesToBits v).getD p false).toNat = (v.map (·.toNat)).getD (p / 8) 0 / 2 ^ (p % 8) % 2 := by
  simp only [bytesToBits]
  rw [show (v.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)) =
    (v.map (·.toNat)).flatMap (fun a => integerToBits a 8) by simp [List.flatMap_map, integerToBits]]
  exact fieldBits_getD (by decide) _ p

/-- Field `i` of the `d`-bit fields of `v` is base-`2ᵈ` digit `i` of the
number whose bytes are `v`. -/
theorem field_eq (d : Nat) (v : List Byte) (i : Nat) :
    bitsToInteger ((List.range d).map fun j => (bytesToBits v).getD (i * d + j) false) =
      digits 8 (v.map (·.toNat)) / 2 ^ (d * i) % 2 ^ d := by
  rw [bitsToInteger_range, ← sum_bits _ d]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  rw [bytesToBits_getD, ← digits_bit (by decide) (map_bytes_lt v), Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.mul_comm d i]

/-- Digit `e` of the number whose bytes are group `g` of `L` (`nb` bytes),
when a group holds `c` digits (`d · c = 8 · nb`): digit `c · g + e` of the
number whose bytes are `L`. -/
theorem digits_group {d c nb : Nat} (hdc : d * c = 8 * nb) {L : List Nat} (hL : ∀ a ∈ L, a < 2 ^ 8)
    {g e : Nat} (he : e < c) :
    digits 8 ((L.drop (nb * g)).take nb) / 2 ^ (d * e) % 2 ^ d = digits 8 L / 2 ^ (d * (c * g + e)) % 2 ^ d := by
  have hx : d * (c * g + e) = 8 * (nb * g) + d * e := by
    rw [Nat.mul_add, ← Nat.mul_assoc, hdc, Nat.mul_assoc]
  have hde : d * e + d ≤ 8 * nb := by
    rw [← hdc, show d * e + d = d * (e + 1) by rw [Nat.mul_succ]]; exact Nat.mul_le_mul_left _ he
  rw [← digits_chunk hL, mod_pow_div_mod _ hde, Nat.div_div_eq_div_mul, ← Nat.pow_add, hx]

theorem simpleBitUnpack_get (v : List Byte) (b : Nat) {i : Nat} (hi : i < n) :
    (simpleBitUnpack v b)[i]'hi = digits 8 (v.map (·.toNat)) / 2 ^ (bitlen b * i) % 2 ^ bitlen b := by
  simp only [simpleBitUnpack, Vector.getElem_ofFn]
  exact field_eq _ v i

theorem bitUnpack_get (v : List Byte) (a b : Nat) {i : Nat} (hi : i < n) :
    (bitUnpack v a b)[i]'hi =
      (b : Int) - (digits 8 (v.map (·.toNat)) / 2 ^ (bitlen (a + b) * i) % 2 ^ bitlen (a + b) : Nat) := by
  simp only [bitUnpack, Vector.getElem_ofFn]
  rw [field_eq]

/-- Reading field `i` from the packed bytes recovers its value when every field fits. -/
private theorem read_packed_field {d : Nat} (hd : 0 < d) {L : List Nat}
    (hlen : L.length = 256) (hfits : ∀ x ∈ L, x < 2 ^ d) {i : Nat} (hi : i < L.length) :
    bitsToInteger ((List.range d).map fun j =>
      (bytesToBits (bitsToBytes (fieldBits d L))).getD (i * d + j) false) = L[i] := by
  let v := bitsToBytes (fieldBits d L)
  rw [bitsToInteger_range, ← Nat.mod_eq_of_lt (hfits _ (List.getElem_mem hi)), ← sum_bits]
  refine congrArg List.sum (List.map_congr_left fun j hjMem => ?_)
  have hj := List.mem_range.mp hjMem
  let p := i * d + j
  have hp : p < 256 * d := calc
    i * d + j < (i + 1) * d := by rw [Nat.succ_mul]; omega
    _ ≤ 256 * d := Nat.mul_le_mul_right _ (by omega)
  have hk : p / 8 < 32 * d := by omega
  have hbyte : p / 8 < v.length := by rwa [pack_length d L hlen]
  change ((bytesToBits v).getD p false).toNat * 2 ^ j = _
  rw [bytesToBits_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hbyte, Option.map_some, Option.getD_some,
    ← getElem!_pos v _ hbyte, pack_getElem hd hlen hfits hk, BitVec.toNat_ofNat]
  rw [mod_pow_div_mod (c := 1) _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add,
    Nat.div_add_mod, Nat.pow_one, digits_bit hd hfits]
  simp [p, Nat.mul_comm i d, Nat.mul_add_div hd, Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj, List.getD_eq_getElem?_getD, hi]

/-- Unpacking a signed ML-DSA polynomial recovers every coefficient in the encoding range. -/
theorem bitUnpack_bitPack (w : IPoly) (a b : Nat)
    (hw : ∀ c ∈ w.toList, -(a : Int) ≤ c ∧ c ≤ b) :
    bitUnpack (bitPack w a b) a b = w := by
  let L := w.toList.map fun c => ((b : Int) - c).toNat
  have hlen : L.length = 256 := by simp [L, n]
  have hfits : ∀ x ∈ L, x < 2 ^ bitlen (a + b) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have bounds := hw c hc
    exact Nat.lt_of_le_of_lt (by omega : ((b : Int) - c).toNat ≤ a + b) Nat.lt_log2_self
  apply Vector.ext
  intro i hi
  rw [bitPack_eq]
  simp only [bitUnpack, Vector.getElem_ofFn]
  rw [read_packed_field (L := L) (by simp [bitlen]) hlen hfits (by simpa [L] using hi)]
  simp only [L, List.getElem_map, Vector.getElem_toList]
  have bounds := hw w[i] (List.getElem_mem (l := w.toList) (by simpa using hi))
  omega

end VG.Proof.MlDsa.Pack
