import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.WriteBytes

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Spec`. -/
section

/-!
# Poly1305: lemmas about the specification

Facts about `Spec/Poly1305.lean` that do not depend on the target:
little-endian numbers of byte strings in memory, the accumulator of a message
extended by whole blocks or a last block, and the tag.
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305

/-! ## Little-endian numbers -/

theorem leNum_append (a b : List Byte) : leNum (a ++ b) = leNum a + 256 ^ a.length * leNum b := by
  induction a with
  | nil => simp [leNum]
  | cons x xs ih =>
    simp only [List.cons_append, leNum, ih, List.length_cons, Nat.pow_succ, Nat.mul_add,
      Nat.add_assoc, Nat.mul_comm _ 256, Nat.mul_assoc]

theorem leNum_lt (a : List Byte) : leNum a < 256 ^ a.length := by
  induction a with
  | nil => simp [leNum]
  | cons x xs ih =>
    simp only [leNum, List.length_cons, Nat.pow_succ]
    have := x.isLt
    omega

theorem leNum_replicate_zero (n : Nat) : leNum (List.replicate n (0 : Byte)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, leNum, ih]; rfl

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    show m _ = m _
    congr 1
    rw [BitVec.add_assoc, Nat.succ_eq_add_one, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 i)]
    rfl

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show m _ = m _
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem leNum_bytesAt_read (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p n) = (m.read p n).toNat := by
  induction n generalizing p with
  | zero => simp [bytesAt, leNum, Mem.read]
  | succ n ih =>
    rw [VG.Proof.Poly1305.bytesAt_succ, leNum, ih, Mem.read, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

theorem leNum_bytesAt_64 (m : Mem) (p : Addr) : leNum (bytesAt m p 8) = (m.readW p 64).toNat := by
  rw [VG.Proof.Poly1305.leNum_bytesAt_read]
  simp [Mem.readW]

/-- A number stored as three little-endian 64-bit words. -/
theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat +
      2 ^ 128 * (m.readW (p + 16) 64).toNat := by
  rw [show 24 = 8 + (8 + 8) from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.leNum_append, VG.Proof.Poly1305.leNum_append,
    VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.leNum_bytesAt_64, VG.Proof.Poly1305.leNum_bytesAt_64, VG.Proof.Poly1305.leNum_bytesAt_64,
    BitVec.add_assoc]
  show (m.readW p 64).toNat + 256 ^ 8 * ((m.readW (p + 8) 64).toNat +
    256 ^ 8 * (m.readW (p + 16) 64).toNat) = _
  omega

theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.leNum_append, VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.leNum_bytesAt_64,
    VG.Proof.Poly1305.leNum_bytesAt_64]
  rfl

/-! ## The accumulator -/

theorem block_append_left {a b : List Byte} (ha : a.length % 16 = 0) {i : Nat}
    (hi : i < a.length / 16) : block (a ++ b) i = block a i := by
  simp only [block]
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
  simp only [List.length_drop]; omega

theorem block_append_right {a b : List Byte} (ha : a.length % 16 = 0) (j : Nat) :
    block (a ++ b) (a.length / 16 + j) = block b j := by
  simp only [block]
  rw [show 16 * (a.length / 16 + j) = a.length + 16 * j by omega, List.drop_append,
    List.drop_of_length_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem numBlocks_append {a b : List Byte} (ha : a.length % 16 = 0) :
    numBlocks (a ++ b) = a.length / 16 + numBlocks b := by
  simp only [numBlocks, List.length_append]; omega

/-- The loop of `accumulate` from the accumulator `a`. -/
def absorbAll (r a : Nat) (msg : List Byte) : Nat :=
  (List.range (numBlocks msg)).foldl (fun a i => (r * (a + leNum (block msg i ++ [0x01]))) % P) a

theorem accumulate_eq (r : Nat) (msg : List Byte) : accumulate r msg = VG.Proof.Poly1305.absorbAll r 0 msg := rfl

theorem foldl_congr_mem {α β : Type} {f g : α → β → α} {l : List β} (a : α)
    (h : ∀ x y, y ∈ l → f x y = g x y) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [h a y List.mem_cons_self]
    exact ih _ fun x z hz => h x z (List.mem_cons_of_mem _ hz)

theorem absorbAll_append {r a : Nat} {x y : List Byte} (hx : x.length % 16 = 0) :
    VG.Proof.Poly1305.absorbAll r a (x ++ y) = VG.Proof.Poly1305.absorbAll r (VG.Proof.Poly1305.absorbAll r a x) y := by
  have hn : numBlocks x = x.length / 16 := by simp only [numBlocks]; omega
  have e : (List.range (x.length / 16)).foldl
      (fun b i => (r * (b + leNum (block (x ++ y) i ++ [0x01]))) % P) a = VG.Proof.Poly1305.absorbAll r a x := by
    rw [VG.Proof.Poly1305.absorbAll, hn]
    exact VG.Proof.Poly1305.foldl_congr_mem a fun b i hi => by rw [VG.Proof.Poly1305.block_append_left hx (List.mem_range.mp hi)]
  rw [VG.Proof.Poly1305.absorbAll, VG.Proof.Poly1305.numBlocks_append hx, List.range_add, List.foldl_append, List.foldl_map, e, VG.Proof.Poly1305.absorbAll]
  exact VG.Proof.Poly1305.foldl_congr_mem _ fun b j _ => by rw [VG.Proof.Poly1305.block_append_right hx]

theorem accumulate_append {r : Nat} {a b : List Byte} (ha : a.length % 16 = 0) :
    accumulate r (a ++ b) = VG.Proof.Poly1305.absorbAll r (accumulate r a) b := by
  rw [VG.Proof.Poly1305.accumulate_eq, VG.Proof.Poly1305.accumulate_eq, VG.Proof.Poly1305.absorbAll_append ha]

/-- Absorbing one block, of 1 to 16 bytes. -/
theorem absorbAll_block {r a : Nat} {b : List Byte} (h₁ : 0 < b.length) (h₂ : b.length ≤ 16) :
    VG.Proof.Poly1305.absorbAll r a b = (r * (a + leNum (b ++ [0x01]))) % P := by
  have hn : numBlocks b = 1 := by simp only [numBlocks]; omega
  simp only [VG.Proof.Poly1305.absorbAll, hn, List.range_one, List.foldl_cons, List.foldl_nil, block, Nat.mul_zero,
    List.drop_zero]
  rw [List.take_of_length_le h₂]

theorem absorbAll_nil (r a : Nat) : VG.Proof.Poly1305.absorbAll r a [] = a := rfl

theorem accumulate_append_block {r : Nat} {a b : List Byte} (ha : a.length % 16 = 0)
    (h₁ : 0 < b.length) (h₂ : b.length ≤ 16) :
    accumulate r (a ++ b) = (r * (accumulate r a + leNum (b ++ [0x01]))) % P := by
  rw [VG.Proof.Poly1305.accumulate_append ha, VG.Proof.Poly1305.absorbAll_block h₁ h₂]

theorem absorbAll_lt {r a : Nat} (ha : a < P) (msg : List Byte) : VG.Proof.Poly1305.absorbAll r a msg < P := by
  rw [VG.Proof.Poly1305.absorbAll]
  generalize numBlocks msg = n
  induction n with
  | zero => exact ha
  | succ n _ =>
    rw [List.range_succ, List.foldl_append]
    exact Nat.mod_lt _ (by simp [P])

theorem accumulate_lt (r : Nat) (msg : List Byte) : accumulate r msg < P :=
  VG.Proof.Poly1305.absorbAll_lt (by simp [P]) msg

/-! ## Clamping `r` -/

theorem land_split {a b c d : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (a + 2 ^ 64 * b) &&& (c + 2 ^ 64 * d) = (a &&& c) + 2 ^ 64 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp [Nat.testBit_and]

/-- The clamped `r` of a key stored as two little-endian 64-bit words. -/
theorem clamp_words (k0 k1 : BitVec 64) :
    clamp (k0.toNat + 2 ^ 64 * k1.toNat) =
      (k0 &&& 0x0ffffffc0fffffff).toNat + 2 ^ 64 * (k1 &&& 0x0ffffffc0ffffffc).toNat := by
  rw [clamp, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0ffffffc0fffffff + 2 ^ 64 * 0x0ffffffc0ffffffc from rfl,
    VG.Proof.Poly1305.land_split k0.isLt (by decide), BitVec.toNat_and, BitVec.toNat_and]
  rfl

/-! ## The tag -/

theorem leBytes_add (a b x : Nat) :
    leBytes (a + b) x = leBytes a x ++ leBytes b (x / 256 ^ a) := by
  simp only [leBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem leBytes_mod (n x : Nat) : leBytes n (x % 256 ^ n) = leBytes n x := by
  simp only [leBytes]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 256 ^ n = 256 ^ i * 256 ^ (n - i) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  rw [show (2 : Nat) ^ 8 = 256 from rfl]
  exact ⟨256 ^ (n - i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩

theorem leBytes_succ (n x : Nat) : leBytes (n + 1) x = BitVec.ofNat 8 x :: leBytes n (x / 256) := by
  rw [Nat.add_comm, VG.Proof.Poly1305.leBytes_add, Nat.pow_one]; simp [leBytes]

theorem bytesAt_leBytes (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n = leBytes n (m.read p n).toNat := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have e : (m.read p (n + 1)).toNat = (m.read (p + 1) n).toNat * 256 + (m p).toNat := by
      rw [Mem.read, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
        Nat.shiftLeft_eq]
    rw [VG.Proof.Poly1305.bytesAt_succ, VG.Proof.Poly1305.leBytes_succ, ih, e]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have := (m p).isLt
      omega
    · congr 1
      have := (m p).isLt
      omega

theorem bytesAt_leBytes_64 (m : Mem) (p : Addr) :
    bytesAt m p 8 = leBytes 8 (m.readW p 64).toNat := by
  rw [VG.Proof.Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- Two little-endian 64-bit words in memory are the 16 bytes of `x`, if they
are its low 128 bits. -/
theorem bytesAt_leBytes_16 (m : Mem) (p : Addr) (x : Nat)
    (h₀ : (m.readW p 64).toNat = x % 2 ^ 64)
    (h₁ : (m.readW (p + BitVec.ofNat 64 8) 64).toNat = x / 2 ^ 64 % 2 ^ 64) :
    bytesAt m p 16 = leBytes 16 x := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, h₀, h₁,
    VG.Proof.Poly1305.leBytes_add, show (2 : Nat) ^ 64 = 256 ^ 8 from rfl, VG.Proof.Poly1305.leBytes_mod, VG.Proof.Poly1305.leBytes_mod]

end VG.Proof.Poly1305

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Limbs26`. -/
section

/-!
# Poly1305 in 26-bit limbs

The arithmetic of vector implementations that keep numbers modulo `p` in five
limbs of 26 bits (`x₀ + 2²⁶ x₁ + … + 2¹⁰⁴ x₄`), as Nat identities with no
bounds: the products `d_j` of two such numbers, with the terms that pass
`2¹³⁰` folded back times 5, and their carrying; how a block's two words split
into limbs; the final reduction; and the interleaved Horner evaluation of four
lanes. Each function sums in the order the code does, so that the terms the
code computes are these functions by definition.
-/

namespace VG.Proof.Poly1305.Limbs26

open VG.Spec.Poly1305 (P)

/-- The number whose limbs are `a 0`, …, `a 4` (of any size). -/
def val (a : Nat → Nat) : Nat := a 0 + 2 ^ 26 * a 1 + 2 ^ 52 * a 2 + 2 ^ 78 * a 3 + 2 ^ 104 * a 4

theorem P_eq : P = 1361129467683753853853498429727072845819 := by decide

/-! ## Products -/

/-- The products `d_j = 5 Σ_{i > j} a_i b_(5+j-i) + Σ_{i ≤ j} a_i b_(j-i)`,
summed as the code does (`s + s · 2²` is `5 s`). -/
def pd (a b : Nat → Nat) : Nat → Nat
  | 0 => let s := a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1; s + s * 2 ^ 2 + a 0 * b 0
  | 1 => let s := a 2 * b 4 + a 3 * b 3 + a 4 * b 2; s + s * 2 ^ 2 + a 0 * b 1 + a 1 * b 0
  | 2 => let s := a 3 * b 4 + a 4 * b 3; s + s * 2 ^ 2 + a 0 * b 2 + a 1 * b 1 + a 2 * b 0
  | 3 => let s := a 4 * b 4; s + s * 2 ^ 2 + a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0
  | _ => a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0

/-- What the products leave out: the terms past `2¹³⁰`, over `2¹³⁰`. -/
def pc (a b : Nat → Nat) : Nat :=
  (a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1) + 2 ^ 26 * (a 2 * b 4 + a 3 * b 3 + a 4 * b 2) +
    2 ^ 52 * (a 3 * b 4 + a 4 * b 3) + 2 ^ 78 * (a 4 * b 4)

theorem pd_val (a b : Nat → Nat) : VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.pd a b) + P * VG.Proof.Poly1305.Limbs26.pc a b = VG.Proof.Poly1305.Limbs26.val a * VG.Proof.Poly1305.Limbs26.val b := by
  simp only [VG.Proof.Poly1305.Limbs26.val, VG.Proof.Poly1305.Limbs26.pd, VG.Proof.Poly1305.Limbs26.pc, VG.Proof.Poly1305.Limbs26.P_eq]
  grind

/-! ## Carrying -/

section
variable (d : Nat → Nat)

/-- The limbs carried from `d₀` up: `e₁ = d₁ + d₀ / 2²⁶`, … -/
def e1 : Nat := d 1 + d 0 / 2 ^ 26
def e2 : Nat := d 2 + VG.Proof.Poly1305.Limbs26.e1 d / 2 ^ 26
def e3 : Nat := d 3 + VG.Proof.Poly1305.Limbs26.e2 d / 2 ^ 26
def e4 : Nat := d 4 + VG.Proof.Poly1305.Limbs26.e3 d / 2 ^ 26
/-- `d₄`'s carry, times 5 (`c + c · 2²`), added to `d₀`'s low bits. -/
def g0 (M : Nat) : Nat := (d 0 &&& M) + (VG.Proof.Poly1305.Limbs26.e4 d / 2 ^ 26 + VG.Proof.Poly1305.Limbs26.e4 d / 2 ^ 26 * 2 ^ 2)

/-- The limbs after carrying, with the mask `M = 2²⁶ - 1`. -/
def carry (M : Nat) : Nat → Nat
  | 0 => VG.Proof.Poly1305.Limbs26.g0 d M &&& M
  | 1 => (VG.Proof.Poly1305.Limbs26.e1 d &&& M) + VG.Proof.Poly1305.Limbs26.g0 d M / 2 ^ 26
  | 2 => VG.Proof.Poly1305.Limbs26.e2 d &&& M
  | 3 => VG.Proof.Poly1305.Limbs26.e3 d &&& M
  | _ => VG.Proof.Poly1305.Limbs26.e4 d &&& M

end

theorem and_mask (x : Nat) : x &&& 0x3ffffff = x % 2 ^ 26 := by
  rw [show (0x3ffffff : Nat) = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem carry_val (d : Nat → Nat) : VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.carry d 0x3ffffff) + P * (VG.Proof.Poly1305.Limbs26.e4 d / 2 ^ 26) = VG.Proof.Poly1305.Limbs26.val d := by
  simp only [VG.Proof.Poly1305.Limbs26.val, VG.Proof.Poly1305.Limbs26.carry, VG.Proof.Poly1305.Limbs26.g0, VG.Proof.Poly1305.Limbs26.e4, VG.Proof.Poly1305.Limbs26.e3, VG.Proof.Poly1305.Limbs26.e2, VG.Proof.Poly1305.Limbs26.e1, VG.Proof.Poly1305.Limbs26.and_mask, VG.Proof.Poly1305.Limbs26.P_eq]
  omega

/-- The product of two numbers, carried. -/
def mul (a b : Nat → Nat) : Nat → Nat := VG.Proof.Poly1305.Limbs26.carry (VG.Proof.Poly1305.Limbs26.pd a b) 0x3ffffff

theorem mul_mod (a b : Nat → Nat) : VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.mul a b) % P = VG.Proof.Poly1305.Limbs26.val a * VG.Proof.Poly1305.Limbs26.val b % P := by
  have h₁ := VG.Proof.Poly1305.Limbs26.carry_val (VG.Proof.Poly1305.Limbs26.pd a b)
  have h₂ := VG.Proof.Poly1305.Limbs26.pd_val a b
  rw [← h₂, ← h₁, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, VG.Proof.Poly1305.Limbs26.mul]

/-! ## Splitting words into limbs

The limbs of `lo + 2⁶⁴ hi` (`lo < 2⁶⁴`), as the code splits them, are
`lo << 38 >> 38`, `lo << 12 >> 38`, `hi << 50 >> 38 | lo >> 52`,
`hi << 24 >> 38` and `hi >> 40`. (They are stated inline rather than as
definitions: `rfl` against a definition whose body is a division unfolds
the division, very slowly.) -/

theorem split_or {lo : Nat} (hlo : lo < 2 ^ 64) (hi : Nat) :
    (hi * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| lo / 2 ^ 52) = 2 ^ 12 * (hi % 2 ^ 14) + lo / 2 ^ 52 := by
  rw [show hi * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 = 2 ^ 12 * (hi % 2 ^ 14) by omega,
    ← Nat.two_pow_add_eq_or_of_lt (show lo / 2 ^ 52 < 2 ^ 12 by omega)]

theorem split_val {lo : Nat} (hlo : lo < 2 ^ 64) (hi : Nat) :
    lo * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 + 2 ^ 26 * (lo * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) +
      2 ^ 52 * (hi * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| lo / 2 ^ 52) + 2 ^ 78 * (hi * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) +
      2 ^ 104 * (hi / 2 ^ 40) = lo + 2 ^ 64 * hi := by
  rw [VG.Proof.Poly1305.Limbs26.split_or hlo]
  omega

/-! ## The final reduction -/

section
variable (c : Nat → Nat) (M five mk : Nat)

/-- `h₁` to `h₄` carried, with the mask `M`. -/
def f2' : Nat := c 2 + c 1 / 2 ^ 26
def f3' : Nat := c 3 + VG.Proof.Poly1305.Limbs26.f2' c / 2 ^ 26
def fc : Nat → Nat
  | 0 => c 0
  | 1 => c 1 &&& M
  | 2 => VG.Proof.Poly1305.Limbs26.f2' c &&& M
  | 3 => VG.Proof.Poly1305.Limbs26.f3' c &&& M
  | _ => c 4 + VG.Proof.Poly1305.Limbs26.f3' c / 2 ^ 26

/-- `g = h + 5`, carried (before its limbs are masked). -/
def g0' : Nat := VG.Proof.Poly1305.Limbs26.fc c M 0 + five
def g1' : Nat := VG.Proof.Poly1305.Limbs26.fc c M 1 + VG.Proof.Poly1305.Limbs26.g0' c M five / 2 ^ 26
def g2' : Nat := VG.Proof.Poly1305.Limbs26.fc c M 2 + VG.Proof.Poly1305.Limbs26.g1' c M five / 2 ^ 26
def g3' : Nat := VG.Proof.Poly1305.Limbs26.fc c M 3 + VG.Proof.Poly1305.Limbs26.g2' c M five / 2 ^ 26
def g4' : Nat := VG.Proof.Poly1305.Limbs26.fc c M 4 + VG.Proof.Poly1305.Limbs26.g3' c M five / 2 ^ 26
def gl : Nat → Nat
  | 0 => VG.Proof.Poly1305.Limbs26.g0' c M five
  | 1 => VG.Proof.Poly1305.Limbs26.g1' c M five
  | 2 => VG.Proof.Poly1305.Limbs26.g2' c M five
  | 3 => VG.Proof.Poly1305.Limbs26.g3' c M five
  | _ => VG.Proof.Poly1305.Limbs26.g4' c M five

/-- The select mask: `(g₄ >> 26) · mk`, as `vpmuludq` computes it. -/
def sel : Nat := VG.Proof.Poly1305.Limbs26.g4' c M five / 2 ^ 26 % 2 ^ 32 * (mk % 2 ^ 32)

/-- `h mod p`, limb by limb. -/
def fin (i : Nat) : Nat :=
  ((2 ^ 64 - 1 - VG.Proof.Poly1305.Limbs26.sel c M five mk) &&& VG.Proof.Poly1305.Limbs26.fc c M i) ||| (VG.Proof.Poly1305.Limbs26.gl c M five i &&& M &&& VG.Proof.Poly1305.Limbs26.sel c M five mk)

end

theorem and_high_zero {x : Nat} (hx : x < 2 ^ 27) : (2 ^ 64 - 1 - (2 ^ 27 - 1)) &&& x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < 27
  · rw [show 2 ^ 64 - 1 - (2 ^ 27 - 1) = (2 ^ 37 - 1) * 2 ^ 27 by decide, Nat.testBit_mul_two_pow,
      decide_eq_false (by omega), Bool.false_and, Bool.false_and]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.and_false]

theorem fin_val {c : Nat → Nat} (h0 : c 0 < 2 ^ 26) (h1 : c 1 < 2 ^ 27) (h2 : c 2 < 2 ^ 26)
    (h3 : c 3 < 2 ^ 26) (h4 : c 4 < 2 ^ 26) :
    VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.fin c 0x3ffffff 5 0x7ffffff) = VG.Proof.Poly1305.Limbs26.val c % P ∧ ∀ i < 5, VG.Proof.Poly1305.Limbs26.fin c 0x3ffffff 5 0x7ffffff i < 2 ^ 26 := by
  have ef : ∀ i < 5, VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff i = (if i = 0 then c 0 else if i = 1 then c 1 % 2 ^ 26
      else if i = 2 then VG.Proof.Poly1305.Limbs26.f2' c % 2 ^ 26 else if i = 3 then VG.Proof.Poly1305.Limbs26.f3' c % 2 ^ 26 else c 4 + VG.Proof.Poly1305.Limbs26.f3' c / 2 ^ 26) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.Poly1305.Limbs26.fc, VG.Proof.Poly1305.Limbs26.and_mask] <;> rfl
  have e2 : VG.Proof.Poly1305.Limbs26.f2' c = c 2 + c 1 / 2 ^ 26 := rfl
  have e3 : VG.Proof.Poly1305.Limbs26.f3' c = c 3 + VG.Proof.Poly1305.Limbs26.f2' c / 2 ^ 26 := rfl
  -- The limbs of `h` carried, and of `g = h + 5`.
  obtain ⟨F0, F1, F2, F3, F4⟩ : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 0 = c 0 ∧ VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 1 = c 1 % 2 ^ 26 ∧
      VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 2 = VG.Proof.Poly1305.Limbs26.f2' c % 2 ^ 26 ∧ VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 3 = VG.Proof.Poly1305.Limbs26.f3' c % 2 ^ 26 ∧
      VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 4 = c 4 + VG.Proof.Poly1305.Limbs26.f3' c / 2 ^ 26 :=
    ⟨ef 0 (by decide), ef 1 (by decide), ef 2 (by decide), ef 3 (by decide), ef 4 (by decide)⟩
  have R0 : VG.Proof.Poly1305.Limbs26.g0' c 0x3ffffff 5 = VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 0 + 5 := rfl
  have R1 : VG.Proof.Poly1305.Limbs26.g1' c 0x3ffffff 5 = VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 1 + VG.Proof.Poly1305.Limbs26.g0' c 0x3ffffff 5 / 2 ^ 26 := rfl
  have R2 : VG.Proof.Poly1305.Limbs26.g2' c 0x3ffffff 5 = VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 2 + VG.Proof.Poly1305.Limbs26.g1' c 0x3ffffff 5 / 2 ^ 26 := rfl
  have R3 : VG.Proof.Poly1305.Limbs26.g3' c 0x3ffffff 5 = VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 3 + VG.Proof.Poly1305.Limbs26.g2' c 0x3ffffff 5 / 2 ^ 26 := rfl
  have R4 : VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 = VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 4 + VG.Proof.Poly1305.Limbs26.g3' c 0x3ffffff 5 / 2 ^ 26 := rfl
  -- Bounds, one carry at a time.
  have bf2 : VG.Proof.Poly1305.Limbs26.f2' c < 2 ^ 26 + 2 := by rw [e2]; omega_using [h1, h2]
  have bf3 : VG.Proof.Poly1305.Limbs26.f3' c < 2 ^ 26 + 2 := by rw [e3]; omega_using [h3, bf2]
  have a0 : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 0 < 2 ^ 26 := by rw [F0]; exact h0
  have a1 : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 1 < 2 ^ 26 := by rw [F1]; omega_using []
  have a2 : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 2 < 2 ^ 26 := by rw [F2]; omega_using []
  have a3 : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 3 < 2 ^ 26 := by rw [F3]; omega_using []
  have a4 : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff 4 < 2 ^ 26 + 2 := by rw [F4]; omega_using [h4, bf3]
  have bg1 : VG.Proof.Poly1305.Limbs26.g1' c 0x3ffffff 5 < 2 ^ 26 + 1 := by omega_using [R1, R0, a0, a1]
  have bg2 : VG.Proof.Poly1305.Limbs26.g2' c 0x3ffffff 5 < 2 ^ 26 + 1 := by omega_using [R2, a2, bg1]
  have bg3 : VG.Proof.Poly1305.Limbs26.g3' c 0x3ffffff 5 < 2 ^ 26 + 1 := by omega_using [R3, a3, bg2]
  have bg4 : VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 < 2 ^ 27 := by omega_using [R4, a4, bg3]
  -- `val h` carried, and `val h + 5` in the limbs of `g`.
  have vfc : VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff) = VG.Proof.Poly1305.Limbs26.val c := by
    rw [VG.Proof.Poly1305.Limbs26.val, VG.Proof.Poly1305.Limbs26.val, F0, F1, F2, F3, F4]; omega_using [e2, e3]
  have hg : VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff) + 5 = VG.Proof.Poly1305.Limbs26.g0' c 0x3ffffff 5 % 2 ^ 26 + 2 ^ 26 * (VG.Proof.Poly1305.Limbs26.g1' c 0x3ffffff 5 % 2 ^ 26) +
      2 ^ 52 * (VG.Proof.Poly1305.Limbs26.g2' c 0x3ffffff 5 % 2 ^ 26) + 2 ^ 78 * (VG.Proof.Poly1305.Limbs26.g3' c 0x3ffffff 5 % 2 ^ 26) +
      2 ^ 104 * VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 := by
    rw [VG.Proof.Poly1305.Limbs26.val]; omega_using [R0, R1, R2, R3, R4]
  have gl_eq : ∀ i < 5, VG.Proof.Poly1305.Limbs26.gl c 0x3ffffff 5 i &&& 0x3ffffff = (if i = 0 then VG.Proof.Poly1305.Limbs26.g0' c 0x3ffffff 5
      else if i = 1 then VG.Proof.Poly1305.Limbs26.g1' c 0x3ffffff 5 else if i = 2 then VG.Proof.Poly1305.Limbs26.g2' c 0x3ffffff 5
      else if i = 3 then VG.Proof.Poly1305.Limbs26.g3' c 0x3ffffff 5 else VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5) % 2 ^ 26 := by
    intro i hi
    rw [VG.Proof.Poly1305.Limbs26.and_mask]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hs : VG.Proof.Poly1305.Limbs26.sel c 0x3ffffff 5 0x7ffffff = VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 / 2 ^ 26 * (2 ^ 27 - 1) := by
    rw [VG.Proof.Poly1305.Limbs26.sel, show (0x7ffffff : Nat) % 2 ^ 32 = 2 ^ 27 - 1 by decide]
    congr 1
    omega_using [bg4]
  have hq : VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 / 2 ^ 26 = 0 ∨ VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 / 2 ^ 26 = 1 := by omega_using [bg4]
  have fin_eq : ∀ i < 5, VG.Proof.Poly1305.Limbs26.fin c 0x3ffffff 5 0x7ffffff i =
      if VG.Proof.Poly1305.Limbs26.g4' c 0x3ffffff 5 / 2 ^ 26 = 0 then VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff i else VG.Proof.Poly1305.Limbs26.gl c 0x3ffffff 5 i &&& 0x3ffffff := by
    intro i hi
    have hf : VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff i < 2 ^ 27 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · omega_using [a0]
      · omega_using [a1]
      · omega_using [a2]
      · omega_using [a3]
      · omega_using [a4]
    rw [VG.Proof.Poly1305.Limbs26.fin, hs]
    rcases hq with hq | hq <;> rw [hq]
    · simp only [Nat.zero_mul, Nat.sub_zero, Nat.and_zero, Nat.or_zero, ite_true]
      rw [show (2 ^ 64 - 1 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_comm,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.lt_trans hf (by decide))]
    · simp only [Nat.one_mul, VG.Proof.Poly1305.Limbs26.and_high_zero hf, Nat.zero_or, show (1 : Nat) ≠ 0 by decide, ite_false]
      rw [Nat.and_two_pow_sub_one_eq_mod, VG.Proof.Poly1305.Limbs26.and_mask]
      omega_using []
  rcases hq with hq | hq
  · have e : ∀ i < 5, VG.Proof.Poly1305.Limbs26.fin c 0x3ffffff 5 0x7ffffff i = VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff i := fun i hi => by
      rw [fin_eq i hi, ite_eq_left hq]
    refine ⟨?_, fun i hi => ?_⟩
    · have hv : VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.fin c 0x3ffffff 5 0x7ffffff) = VG.Proof.Poly1305.Limbs26.val (VG.Proof.Poly1305.Limbs26.fc c 0x3ffffff) := by
        unfold VG.Proof.Poly1305.Limbs26.val; rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)]
      rw [hv, ← vfc, Nat.mod_eq_of_lt (by rw [VG.Proof.Poly1305.Limbs26.P_eq]; omega_using [hg, hq])]
    · rw [e i hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      exacts [a0, a1, a2, a3, by omega_using [R4, hq]]
  · have e : ∀ i < 5, VG.Proof.Poly1305.Limbs26.fin c 0x3ffffff 5 0x7ffffff i = VG.Proof.Poly1305.Limbs26.gl c 0x3ffffff 5 i &&& 0x3ffffff := fun i hi => by
      rw [fin_eq i hi, ite_eq_right (by omega)]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [VG.Proof.Poly1305.Limbs26.val, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
        gl_eq 0 (by decide), gl_eq 1 (by decide), gl_eq 2 (by decide), gl_eq 3 (by decide),
        gl_eq 4 (by decide)]
      simp only [ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (3 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide,
        show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 3 by decide]
      rw [← vfc, VG.Proof.Poly1305.Limbs26.P_eq]
      unfold VG.Proof.Poly1305.Limbs26.val at hg ⊢
      omega_using [hg, hq, a0, a1, a2, a3, a4]
    · rw [e i hi, VG.Proof.Poly1305.Limbs26.and_mask]; omega_using []

/-! ## Words -/

section
variable (o : Nat → Nat)

/-- The three words of `h`, as `storeH` computes them. -/
def w0 : Nat := o 1 * 2 ^ 26 % 2 ^ 64 ||| o 0 ||| o 2 * 2 ^ 52 % 2 ^ 64
def w1 : Nat := o 2 / 2 ^ 12 ||| o 3 * 2 ^ 14 % 2 ^ 64 ||| o 4 * 2 ^ 40 % 2 ^ 64

end

theorem words_val {o : Nat → Nat} (h : ∀ i < 5, o i < 2 ^ 26) :
    VG.Proof.Poly1305.Limbs26.w0 o + 2 ^ 64 * VG.Proof.Poly1305.Limbs26.w1 o + 2 ^ 128 * (o 4 / 2 ^ 24) = VG.Proof.Poly1305.Limbs26.val o ∧ VG.Proof.Poly1305.Limbs26.w0 o < 2 ^ 64 ∧ VG.Proof.Poly1305.Limbs26.w1 o < 2 ^ 64 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have e0 : VG.Proof.Poly1305.Limbs26.w0 o = 2 ^ 52 * (o 2 % 2 ^ 12) + (2 ^ 26 * o 1 + o 0) := by
    have a1 : (o 1 * 2 ^ 26 % 2 ^ 64 ||| o 0) = 2 ^ 26 * o 1 + o 0 := by
      rw [show o 1 * 2 ^ 26 % 2 ^ 64 = 2 ^ 26 * o 1 by omega]
      exact (Nat.two_pow_add_eq_or_of_lt h0 _).symm
    rw [VG.Proof.Poly1305.Limbs26.w0, a1, show o 2 * 2 ^ 52 % 2 ^ 64 = 2 ^ 52 * (o 2 % 2 ^ 12) by omega, Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  have e1 : VG.Proof.Poly1305.Limbs26.w1 o = 2 ^ 40 * (o 4 % 2 ^ 24) + (2 ^ 14 * o 3 + o 2 / 2 ^ 12) := by
    have b1 : (o 2 / 2 ^ 12 ||| o 3 * 2 ^ 14 % 2 ^ 64) = 2 ^ 14 * o 3 + o 2 / 2 ^ 12 := by
      rw [show o 3 * 2 ^ 14 % 2 ^ 64 = 2 ^ 14 * o 3 by omega, Nat.or_comm]
      exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
    rw [VG.Proof.Poly1305.Limbs26.w1, b1, show o 4 * 2 ^ 40 % 2 ^ 64 = 2 ^ 40 * (o 4 % 2 ^ 24) by omega, Nat.or_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (by omega) _).symm
  simp only [e0, e1, VG.Proof.Poly1305.Limbs26.val]
  omega

end VG.Proof.Poly1305.Limbs26

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Stream`. -/
section

/-!
# Poly1305: the streaming state, for every target

Counters, bytes written to memory, and a message with its last bytes buffered
(`Buffered`) as its whole blocks and the rest.
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (bytesAt Repr Buffered)

/-! ## Counters -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, VG.Proof.Poly1305.ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-! ## Bytes in memory -/

export VG.WriteBytes (writeBytes writeBytes_nil writeW8_apply writeBytes_snoc writeBytes_before
  writeBytes_frame)

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact VG.WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, VG.WriteBytes.writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-! ## Whole blocks and the rest -/

theorem take_whole {a b : List Byte} (ha : a.length % 16 = 0) (hb : b.length < 16) :
    (a ++ b).take (16 * ((a ++ b).length / 16)) = a := by
  rw [show 16 * ((a ++ b).length / 16) = a.length by simp only [List.length_append]; omega,
    List.take_left' rfl]

theorem drop_whole {a b : List Byte} (ha : a.length % 16 = 0) (hb : b.length < 16) :
    (a ++ b).drop (16 * ((a ++ b).length / 16)) = b := by
  rw [show 16 * ((a ++ b).length / 16) = a.length by simp only [List.length_append]; omega,
    List.drop_left' rfl]

/-- A message with its last bytes buffered: its whole blocks, which the
state represents as `Repr` does, and the buffered bytes. -/
theorem Buffered.split {m : Mem} {st : Addr} {key msg : List Byte} (h : Buffered m st key msg) :
    ∃ w b, msg = w ++ b ∧ Repr m st key w ∧ b.length = msg.length % 16 ∧
      bytesAt m (st + 56) (msg.length % 16) = b :=
  ⟨_, _, (List.take_append_drop _ _).symm, h.1, by simp only [List.length_drop]; omega, h.2⟩

theorem Buffered.of {m : Mem} {st : Addr} {key w b : List Byte} (hr : Repr m st key w) (hb : b.length < 16)
    (hbuf : bytesAt m (st + 56) b.length = b) : Buffered m st key (w ++ b) := by
  have hw := hr.1
  refine ⟨by rw [VG.Proof.Poly1305.take_whole hw hb]; exact hr, ?_⟩
  rw [VG.Proof.Poly1305.drop_whole hw hb, show (w ++ b).length % 16 = b.length by simp only [List.length_append]; omega]
  exact hbuf

/-- A message of whole blocks, with nothing buffered. -/
theorem Repr.buffered {m : Mem} {st : Addr} {key msg : List Byte} (h : Repr m st key msg) :
    Buffered m st key msg := by
  have e := Buffered.of (b := []) h (by simp) rfl
  rwa [List.append_nil] at e

end VG.Proof.Poly1305

end
