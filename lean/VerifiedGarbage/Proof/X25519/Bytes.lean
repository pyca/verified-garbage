import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Tactic.SplitIfs

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Field`. -/
section

/-!
# X25519: field elements as natural numbers

Implementations compute with natural numbers (the limbs of a field element, as
any number standing for its residue modulo `p`); `toFe` reads one as an
element of `GF(p)`, and the lemmas here turn what an implementation proves
about its numbers (modulo `p`) into the operations of `Spec/X25519.lean`, in
the order the spec writes them.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- A natural number as an element of `GF(p)`: its residue. -/
def toFe (x : Nat) : Fe := Fin.ofNat P x

theorem toFe_val (x : Nat) : (VG.Proof.X25519.toFe x).val = x % P := rfl

theorem toFe_eq_iff {a b : Nat} : VG.Proof.X25519.toFe a = VG.Proof.X25519.toFe b ↔ a % P = b % P := Fin.ext_iff

theorem toFe_congr {a b : Nat} (h : a % P = b % P) : VG.Proof.X25519.toFe a = VG.Proof.X25519.toFe b := toFe_eq_iff.2 h

theorem toFe_self (x : Fe) : VG.Proof.X25519.toFe x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem toFe_mod (x : Nat) : VG.Proof.X25519.toFe (x % P) = VG.Proof.X25519.toFe x := VG.Proof.X25519.toFe_congr (Nat.mod_mod _ _)

theorem toFe_mul {a b c : Nat} (h : c % P = a * b % P) : VG.Proof.X25519.toFe c = VG.Proof.X25519.toFe a * VG.Proof.X25519.toFe b := by
  apply Fin.ext
  show c % P = (a % P) * (b % P) % P
  rw [h, Nat.mul_mod]

theorem toFe_add {a b c : Nat} (h : c % P = (a + b) % P) : VG.Proof.X25519.toFe c = VG.Proof.X25519.toFe a + VG.Proof.X25519.toFe b := by
  apply Fin.ext
  show c % P = (a % P + b % P) % P
  rw [h, Nat.add_mod]

/-- A difference: `c + b ≡ a`. -/
theorem toFe_sub {a b c : Nat} (h : (c + b) % P = a % P) : VG.Proof.X25519.toFe c = VG.Proof.X25519.toFe a - VG.Proof.X25519.toFe b := by
  apply Fin.ext
  show c % P = ((P - b % P) + a % P) % P
  have hx : c % P < P := Nat.mod_lt _ (by decide)
  have hy : b % P < P := Nat.mod_lt _ (by decide)
  rw [← h, Nat.add_mod c b]
  generalize c % P = x at *
  generalize b % P = y at *
  rcases Nat.lt_or_ge (x + y) P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, show P - y + (x + y) = x + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]
  · rw [show (x + y) % P = x + y - P by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)],
      show P - y + (x + y - P) = x by omega, Nat.mod_eq_of_lt hx]

/-- A multiplication by `a24`, written as the spec writes it. -/
theorem toFe_a24 {a c : Nat} (h : c % P = 121665 * a % P) : VG.Proof.X25519.toFe c = a24 * VG.Proof.X25519.toFe a := by
  apply Fin.ext
  show c % P = (121665 % P) * (a % P) % P
  rw [h, Nat.mul_mod]

theorem toFe_zero : VG.Proof.X25519.toFe 0 = 0 := rfl
theorem toFe_one : VG.Proof.X25519.toFe 1 = 1 := rfl

/-- `2²⁵⁶ ≡ 38` modulo `p`: the top of a 512-bit product folds into its
bottom times 38. -/
theorem fold256 (lo hi : Nat) : (lo + 2 ^ 256 * hi) % P = (lo + 38 * hi) % P := by
  rw [show lo + 2 ^ 256 * hi = lo + 38 * hi + P * (2 * hi) by simp only [P]; omega,
    Nat.add_mul_mod_self_left]

/-- `2²⁵⁵ ≡ 19` modulo `p`. -/
theorem fold255 (lo hi : Nat) : (lo + 2 ^ 255 * hi) % P = (lo + 19 * hi) % P := by
  rw [show lo + 2 ^ 255 * hi = lo + 19 * hi + P * hi by simp only [P]; omega,
    Nat.add_mul_mod_self_left]

end VG.Proof.X25519

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Invert`. -/
section

/-!
# X25519: the inversion `z^(p-2)` as an addition chain

`invert`, the addition chain of ref10's `fe_invert` (254 squarings and 11
multiplications, in the order implementations compute them), is the spec's
`pow z (p-2)`, shown on the residues (`pw z e`, the residue of `z^e`), without
Mathlib's ring structure on `Fin p`. An implementation of the chain is proven
against `invert`, one multiplication or run of squarings (`sqn`) at a time.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- `x` squared `n` times: `x^(2^n)`. -/
def sqn (x : Fe) : Nat → Fe
  | 0 => x
  | n + 1 => VG.Proof.X25519.sqn x n * VG.Proof.X25519.sqn x n

theorem sqn_succ' (x : Fe) (n : Nat) : VG.Proof.X25519.sqn x (n + 1) = VG.Proof.X25519.sqn (x * x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X25519.sqn, ih, VG.Proof.X25519.sqn]

/-- ref10's `fe_invert(z)`: the exponents of `z` in the comments. -/
def invert (z : Fe) : Fe :=
  let t0 := z * z                 -- 2
  let t1 := VG.Proof.X25519.sqn t0 2              -- 8
  let t1 := z * t1                -- 9
  let t0 := t0 * t1               -- 11
  let t2 := t0 * t0               -- 22
  let t1 := t1 * t2               -- 31 = 2^5 - 1
  let t2 := VG.Proof.X25519.sqn t1 5
  let t1 := t2 * t1               -- 2^10 - 1
  let t2 := VG.Proof.X25519.sqn t1 10
  let t2 := t2 * t1               -- 2^20 - 1
  let t3 := VG.Proof.X25519.sqn t2 20
  let t2 := t3 * t2               -- 2^40 - 1
  let t2 := VG.Proof.X25519.sqn t2 10
  let t1 := t2 * t1               -- 2^50 - 1
  let t2 := VG.Proof.X25519.sqn t1 50
  let t2 := t2 * t1               -- 2^100 - 1
  let t3 := VG.Proof.X25519.sqn t2 100
  let t2 := t3 * t2               -- 2^200 - 1
  let t2 := VG.Proof.X25519.sqn t2 50
  let t1 := t2 * t1               -- 2^250 - 1
  let t1 := VG.Proof.X25519.sqn t1 5
  t1 * t0                         -- 2^255 - 21 = p - 2

/-- `z^e`, computed on the residue. -/
def pw (z : Fe) (e : Nat) : Fe := Fin.ofNat P (z.val ^ e)

theorem pw_one (z : Fe) : VG.Proof.X25519.pw z 1 = z :=
  Fin.ext (by simp only [VG.Proof.X25519.pw, Fin.val_ofNat, Nat.pow_one, Nat.mod_eq_of_lt z.isLt])

theorem pw_zero (z : Fe) : VG.Proof.X25519.pw z 0 = 1 := by
  show Fin.ofNat P (z.val ^ 0) = 1
  rw [Nat.pow_zero]
  rfl

theorem pw_mul (z : Fe) (a b : Nat) : VG.Proof.X25519.pw z a * VG.Proof.X25519.pw z b = VG.Proof.X25519.pw z (a + b) :=
  Fin.ext (by simp only [VG.Proof.X25519.pw, Fin.val_mul, Fin.val_ofNat, Nat.pow_add, ← Nat.mul_mod])

theorem pw_sq (z : Fe) (a : Nat) : VG.Proof.X25519.pw (z * z) a = VG.Proof.X25519.pw z (2 * a) :=
  Fin.ext (by simp only [VG.Proof.X25519.pw, Fin.val_mul, Fin.val_ofNat, ← Nat.pow_mod, Nat.pow_mul, Nat.pow_two])

theorem sqn_pw (z : Fe) (a n : Nat) : VG.Proof.X25519.sqn (VG.Proof.X25519.pw z a) n = VG.Proof.X25519.pw z (a * 2 ^ n) := by
  induction n with
  | zero => rw [VG.Proof.X25519.sqn, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [VG.Proof.X25519.sqn, ih, VG.Proof.X25519.pw_mul, Nat.pow_succ, Nat.mul_two, Nat.mul_add]

theorem pow_pw (a : Fe) (e : Nat) : pow a e = VG.Proof.X25519.pw a e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [pow]
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, h0]
      exact Fin.ext (by simp only [VG.Proof.X25519.pw, Fin.val_ofNat, Nat.pow_zero]; rfl)
    · simp only [h0, ite_false]
      rw [ih (e / 2) (by omega), VG.Proof.X25519.pw_sq]
      by_cases h : e % 2 = 0
      · rw [ite_eq_left h]; exact congrArg (VG.Proof.X25519.pw a) (by omega)
      · rw [ite_eq_right h, ← congrArg (· * _) (VG.Proof.X25519.pw_one a), VG.Proof.X25519.pw_mul]
        exact congrArg (VG.Proof.X25519.pw a) (by omega)

theorem invert_eq (z : Fe) : VG.Proof.X25519.invert z = pow z (P - 2) := by
  rw [VG.Proof.X25519.pow_pw, ← congrArg VG.Proof.X25519.invert (VG.Proof.X25519.pw_one z)]
  simp only [VG.Proof.X25519.invert, VG.Proof.X25519.pw_mul, VG.Proof.X25519.sqn_pw]
  exact congrArg (VG.Proof.X25519.pw z) (by decide)

end VG.Proof.X25519

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Ladder`. -/
section

/-!
# X25519: the ladder one iteration at a time

`X25519` of the spec folds `ladderStep` over the bits `254, …, 0` of the
scalar; implementations loop over them with a counter. `ladderAfter k x1 n` is
the ladder's state after the iterations for the bits `254` down to `n` (so
`ladderAfter k x1 255` is the initial state and `ladderAfter k x1 0` the final
one), and each iteration takes it from `n + 1` to `n` (`ladderAfter_step`).
`x25519_eq` states the spec with it, and with the inversion as `invert`.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- The ladder's initial state, for `x_1 = u`. -/
def init (u : Fe) : Ladder := { x2 := 1, z2 := 0, x3 := u, z3 := 1, swap := 0 }

/-- The ladder's state after the iterations for the bits `254` down to `n`. -/
def ladderAfter (k : Nat) (x1 : Fe) (n : Nat) : Ladder :=
  ((List.range 255).reverse.take (255 - n)).foldl (ladderStep k x1) (VG.Proof.X25519.init x1)

theorem ladderAfter_255 (k : Nat) (x1 : Fe) : VG.Proof.X25519.ladderAfter k x1 255 = VG.Proof.X25519.init x1 := rfl

theorem take_reverse_range {n : Nat} (hn : n < 255) :
    (List.range 255).reverse.take (255 - n) = (List.range 255).reverse.take (255 - (n + 1)) ++ [n] := by
  rw [show 255 - n = 255 - (n + 1) + 1 by omega, List.take_add_one]
  congr
  rw [List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp only [List.length_range, Option.toList_some, List.cons.injEq, and_true]
  omega

theorem ladderAfter_step (k : Nat) (x1 : Fe) {n : Nat} (hn : n < 255) :
    VG.Proof.X25519.ladderAfter k x1 n = ladderStep k x1 (VG.Proof.X25519.ladderAfter k x1 (n + 1)) n := by
  rw [VG.Proof.X25519.ladderAfter, VG.Proof.X25519.take_reverse_range hn, List.foldl_append]
  rfl

theorem ladderAfter_zero (k : Nat) (x1 : Fe) :
    VG.Proof.X25519.ladderAfter k x1 0 = (List.range 255).reverse.foldl (ladderStep k x1) (VG.Proof.X25519.init x1) := by
  rw [VG.Proof.X25519.ladderAfter, Nat.sub_zero, List.take_of_length_le (by simp)]

/-- `k_t`, the bit `t` of the scalar. -/
def bit (k t : Nat) : Nat := (k >>> t) &&& 1

theorem bit_le (k t : Nat) : VG.Proof.X25519.bit k t ≤ 1 := by
  simp only [VG.Proof.X25519.bit]; exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : 1 < 2 ^ 1))

theorem ladderAfter_swap_le (k : Nat) (x1 : Fe) {n : Nat} (hn : n ≤ 255) :
    (VG.Proof.X25519.ladderAfter k x1 n).swap ≤ 1 := by
  rcases Nat.lt_or_ge n 255 with h | h
  · rw [VG.Proof.X25519.ladderAfter_step k x1 h]; exact VG.Proof.X25519.bit_le k n
  · rw [show n = 255 by omega]; exact Nat.zero_le _

/-- One iteration, spelled out: the new `swap` and the swaps by it, then the
formulas. -/
theorem ladderStep_eq (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ladderStep k x1 st t =
      let s := st.swap ^^^ VG.Proof.X25519.bit k t
      let x2 := (cswap s st.x2 st.x3).1
      let x3 := (cswap s st.x2 st.x3).2
      let z2 := (cswap s st.z2 st.z3).1
      let z3 := (cswap s st.z2 st.z3).2
      let A := x2 + z2
      let AA := A * A
      let B := x2 - z2
      let BB := B * B
      let E := AA - BB
      let C := x3 + z3
      let D := x3 - z3
      let DA := D * A
      let CB := C * B
      { x2 := AA * BB, z2 := E * (AA + a24 * E), x3 := (DA + CB) * (DA + CB),
        z3 := x1 * ((DA - CB) * (DA - CB)), swap := VG.Proof.X25519.bit k t } := rfl

/-- `X25519` with the ladder's final state and `invert`. -/
theorem x25519_eq (kb ub : List Byte) :
    x25519 kb ub =
      let k := decodeScalar25519 kb
      let st := VG.Proof.X25519.ladderAfter k (VG.Proof.X25519.toFe (decodeUCoordinate ub)) 0
      encodeUCoordinate ((cswap st.swap st.x2 st.x3).1 * VG.Proof.X25519.invert (cswap st.swap st.z2 st.z3).1) := by
  simp only [VG.Proof.X25519.invert_eq, VG.Proof.X25519.ladderAfter_zero]
  rfl

end VG.Proof.X25519

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Bytes`. -/
section

/-!
# X25519: byte strings, numbers and words

The encodings of RFC 7748 §5 as little-endian numbers of byte strings
(`leNum`) and byte strings of numbers (`leBytes`), and in memory as 64-bit or
32-bit words: the decoded u-coordinate is the number of its bytes modulo
`2²⁵⁵`, each bit of the decoded scalar a bit of one of its bytes (or fixed by
the clamping), and the encoded result the bytes of its value.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- The little-endian number of a byte string. -/
def leNum : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * VG.Proof.X25519.leNum bs

/-- The `n` least significant bytes of `x`, in little-endian order. -/
def leBytes (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

theorem leNum_append (a b : List Byte) : VG.Proof.X25519.leNum (a ++ b) = VG.Proof.X25519.leNum a + 256 ^ a.length * VG.Proof.X25519.leNum b := by
  induction a with
  | nil => simp [VG.Proof.X25519.leNum]
  | cons x xs ih =>
    simp only [List.cons_append, VG.Proof.X25519.leNum, ih, List.length_cons, Nat.pow_succ, Nat.mul_add,
      Nat.add_assoc, Nat.mul_comm _ 256, Nat.mul_assoc]

theorem leNum_lt (a : List Byte) : VG.Proof.X25519.leNum a < 256 ^ a.length := by
  induction a with
  | nil => simp [VG.Proof.X25519.leNum]
  | cons x xs ih =>
    simp only [VG.Proof.X25519.leNum, List.length_cons, Nat.pow_succ]
    have := x.isLt
    omega

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
    VG.Proof.X25519.leNum (bytesAt m p n) = (m.read p n).toNat := by
  induction n generalizing p with
  | zero => simp [bytesAt, VG.Proof.X25519.leNum, Mem.read]
  | succ n ih =>
    rw [VG.Proof.X25519.bytesAt_succ, VG.Proof.X25519.leNum, ih, Mem.read, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

theorem leNum_bytesAt_64 (m : Mem) (p : Addr) : VG.Proof.X25519.leNum (bytesAt m p 8) = (m.readW p 64).toNat := by
  rw [VG.Proof.X25519.leNum_bytesAt_read]
  simp [Mem.readW]

theorem leNum_bytesAt_32bit (m : Mem) (p : Addr) : VG.Proof.X25519.leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [VG.Proof.X25519.leNum_bytesAt_read]
  simp [Mem.readW]

/-- A number stored as four little-endian 64-bit words. -/
theorem leNum_bytesAt_words64 (m : Mem) (p : Addr) :
    VG.Proof.X25519.leNum (bytesAt m p 32) = (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat +
      2 ^ 128 * (m.readW (p + 16) 64).toNat + 2 ^ 192 * (m.readW (p + 24) 64).toNat := by
  rw [show 32 = 8 + (8 + (8 + 8)) from rfl, VG.Proof.X25519.bytesAt_add, VG.Proof.X25519.bytesAt_add, VG.Proof.X25519.bytesAt_add, VG.Proof.X25519.leNum_append,
    VG.Proof.X25519.leNum_append, VG.Proof.X25519.leNum_append, VG.Proof.X25519.length_bytesAt, VG.Proof.X25519.length_bytesAt, VG.Proof.X25519.length_bytesAt, VG.Proof.X25519.leNum_bytesAt_64,
    VG.Proof.X25519.leNum_bytesAt_64, VG.Proof.X25519.leNum_bytesAt_64, VG.Proof.X25519.leNum_bytesAt_64, BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_assoc]
  show (m.readW p 64).toNat + 256 ^ 8 * ((m.readW (p + 8) 64).toNat +
    256 ^ 8 * ((m.readW (p + 16) 64).toNat + 256 ^ 8 * (m.readW (p + 24) 64).toNat)) = _
  omega

/-- A number stored as eight little-endian 32-bit words. -/
theorem leNum_bytesAt_words32 (m : Mem) (p : Addr) :
    VG.Proof.X25519.leNum (bytesAt m p 32) = (m.readW p 32).toNat + 2 ^ 32 * (m.readW (p + 4) 32).toNat +
      2 ^ 64 * (m.readW (p + 8) 32).toNat + 2 ^ 96 * (m.readW (p + 12) 32).toNat +
      2 ^ 128 * (m.readW (p + 16) 32).toNat + 2 ^ 160 * (m.readW (p + 20) 32).toNat +
      2 ^ 192 * (m.readW (p + 24) 32).toNat + 2 ^ 224 * (m.readW (p + 28) 32).toNat := by
  rw [show bytesAt m p 32 = bytesAt m p (4 + (4 + (4 + (4 + (4 + (4 + (4 + 4))))))) from rfl]
  simp only [VG.Proof.X25519.bytesAt_add, VG.Proof.X25519.leNum_append, VG.Proof.X25519.length_bytesAt, VG.Proof.X25519.leNum_bytesAt_32bit, BitVec.add_assoc]
  show (m.readW p 32).toNat + 256 ^ 4 * ((m.readW (p + 4) 32).toNat +
    256 ^ 4 * ((m.readW (p + 8) 32).toNat + 256 ^ 4 * ((m.readW (p + 12) 32).toNat +
    256 ^ 4 * ((m.readW (p + 16) 32).toNat + 256 ^ 4 * ((m.readW (p + 20) 32).toNat +
    256 ^ 4 * ((m.readW (p + 24) 32).toNat + 256 ^ 4 * (m.readW (p + 28) 32).toNat)))))) = _
  omega

/-! ## Numbers as bytes -/

theorem leBytes_add (a b x : Nat) :
    VG.Proof.X25519.leBytes (a + b) x = VG.Proof.X25519.leBytes a x ++ VG.Proof.X25519.leBytes b (x / 256 ^ a) := by
  simp only [VG.Proof.X25519.leBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem leBytes_mod (n x : Nat) : VG.Proof.X25519.leBytes n (x % 256 ^ n) = VG.Proof.X25519.leBytes n x := by
  simp only [VG.Proof.X25519.leBytes]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 256 ^ n = 256 ^ i * 256 ^ (n - i) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  rw [show (2 : Nat) ^ 8 = 256 from rfl]
  exact ⟨256 ^ (n - i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩

theorem leBytes_succ (n x : Nat) : VG.Proof.X25519.leBytes (n + 1) x = BitVec.ofNat 8 x :: VG.Proof.X25519.leBytes n (x / 256) := by
  rw [Nat.add_comm, VG.Proof.X25519.leBytes_add, Nat.pow_one]; simp [VG.Proof.X25519.leBytes]

theorem bytesAt_leBytes (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n = VG.Proof.X25519.leBytes n (m.read p n).toNat := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have e : (m.read p (n + 1)).toNat = (m.read (p + 1) n).toNat * 256 + (m p).toNat := by
      rw [Mem.read, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
        Nat.shiftLeft_eq]
    rw [VG.Proof.X25519.bytesAt_succ, VG.Proof.X25519.leBytes_succ, ih, e]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have := (m p).isLt
      omega
    · congr 1
      have := (m p).isLt
      omega

theorem bytesAt_leBytes_64 (m : Mem) (p : Addr) :
    bytesAt m p 8 = VG.Proof.X25519.leBytes 8 (m.readW p 64).toNat := by
  rw [VG.Proof.X25519.bytesAt_leBytes]; simp [Mem.readW]

/-- Four little-endian 64-bit words in memory are the 32 bytes of `x`, if they
are its four 64-bit digits. -/
theorem bytesAt_leBytes_words64 (m : Mem) (p : Addr) (x : Nat)
    (h₀ : (m.readW p 64).toNat = x % 2 ^ 64)
    (h₁ : (m.readW (p + 8) 64).toNat = x / 2 ^ 64 % 2 ^ 64)
    (h₂ : (m.readW (p + 16) 64).toNat = x / 2 ^ 128 % 2 ^ 64)
    (h₃ : (m.readW (p + 24) 64).toNat = x / 2 ^ 192 % 2 ^ 64) :
    bytesAt m p 32 = VG.Proof.X25519.leBytes 32 x := by
  have e := VG.Proof.X25519.leNum_bytesAt_words64 m p
  rw [VG.Proof.X25519.leNum_bytesAt_read, h₀, h₁, h₂, h₃] at e
  rw [VG.Proof.X25519.bytesAt_leBytes, e, ← VG.Proof.X25519.leBytes_mod 32 x]
  congr 1
  omega

/-- Eight little-endian 32-bit words in memory are the 32 bytes of `x`, if they
are its eight 32-bit digits. -/
theorem bytesAt_leBytes_words32 (m : Mem) (p : Addr) (x : Nat)
    (h : ∀ j < 8, (m.readW (p + BitVec.ofNat 64 (4 * j)) 32).toNat = x / 2 ^ (32 * j) % 2 ^ 32) :
    bytesAt m p 32 = VG.Proof.X25519.leBytes 32 x := by
  have e := VG.Proof.X25519.leNum_bytesAt_words32 m p
  have h0 : (m.readW p 32).toNat = x % 2 ^ 32 := by simpa using h 0 (by omega)
  have h1 : (m.readW (p + 4) 32).toNat = x / 2 ^ 32 % 2 ^ 32 := h 1 (by omega)
  have h2 : (m.readW (p + 8) 32).toNat = x / 2 ^ 64 % 2 ^ 32 := h 2 (by omega)
  have h3 : (m.readW (p + 12) 32).toNat = x / 2 ^ 96 % 2 ^ 32 := h 3 (by omega)
  have h4 : (m.readW (p + 16) 32).toNat = x / 2 ^ 128 % 2 ^ 32 := h 4 (by omega)
  have h5 : (m.readW (p + 20) 32).toNat = x / 2 ^ 160 % 2 ^ 32 := h 5 (by omega)
  have h6 : (m.readW (p + 24) 32).toNat = x / 2 ^ 192 % 2 ^ 32 := h 6 (by omega)
  have h7 : (m.readW (p + 28) 32).toNat = x / 2 ^ 224 % 2 ^ 32 := h 7 (by omega)
  rw [VG.Proof.X25519.leNum_bytesAt_read, h0, h1, h2, h3, h4, h5, h6, h7] at e
  rw [VG.Proof.X25519.bytesAt_leBytes, e, ← VG.Proof.X25519.leBytes_mod 32 x]
  congr 1
  omega

/-! ## The encodings of RFC 7748 -/

theorem leNum_take_succ (l : List Byte) (n : Nat) :
    VG.Proof.X25519.leNum (l.take (n + 1)) = VG.Proof.X25519.leNum (l.take n) + 256 ^ n * (l.getD n 0).toNat := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD]
  rcases h : l[n]? with _ | b
  · simp
  · have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
    rw [VG.Proof.X25519.leNum_append, List.length_take, Nat.min_eq_left (by omega)]
    simp [VG.Proof.X25519.leNum]

theorem decodeLittleEndian_eq (l : List Byte) : decodeLittleEndian l = VG.Proof.X25519.leNum (l.take 32) := by
  suffices h : ∀ n, ((List.range n).map fun i => (l.getD i 0).toNat <<< (8 * i)).sum =
      VG.Proof.X25519.leNum (l.take n) from h 32
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, VG.Proof.X25519.leNum_take_succ]
    simp only [Nat.shiftLeft_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.mul_comm 8, Nat.pow_mul]
    congr 1
    rw [Nat.mul_comm, ← Nat.pow_mul, Nat.mul_comm n, Nat.pow_mul]

/-- `encodeUCoordinate` is the 32 bytes of the value. -/
theorem encodeUCoordinate_eq (x : Fe) : encodeUCoordinate x = VG.Proof.X25519.leBytes 32 x.val := by
  simp only [encodeUCoordinate, VG.Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem take_32 {l : List Byte} (h : l.length = 32) : l.take 32 = l :=
  List.take_of_length_le (by omega)

/-- The decoded u-coordinate is the number of its 32 bytes modulo `2²⁵⁵`. -/
theorem decodeUCoordinate_eq {l : List Byte} (h : l.length = 32) :
    decodeUCoordinate l = VG.Proof.X25519.leNum l % 2 ^ 255 := by
  obtain ⟨l₀, b, rfl⟩ : ∃ l₀ b, l = l₀ ++ [b] := by
    obtain ⟨l₀, b, e⟩ := List.eq_nil_or_concat l |>.resolve_left (by intro e; simp [e] at h)
    exact ⟨l₀, b, by rw [e, List.concat_eq_append]⟩
  have h₀ : l₀.length = 31 := by simpa using h
  rw [decodeUCoordinate, VG.Proof.X25519.decodeLittleEndian_eq]
  rw [show (l₀ ++ [b]).getD 31 0 = b by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h₀]; rfl]
  rw [List.set_append_right _ _ (by omega), h₀, List.take_of_length_le (by simp [h₀]),
    VG.Proof.X25519.leNum_append, VG.Proof.X25519.leNum_append, h₀]
  simp only [Nat.sub_self, List.set_cons_zero, VG.Proof.X25519.leNum, BitVec.toNat_and]
  have hl := VG.Proof.X25519.leNum_lt l₀
  rw [h₀] at hl
  have hb := b.isLt
  rw [show (127 : BitVec 8).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A bit of a little-endian number is that bit of one of its bytes. -/
theorem leNum_bit (l : List Byte) (t : Nat) :
    (VG.Proof.X25519.leNum l >>> t) &&& 1 = ((l.getD (t / 8) 0).toNat >>> (t % 8)) &&& 1 := by
  induction l generalizing t with
  | nil => simp [VG.Proof.X25519.leNum]
  | cons b bs ih =>
    simp only [VG.Proof.X25519.leNum, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
    have hb := b.isLt
    rcases Nat.lt_or_ge t 8 with ht | ht
    · rw [Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, List.getD_cons_zero]
      rw [show 256 = 2 ^ t * 2 ^ (8 - t) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]]
      rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
      rw [show 2 ^ (8 - t) = 2 * 2 ^ (8 - t - 1) by rw [← Nat.pow_succ']; congr 1; omega]
      rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · have e := ih (t - 8)
      simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at e
      rw [show t / 8 = (t - 8) / 8 + 1 by omega, List.getD_cons_succ,
        show t % 8 = (t - 8) % 8 by omega, ← e]
      rw [show t = 8 + (t - 8) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
      rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt hb, Nat.zero_add]
      simp

/-- The bits of a byte masked with `248`. -/
theorem bit_and_248 : ∀ x < 256, ∀ r < 8,
    ((x &&& 248) >>> r) &&& 1 = if r < 3 then 0 else (x >>> r) &&& 1 := by decide +kernel

/-- The bits of a byte masked with `127` and then 64 set. -/
theorem bit_and_or_64 : ∀ x < 256, ∀ r < 7,
    (((x &&& 127) ||| 64) >>> r) &&& 1 = if r = 6 then 1 else (x >>> r) &&& 1 := by decide +kernel

theorem getD_set (l : List Byte) {i : Nat} (j : Nat) (a : Byte) (hi : i < l.length) :
    (l.set i a).getD j 0 = if i = j then a else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h
  · subst h; simp only [Option.getD_some]
  · rfl

/-- The bits `0, …, 254` of the decoded scalar: those of its bytes, but for the
clamped ones (bits 0–2 are 0, bit 254 is 1). -/
theorem scalar_bit {kb : List Byte} (h : kb.length = 32) {t : Nat} (ht : t < 255) :
    VG.Proof.X25519.bit (decodeScalar25519 kb) t =
      if t < 3 then 0 else if t = 254 then 1 else ((kb.getD (t / 8) 0).toNat >>> (t % 8)) &&& 1 := by
  simp only [decodeScalar25519, VG.Proof.X25519.bit, VG.Proof.X25519.decodeLittleEndian_eq]
  rw [List.take_of_length_le (by simp [h]), VG.Proof.X25519.leNum_bit,
    VG.Proof.X25519.getD_set _ _ _ (by simp [h]), VG.Proof.X25519.getD_set _ _ _ (by simp [h]), VG.Proof.X25519.getD_set _ _ _ (by simp [h])]
  rcases Nat.lt_or_ge t 8 with h8 | h8
  · rw [show t / 8 = 0 by omega, show t % 8 = t by omega]
    simp (disch := omega) only [ite_true, ite_eq_left, ite_eq_right]
    rw [BitVec.toNat_and, show (248 : BitVec 8).toNat = 248 from rfl,
      VG.Proof.X25519.bit_and_248 _ (kb.getD 0 0).isLt _ h8]
  · by_cases h31 : t / 8 = 31
    · rw [h31]
      simp (disch := omega) only [ite_true, ite_eq_right]
      rw [BitVec.toNat_or, BitVec.toNat_and, show (127 : BitVec 8).toNat = 127 from rfl,
        show (64 : BitVec 8).toNat = 64 from rfl, VG.Proof.X25519.bit_and_or_64 _ (kb.getD 31 0).isLt _ (by omega)]
      split_ifs <;> first | rfl | omega
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.X25519

end
