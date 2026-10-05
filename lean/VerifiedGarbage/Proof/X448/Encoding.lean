import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Spec.X448
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.X25519.Bytes
import Batteries.Tactic.Init
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.AddrArith

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Field`. -/
section

/-!
# X448: field elements as natural numbers

Implementations compute with natural numbers (the limbs of a field element, as
any number standing for its residue modulo `p`); `toFe` reads one as an
element of `GF(p)`, and the lemmas here turn what an implementation proves
about its numbers (modulo `p`) into the operations of `Spec/X448.lean`, in the
order the spec writes them.
-/

namespace VG.Proof.X448

open VG.Spec.X448

/-- A natural number as an element of `GF(p)`: its residue. -/
def toFe (x : Nat) : VG.Spec.X448.Fe := Fin.ofNat VG.Spec.X448.P x

theorem toFe_val (x : Nat) : (VG.Proof.X448.toFe x).val = x % VG.Spec.X448.P := rfl

theorem toFe_eq_iff {a b : Nat} : VG.Proof.X448.toFe a = VG.Proof.X448.toFe b ↔ a % VG.Spec.X448.P = b % VG.Spec.X448.P := Fin.ext_iff

theorem toFe_congr {a b : Nat} (h : a % VG.Spec.X448.P = b % VG.Spec.X448.P) : VG.Proof.X448.toFe a = VG.Proof.X448.toFe b := toFe_eq_iff.2 h

theorem toFe_self (x : VG.Spec.X448.Fe) : VG.Proof.X448.toFe x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem toFe_mod (x : Nat) : VG.Proof.X448.toFe (x % VG.Spec.X448.P) = VG.Proof.X448.toFe x := VG.Proof.X448.toFe_congr (Nat.mod_mod _ _)

theorem toFe_mul {a b c : Nat} (h : c % VG.Spec.X448.P = a * b % VG.Spec.X448.P) : VG.Proof.X448.toFe c = VG.Proof.X448.toFe a * VG.Proof.X448.toFe b := by
  apply Fin.ext
  show c % VG.Spec.X448.P = (a % VG.Spec.X448.P) * (b % VG.Spec.X448.P) % VG.Spec.X448.P
  rw [h, Nat.mul_mod]

theorem toFe_add {a b c : Nat} (h : c % VG.Spec.X448.P = (a + b) % VG.Spec.X448.P) : VG.Proof.X448.toFe c = VG.Proof.X448.toFe a + VG.Proof.X448.toFe b := by
  apply Fin.ext
  show c % VG.Spec.X448.P = (a % VG.Spec.X448.P + b % VG.Spec.X448.P) % VG.Spec.X448.P
  rw [h, Nat.add_mod]

/-- A difference: `c + b ≡ a`. -/
theorem toFe_sub {a b c : Nat} (h : (c + b) % VG.Spec.X448.P = a % VG.Spec.X448.P) : VG.Proof.X448.toFe c = VG.Proof.X448.toFe a - VG.Proof.X448.toFe b := by
  apply Fin.ext
  show c % VG.Spec.X448.P = ((VG.Spec.X448.P - b % VG.Spec.X448.P) + a % VG.Spec.X448.P) % VG.Spec.X448.P
  have hx : c % VG.Spec.X448.P < VG.Spec.X448.P := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne VG.Spec.X448.P))
  have hy : b % VG.Spec.X448.P < VG.Spec.X448.P := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne VG.Spec.X448.P))
  rw [← h, Nat.add_mod c b]
  generalize c % VG.Spec.X448.P = x at *
  generalize b % VG.Spec.X448.P = y at *
  rcases Nat.lt_or_ge (x + y) VG.Spec.X448.P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, show VG.Spec.X448.P - y + (x + y) = x + VG.Spec.X448.P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]
  · rw [show (x + y) % VG.Spec.X448.P = x + y - VG.Spec.X448.P by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)],
      show VG.Spec.X448.P - y + (x + y - VG.Spec.X448.P) = x by omega, Nat.mod_eq_of_lt hx]

/-- A multiplication by `a24`, written as the spec writes it. -/
theorem toFe_a24 {a c : Nat} (h : c % VG.Spec.X448.P = 39081 * a % VG.Spec.X448.P) : VG.Proof.X448.toFe c = VG.Spec.X448.a24 * VG.Proof.X448.toFe a :=
  VG.Proof.X448.toFe_mul h

theorem toFe_zero : VG.Proof.X448.toFe 0 = 0 := rfl
theorem toFe_one : VG.Proof.X448.toFe 1 = 1 := rfl

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Invert`. -/
section

/-!
# X448: the inversion `z^(p-2)` as an addition chain

An addition chain for `z^(2⁴⁴⁸ - 2²²⁴ - 3)`, with runs of squarings shared by
the targets. The chain first builds `z^(2²²² - 1)`, then its two final
factors.
-/

namespace VG.Proof.X448

open VG.Spec.X448

/-- `x` squared `n` times: `x^(2^n)`. -/
def sqn (x : VG.Spec.X448.Fe) : Nat → VG.Spec.X448.Fe
  | 0 => x
  | n + 1 => VG.Proof.X448.sqn x n * VG.Proof.X448.sqn x n

theorem sqn_succ' (x : VG.Spec.X448.Fe) (n : Nat) : VG.Proof.X448.sqn x (n + 1) = VG.Proof.X448.sqn (x * x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.sqn, ih, VG.Proof.X448.sqn]

/-- An addition chain for `z^(P - 2)`. The comments give the exponent
of each intermediate result. -/
def invert (z : VG.Spec.X448.Fe) : VG.Spec.X448.Fe :=
  let t2 := VG.Proof.X448.sqn z 1 * z            -- 2^2 - 1
  let t4 := VG.Proof.X448.sqn t2 2 * t2          -- 2^4 - 1
  let t8 := VG.Proof.X448.sqn t4 4 * t4          -- 2^8 - 1
  let t16 := VG.Proof.X448.sqn t8 8 * t8         -- 2^16 - 1
  let t32 := VG.Proof.X448.sqn t16 16 * t16      -- 2^32 - 1
  let t64 := VG.Proof.X448.sqn t32 32 * t32      -- 2^64 - 1
  let t128 := VG.Proof.X448.sqn t64 64 * t64     -- 2^128 - 1
  let t192 := VG.Proof.X448.sqn t128 64 * t64    -- 2^192 - 1
  let t208 := VG.Proof.X448.sqn t192 16 * t16    -- 2^208 - 1
  let t216 := VG.Proof.X448.sqn t208 8 * t8      -- 2^216 - 1
  let t220 := VG.Proof.X448.sqn t216 4 * t4      -- 2^220 - 1
  let t222 := VG.Proof.X448.sqn t220 2 * t2      -- 2^222 - 1
  let t223 := VG.Proof.X448.sqn t222 1 * z       -- 2^223 - 1
  VG.Proof.X448.sqn t223 225 * (VG.Proof.X448.sqn t222 2 * z)

/-- `z^e`, computed on the residue. -/
def pw (z : VG.Spec.X448.Fe) (e : Nat) : VG.Spec.X448.Fe := Fin.ofNat VG.Spec.X448.P (z.val ^ e)

theorem pw_one (z : VG.Spec.X448.Fe) : VG.Proof.X448.pw z 1 = z :=
  Fin.ext (by simp only [VG.Proof.X448.pw, Fin.val_ofNat, Nat.pow_one, Nat.mod_eq_of_lt z.isLt])

theorem pw_mul (z : VG.Spec.X448.Fe) (a b : Nat) : VG.Proof.X448.pw z a * VG.Proof.X448.pw z b = VG.Proof.X448.pw z (a + b) :=
  Fin.ext (by simp only [VG.Proof.X448.pw, Fin.val_mul, Fin.val_ofNat, Nat.pow_add, ← Nat.mul_mod])

theorem pw_sq (z : VG.Spec.X448.Fe) (a : Nat) : VG.Proof.X448.pw (z * z) a = VG.Proof.X448.pw z (2 * a) :=
  Fin.ext (by simp only [VG.Proof.X448.pw, Fin.val_mul, Fin.val_ofNat, ← Nat.pow_mod, Nat.pow_mul, Nat.pow_two])

theorem sqn_pw (z : VG.Spec.X448.Fe) (a n : Nat) : VG.Proof.X448.sqn (VG.Proof.X448.pw z a) n = VG.Proof.X448.pw z (a * 2 ^ n) := by
  induction n with
  | zero => rw [VG.Proof.X448.sqn, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [VG.Proof.X448.sqn, ih, VG.Proof.X448.pw_mul, Nat.pow_succ, Nat.mul_two, Nat.mul_add]

theorem pow_pw (a : VG.Spec.X448.Fe) (e : Nat) : VG.Spec.X448.pow a e = VG.Proof.X448.pw a e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [VG.Spec.X448.pow]
    by_cases h0 : e = 0
    · rw [ite_eq_left h0, h0]
      show (1 : VG.Spec.X448.Fe) = Fin.ofNat VG.Spec.X448.P (a.val ^ 0)
      rw [Nat.pow_zero]
      rfl
    · simp only [h0, ite_false]
      rw [ih (e / 2) (by omega), VG.Proof.X448.pw_sq]
      by_cases h : e % 2 = 0
      · rw [ite_eq_left h]; exact congrArg (VG.Proof.X448.pw a) (by omega)
      · rw [ite_eq_right h, ← congrArg (· * _) (VG.Proof.X448.pw_one a), VG.Proof.X448.pw_mul]
        exact congrArg (VG.Proof.X448.pw a) (by omega)

theorem invert_eq (z : VG.Spec.X448.Fe) : VG.Proof.X448.invert z = VG.Spec.X448.pow z (VG.Spec.X448.P - 2) := by
  rw [VG.Proof.X448.pow_pw, ← congrArg VG.Proof.X448.invert (VG.Proof.X448.pw_one z)]
  simp only [VG.Proof.X448.invert, VG.Proof.X448.pw_mul, VG.Proof.X448.sqn_pw]
  exact congrArg (VG.Proof.X448.pw z) (by decide +kernel)

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Ladder`. -/
section

/-!
# X448: the ladder one iteration at a time

`X448` of the spec folds `ladderStep` over the bits `447, …, 0` of the scalar;
implementations loop over them with a counter. `ladderAfter k x1 n` is the
ladder's state after the iterations for the bits `447` down to `n` (so
`ladderAfter k x1 448` is the initial state and `ladderAfter k x1 0` the final
one), and each iteration takes it from `n + 1` to `n` (`ladderAfter_step`).
`x448_eq` states the spec with it, and with the inversion as `invert`.
-/

namespace VG.Proof.X448

open VG.Spec.X448

/-- The ladder's initial state, for `x_1 = u`. -/
def init (u : VG.Spec.X448.Fe) : VG.Spec.X448.Ladder := { x2 := 1, z2 := 0, x3 := u, z3 := 1, swap := 0 }

/-- The ladder's state after the iterations for the bits `447` down to `n`. -/
def ladderAfter (k : Nat) (x1 : VG.Spec.X448.Fe) (n : Nat) : VG.Spec.X448.Ladder :=
  ((List.range 448).reverse.take (448 - n)).foldl (VG.Spec.X448.ladderStep k x1) (VG.Proof.X448.init x1)

theorem ladderAfter_448 (k : Nat) (x1 : VG.Spec.X448.Fe) : VG.Proof.X448.ladderAfter k x1 448 = VG.Proof.X448.init x1 := rfl

theorem take_reverse_range {n : Nat} (hn : n < 448) :
    (List.range 448).reverse.take (448 - n) = (List.range 448).reverse.take (448 - (n + 1)) ++ [n] := by
  rw [show 448 - n = 448 - (n + 1) + 1 by omega, List.take_add_one]
  congr
  rw [List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp only [List.length_range, Option.toList_some, List.cons.injEq, and_true]
  omega

theorem ladderAfter_step (k : Nat) (x1 : VG.Spec.X448.Fe) {n : Nat} (hn : n < 448) :
    VG.Proof.X448.ladderAfter k x1 n = VG.Spec.X448.ladderStep k x1 (VG.Proof.X448.ladderAfter k x1 (n + 1)) n := by
  rw [VG.Proof.X448.ladderAfter, VG.Proof.X448.take_reverse_range hn, List.foldl_append]
  rfl

theorem ladderAfter_zero (k : Nat) (x1 : VG.Spec.X448.Fe) :
    VG.Proof.X448.ladderAfter k x1 0 = (List.range 448).reverse.foldl (VG.Spec.X448.ladderStep k x1) (VG.Proof.X448.init x1) := by
  rw [VG.Proof.X448.ladderAfter, Nat.sub_zero, List.take_of_length_le (by simp)]

/-- `k_t`, the bit `t` of the scalar. -/
def bit (k t : Nat) : Nat := (k >>> t) &&& 1

theorem bit_le (k t : Nat) : VG.Proof.X448.bit k t ≤ 1 := by
  simp only [VG.Proof.X448.bit]; exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : 1 < 2 ^ 1))

theorem ladderAfter_swap_le (k : Nat) (x1 : VG.Spec.X448.Fe) {n : Nat} (hn : n ≤ 448) :
    (VG.Proof.X448.ladderAfter k x1 n).swap ≤ 1 := by
  rcases Nat.lt_or_ge n 448 with h | h
  · rw [VG.Proof.X448.ladderAfter_step k x1 h]; exact VG.Proof.X448.bit_le k n
  · rw [show n = 448 by omega]; exact Nat.zero_le _

/-- One iteration, spelled out: the new `swap` and the swaps by it, then the
formulas. -/
theorem ladderStep_eq (k : Nat) (x1 : VG.Spec.X448.Fe) (st : VG.Spec.X448.Ladder) (t : Nat) :
    VG.Spec.X448.ladderStep k x1 st t =
      let s := st.swap ^^^ VG.Proof.X448.bit k t
      let x2 := (VG.Spec.X448.cswap s st.x2 st.x3).1
      let x3 := (VG.Spec.X448.cswap s st.x2 st.x3).2
      let z2 := (VG.Spec.X448.cswap s st.z2 st.z3).1
      let z3 := (VG.Spec.X448.cswap s st.z2 st.z3).2
      let A := x2 + z2
      let AA := A * A
      let B := x2 - z2
      let BB := B * B
      let E := AA - BB
      let C := x3 + z3
      let D := x3 - z3
      let DA := D * A
      let CB := C * B
      { x2 := AA * BB, z2 := E * (AA + VG.Spec.X448.a24 * E), x3 := (DA + CB) * (DA + CB),
        z3 := x1 * ((DA - CB) * (DA - CB)), swap := VG.Proof.X448.bit k t } := rfl

/-- `X448` with the ladder's final state and `invert`. -/
theorem x448_eq (kb ub : List Byte) :
    x448 kb ub =
      let k := decodeScalar448 kb
      let st := VG.Proof.X448.ladderAfter k (VG.Proof.X448.toFe (VG.Spec.X448.decodeUCoordinate ub)) 0
      VG.Spec.X448.encodeUCoordinate ((VG.Spec.X448.cswap st.swap st.x2 st.x3).1 * VG.Proof.X448.invert (VG.Spec.X448.cswap st.swap st.z2 st.z3).1) := by
  simp only [VG.Proof.X448.invert_eq, VG.Proof.X448.ladderAfter_zero]
  rfl

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Bytes`. -/
section

/-!
# X448: byte encodings

The target-independent little-endian helpers are shared with X25519; the width
and clamping lemmas here are specific to X448.
-/

namespace VG.Proof.X448

open VG.Spec.X448

open VG.Proof.X25519 (leNum leBytes)

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b :=
  VG.Proof.X25519.bytesAt_add m p a b

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem leNum_bytesAt_read (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p n) = (m.read p n).toNat := VG.Proof.X25519.leNum_bytesAt_read m p n

theorem decodeLittleEndian_eq (l : List Byte) : decodeLittleEndian l = leNum (l.take 56) := by
  suffices h : ∀ n, ((List.range n).map fun i => (l.getD i 0).toNat <<< (8 * i)).sum =
      leNum (l.take n) from h 56
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, VG.Proof.X25519.leNum_take_succ]
    simp only [Nat.shiftLeft_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.mul_comm 8, Nat.pow_mul]
    congr 1
    rw [Nat.mul_comm, ← Nat.pow_mul, Nat.mul_comm n, Nat.pow_mul]

/-- `encodeUCoordinate` is the 56 bytes of the value. -/
theorem encodeUCoordinate_eq (x : Fe) : encodeUCoordinate x = leBytes 56 x.val := by
  simp only [encodeUCoordinate, leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem take_56 {l : List Byte} (h : l.length = 56) : l.take 56 = l :=
  List.take_of_length_le (by omega)

/-- X448 uses all 448 bits of the coordinate. -/
theorem decodeUCoordinate_eq {l : List Byte} (h : l.length = 56) :
    decodeUCoordinate l = leNum l := by
  rw [decodeUCoordinate, VG.Proof.X448.decodeLittleEndian_eq, VG.Proof.X448.take_56 h]

/-- The low two bits of the scalar are cleared. -/
theorem bit_and_252 : ∀ x < 256, ∀ r < 8,
    ((x &&& 252) >>> r) &&& 1 = if r < 2 then 0 else (x >>> r) &&& 1 := by decide +kernel

/-- Bit 447 is set, with the other bits in the last byte preserved. -/
theorem bit_or_128 : ∀ x < 256, ∀ r < 8,
    ((x ||| 128) >>> r) &&& 1 = if r = 7 then 1 else (x >>> r) &&& 1 := by decide +kernel

/-- The bits `0, …, 447` of the decoded scalar: those of its bytes, but for the
clamped ones (bits 0–1 are 0, bit 447 is 1). -/
theorem scalar_bit {kb : List Byte} (h : kb.length = 56) {t : Nat} (ht : t < 448) :
    VG.Proof.X448.bit (decodeScalar448 kb) t =
      if t < 2 then 0 else if t = 447 then 1 else ((kb.getD (t / 8) 0).toNat >>> (t % 8)) &&& 1 := by
  simp only [decodeScalar448, VG.Proof.X448.bit, VG.Proof.X448.decodeLittleEndian_eq]
  rw [List.take_of_length_le (by simp [h]), VG.Proof.X25519.leNum_bit,
    VG.Proof.X25519.getD_set _ _ _ (by simp [h]), VG.Proof.X25519.getD_set _ _ _ (by simp [h]), VG.Proof.X25519.getD_set _ _ _ (by simp [h])]
  rcases Nat.lt_or_ge t 8 with h8 | h8
  · rw [show t / 8 = 0 by omega, show t % 8 = t by omega]
    simp (disch := omega) only [ite_true, ite_eq_left, ite_eq_right]
    rw [BitVec.toNat_and, show (252 : BitVec 8).toNat = 252 from rfl,
      VG.Proof.X448.bit_and_252 _ (kb.getD 0 0).isLt _ h8]
  · by_cases h55 : t / 8 = 55
    · rw [h55]
      simp (disch := omega) only [ite_true, ite_eq_right]
      rw [BitVec.toNat_or, show (128 : BitVec 8).toNat = 128 from rfl, VG.Proof.X448.bit_or_128 _ (kb.getD 55 0).isLt _ (by omega)]
      split_ifs <;> omega
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]


end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Limbs`. -/
section

/-!
# X448: radix-2²⁸ arithmetic

The sixteen limbs of a field element, carries, and reduction using `2^448 =
2^224 + 1` modulo p. These lemmas do not depend on an instruction set.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def radix : Nat := 2 ^ 28
def full : Nat := VG.Proof.X448.radix ^ 16
def half : Nat := VG.Proof.X448.radix ^ 8

theorem full_eq : VG.Proof.X448.full = VG.Spec.X448.P + (VG.Proof.X448.half + 1) := by decide +kernel
theorem half_sq : VG.Proof.X448.half * VG.Proof.X448.half = VG.Proof.X448.full := by decide +kernel

/-- Read `n` limbs, lowest first. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X448.valN f n + VG.Proof.X448.radix ^ n * f n

theorem valN_succ (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.valN f (n + 1) = VG.Proof.X448.valN f n + VG.Proof.X448.radix ^ n * f n := rfl

theorem valN_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ i < n, f i = g i) : VG.Proof.X448.valN f n = VG.Proof.X448.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.valN, VG.Proof.X448.valN, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem valN_add (f g : Nat → Nat) (n : Nat) :
    VG.Proof.X448.valN (fun i => f i + g i) n = VG.Proof.X448.valN f n + VG.Proof.X448.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.valN, VG.Proof.X448.valN, VG.Proof.X448.valN, ih, Nat.mul_add]; omega

theorem valN_scale (c : Nat) (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.valN (fun i => c * f i) n = c * VG.Proof.X448.valN f n := by
  induction n with
  | zero => simp only [VG.Proof.X448.valN, Nat.mul_zero]
  | succ n ih => rw [VG.Proof.X448.valN, VG.Proof.X448.valN, ih, Nat.mul_add, Nat.mul_left_comm (VG.Proof.X448.radix ^ n) c]

theorem valN_split (f : Nat → Nat) (a b : Nat) :
    VG.Proof.X448.valN f (a + b) = VG.Proof.X448.valN f a + VG.Proof.X448.radix ^ a * VG.Proof.X448.valN (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, VG.Proof.X448.valN, Nat.mul_zero]
  | succ b ih => rw [Nat.add_succ, VG.Proof.X448.valN, VG.Proof.X448.valN, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < VG.Proof.X448.radix) :
    VG.Proof.X448.valN f n < VG.Proof.X448.radix ^ n := by
  induction n with
  | zero => simp only [VG.Proof.X448.valN, Nat.pow_zero]; decide
  | succ n ih =>
    have hn := h n (by omega)
    have hp := ih fun i hi => h i (by omega)
    have hm := Nat.mul_le_mul_left (VG.Proof.X448.radix ^ n) hn
    rw [Nat.mul_succ] at hm
    rw [VG.Proof.X448.valN, Nat.pow_succ]
    omega

/-- Changing one limb changes the value at that limb's weight. -/
theorem valN_update {f g : Nat → Nat} {n k v : Nat} (hk : k < n)
    (h : ∀ i < n, g i = if i = k then f i + v else f i) :
    VG.Proof.X448.valN g n = VG.Proof.X448.valN f n + VG.Proof.X448.radix ^ k * v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : k = n
    · subst k
      have he : VG.Proof.X448.valN g n = VG.Proof.X448.valN f n := VG.Proof.X448.valN_congr fun i hi => by
        rw [h i (by omega), ite_eq_right (by omega)]
      rw [VG.Proof.X448.valN, VG.Proof.X448.valN, he, h n (by omega), ite_eq_left rfl, Nat.mul_add]
      omega
    · rw [VG.Proof.X448.valN, VG.Proof.X448.valN, ih (by omega) (fun i hi => h i (by omega)),
        h n (by omega), ite_eq_right (Ne.symm hn)]
      omega

/-- The incoming carry at position `n`. -/
def carry (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n + VG.Proof.X448.carry f n) / VG.Proof.X448.radix

def digit (f : Nat → Nat) (i : Nat) : Nat := (f i + VG.Proof.X448.carry f i) % VG.Proof.X448.radix

theorem digit_lt (f : Nat → Nat) (i : Nat) : VG.Proof.X448.digit f i < VG.Proof.X448.radix :=
  Nat.mod_lt _ (by decide)

theorem pass_eq (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.valN (VG.Proof.X448.digit f) n + VG.Proof.X448.radix ^ n * VG.Proof.X448.carry f n = VG.Proof.X448.valN f n := by
  induction n with
  | zero => simp only [VG.Proof.X448.valN, VG.Proof.X448.carry, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (f n + VG.Proof.X448.carry f n) VG.Proof.X448.radix
    change VG.Proof.X448.digit f n + VG.Proof.X448.radix * VG.Proof.X448.carry f (n + 1) = f n + VG.Proof.X448.carry f n at hd
    rw [VG.Proof.X448.valN, VG.Proof.X448.valN, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hd,
      Nat.mul_add]
    omega

theorem carry_bound {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 62) :
    VG.Proof.X448.carry f n < 2 ^ 35 := by
  induction n with
  | zero => simp only [VG.Proof.X448.carry]; decide
  | succ n ih =>
    have hi := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    simp only [VG.Proof.X448.carry, VG.Proof.X448.radix]
    omega

/-- The carry-out folded into the normalized limbs at positions 0 and 8. -/
def folded (f : Nat → Nat) (i : Nat) : Nat :=
  VG.Proof.X448.digit f i + if i = 0 ∨ i = 8 then VG.Proof.X448.carry f 16 else 0

theorem folded_val (f : Nat → Nat) :
    VG.Proof.X448.valN (VG.Proof.X448.folded f) 16 = VG.Proof.X448.valN (VG.Proof.X448.digit f) 16 + (VG.Proof.X448.half + 1) * VG.Proof.X448.carry f 16 := by
  change VG.Proof.X448.valN (fun i => VG.Proof.X448.digit f i + if i = 0 ∨ i = 8 then VG.Proof.X448.carry f 16 else 0) 16 = _
  rw [VG.Proof.X448.valN_add]
  congr 1
  simp only [VG.Proof.X448.valN, VG.Proof.X448.half]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, or_true, or_false, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  grind

theorem fold_mod (lo hi : Nat) :
    (lo + VG.Proof.X448.full * hi) % VG.Spec.X448.P = (lo + (VG.Proof.X448.half + 1) * hi) % VG.Spec.X448.P := by
  rw [VG.Proof.X448.full_eq, Nat.add_mul, Nat.add_left_comm lo, Nat.add_comm (VG.Spec.X448.P * hi), Nat.add_mul_mod_self_left]

theorem folded_mod (f : Nat → Nat) : VG.Proof.X448.valN (VG.Proof.X448.folded f) 16 % VG.Spec.X448.P = VG.Proof.X448.valN f 16 % VG.Spec.X448.P := by
  rw [VG.Proof.X448.folded_val, ← VG.Proof.X448.fold_mod, ← VG.Proof.X448.pass_eq f 16]
  rfl

theorem folded_bound {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 62) :
    ∀ i < 16, VG.Proof.X448.folded f i < 2 ^ 62 := by
  have hc := VG.Proof.X448.carry_bound h
  intro i _
  have hd := VG.Proof.X448.digit_lt f i
  simp only [VG.Proof.X448.folded]
  split <;> simp only [VG.Proof.X448.radix] at hd <;> omega

/-- After two folds, no carry remains beyond the 448-bit field width. -/
theorem final_carry {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 62) :
    VG.Proof.X448.carry (VG.Proof.X448.folded (VG.Proof.X448.folded f)) 16 = 0 := by
  by_contra hn
  have hn : 1 ≤ VG.Proof.X448.carry (VG.Proof.X448.folded (VG.Proof.X448.folded f)) 16 := Nat.pos_of_ne_zero hn
  have c0 := VG.Proof.X448.carry_bound h
  have v0 := VG.Proof.X448.valN_lt (n := 16) (fun i _ => VG.Proof.X448.digit_lt f i)
  have v1 := VG.Proof.X448.valN_lt (n := 16) (fun i _ => VG.Proof.X448.digit_lt (VG.Proof.X448.folded f) i)
  have e1 := VG.Proof.X448.pass_eq (VG.Proof.X448.folded f) 16
  have e2 := VG.Proof.X448.pass_eq (VG.Proof.X448.folded (VG.Proof.X448.folded f)) 16
  rw [VG.Proof.X448.folded_val] at e1 e2
  change VG.Proof.X448.valN (VG.Proof.X448.digit f) 16 < VG.Proof.X448.full at v0
  change VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.folded f)) 16 < VG.Proof.X448.full at v1
  change VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.folded f)) 16 + VG.Proof.X448.full * VG.Proof.X448.carry (VG.Proof.X448.folded f) 16 = _ at e1
  change VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.folded (VG.Proof.X448.folded f))) 16 + VG.Proof.X448.full * VG.Proof.X448.carry (VG.Proof.X448.folded (VG.Proof.X448.folded f)) 16 = _ at e2
  have small : (VG.Proof.X448.half + 1) * (2 ^ 35 + 1) < VG.Proof.X448.full := by decide +kernel
  have c1 : VG.Proof.X448.carry (VG.Proof.X448.folded f) 16 ≤ 1 := by
    by_contra hc
    have hb := Nat.mul_le_mul_left (VG.Proof.X448.half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left VG.Proof.X448.full (show 2 ≤ VG.Proof.X448.carry (VG.Proof.X448.folded f) 16 from by omega)
    omega
  rcases Nat.eq_zero_or_pos (VG.Proof.X448.carry (VG.Proof.X448.folded f) 16) with hc | hc
  · rw [hc, Nat.mul_zero, Nat.add_zero] at e2
    have hp := Nat.mul_le_mul_left VG.Proof.X448.full hn
    omega
  · have hc : VG.Proof.X448.carry (VG.Proof.X448.folded f) 16 = 1 := by omega
    rw [hc, Nat.mul_one] at e1 e2
    have hb := Nat.mul_le_mul_left (VG.Proof.X448.half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left VG.Proof.X448.full hn
    omega

def normalized (f : Nat → Nat) : Nat → Nat := VG.Proof.X448.digit (VG.Proof.X448.folded (VG.Proof.X448.folded f))

theorem normalized_mod {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 62) :
    VG.Proof.X448.valN (VG.Proof.X448.normalized f) 16 % VG.Spec.X448.P = VG.Proof.X448.valN f 16 % VG.Spec.X448.P := by
  have e := VG.Proof.X448.pass_eq (VG.Proof.X448.folded (VG.Proof.X448.folded f)) 16
  rw [VG.Proof.X448.final_carry h, Nat.mul_zero, Nat.add_zero] at e
  rw [VG.Proof.X448.normalized, e, VG.Proof.X448.folded_mod, VG.Proof.X448.folded_mod]

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Difference`. -/
section

/-!
# X448: nonnegative limb subtraction

Adding twice the field prime permits every limb subtraction to be performed
without borrowing.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def bias (i : Nat) : Nat := if i = 8 then 2 * VG.Proof.X448.radix - 4 else 2 * VG.Proof.X448.radix - 2

theorem bias_val : VG.Proof.X448.valN VG.Proof.X448.bias 16 = 2 * VG.Spec.X448.P := by decide +kernel

theorem bias_bound (i : Nat) : VG.Proof.X448.radix ≤ VG.Proof.X448.bias i ∧ VG.Proof.X448.bias i < 2 * VG.Proof.X448.radix := by
  unfold VG.Proof.X448.bias
  split <;> decide

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + VG.Proof.X448.bias i - g i

theorem difference_bound {f g : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix) :
    ∀ i < 16, VG.Proof.X448.difference f g i < 2 ^ 62 := by
  intro i hi
  have h1 := hf i hi
  have h2 := (VG.Proof.X448.bias_bound i).2
  have hr : 3 * VG.Proof.X448.radix < 2 ^ 62 := by decide
  simp only [VG.Proof.X448.difference]
  omega

theorem difference_val {f g : Nat → Nat} (hg : ∀ i < 16, g i < VG.Proof.X448.radix) :
    VG.Proof.X448.valN (VG.Proof.X448.difference f g) 16 + VG.Proof.X448.valN g 16 = VG.Proof.X448.valN f 16 + 2 * VG.Spec.X448.P := by
  rw [← VG.Proof.X448.valN_add]
  have he : VG.Proof.X448.valN (fun i => VG.Proof.X448.difference f g i + g i) 16 = VG.Proof.X448.valN (fun i => f i + VG.Proof.X448.bias i) 16 := by
    apply VG.Proof.X448.valN_congr
    intro i hi
    have h1 := hg i hi
    have h2 := (VG.Proof.X448.bias_bound i).1
    simp only [VG.Proof.X448.difference]
    omega
  rw [he, VG.Proof.X448.valN_add, VG.Proof.X448.bias_val]

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Pairs`. -/
section

/-!
# X448: seven-byte chunks and limb pairs

A seven-byte chunk contains exactly two 28-bit limbs. Reading eight chunks
uses all 56 input bytes.
-/

namespace VG.Proof.X448

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leNum_append leNum_lt)

abbrev chunk (m : Mem) (p : Addr) (i : Nat) : Nat :=
  leNum (bytesAt m (p + BitVec.ofNat 64 (7 * i)) 7)

def decoded (m : Mem) (p : Addr) (i : Nat) : Nat :=
  if i % 2 = 0 then VG.Proof.X448.chunk m p (i / 2) % VG.Proof.X448.radix else VG.Proof.X448.chunk m p (i / 2) / VG.Proof.X448.radix

theorem chunk_lt (m : Mem) (p : Addr) (i : Nat) : VG.Proof.X448.chunk m p i < VG.Proof.X448.radix * VG.Proof.X448.radix := by
  have h := leNum_lt (bytesAt m (p + BitVec.ofNat 64 (7 * i)) 7)
  rw [VG.Proof.X448.length_bytesAt] at h
  exact h

theorem decoded_even (m : Mem) (p : Addr) (i : Nat) : VG.Proof.X448.decoded m p (2 * i) = VG.Proof.X448.chunk m p i % VG.Proof.X448.radix := by
  rw [VG.Proof.X448.decoded, show 2 * i % 2 = 0 by omega, ite_eq_left rfl, show 2 * i / 2 = i by omega]

theorem decoded_odd (m : Mem) (p : Addr) (i : Nat) : VG.Proof.X448.decoded m p (2 * i + 1) = VG.Proof.X448.chunk m p i / VG.Proof.X448.radix := by
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  rw [VG.Proof.X448.decoded, hd, hm, ite_eq_right (by decide)]

theorem decoded_bound (m : Mem) (p : Addr) (i : Nat) : VG.Proof.X448.decoded m p i < VG.Proof.X448.radix := by
  unfold VG.Proof.X448.decoded
  split
  · exact Nat.mod_lt _ (by decide)
  · have h := VG.Proof.X448.chunk_lt m p (i / 2)
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h

theorem byte_power (n : Nat) : 256 ^ (7 * n) = VG.Proof.X448.radix ^ (2 * n) := by
  rw [Nat.pow_mul, Nat.pow_mul]
  exact congrArg (fun b => b ^ n) (by decide)

theorem decoded_val (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.X448.valN (VG.Proof.X448.decoded m p) (2 * n) = leNum (bytesAt m p (7 * n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, VG.Proof.X448.valN, VG.Proof.X448.valN, ih, VG.Proof.X448.decoded_even, VG.Proof.X448.decoded_odd,
      Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.mod_add_div]
    rw [show 7 * (n + 1) = 7 * n + 7 by omega, VG.Proof.X448.bytesAt_add, leNum_append, VG.Proof.X448.length_bytesAt, VG.Proof.X448.byte_power]

/-- Accumulating a seven-byte chunk from its highest byte downwards. -/
def suffix (m : Mem) (p : Addr) (i n : Nat) : Nat :=
  leNum (bytesAt m (p + BitVec.ofNat 64 (7 * i + (7 - n))) n)

theorem suffix_bound (m : Mem) (p : Addr) (i n : Nat) : VG.Proof.X448.suffix m p i n < 256 ^ n := by
  have h := leNum_lt (bytesAt m (p + BitVec.ofNat 64 (7 * i + (7 - n))) n)
  rw [VG.Proof.X448.length_bytesAt] at h
  exact h

theorem suffix_succ (m : Mem) (p : Addr) (i : Nat) {n : Nat} (hn : n < 7) :
    VG.Proof.X448.suffix m p i (n + 1) = 256 * VG.Proof.X448.suffix m p i n + (m (p + BitVec.ofNat 64 (7 * i + (6 - n)))).toNat := by
  unfold VG.Proof.X448.suffix
  have bs : ∀ (q : Addr) (n : Nat), bytesAt m q (n + 1) = m q :: bytesAt m (q + 1) n :=
    VG.Proof.X25519.bytesAt_succ m
  rw [bs, leNum]
  have he : p + BitVec.ofNat 64 (7 * i + (7 - (n + 1))) + 1 =
      p + BitVec.ofNat 64 (7 * i + (7 - n)) := by
    change p + BitVec.ofNat 64 (7 * i + (7 - (n + 1))) + BitVec.ofNat 64 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [he, show 7 - (n + 1) = 6 - n by omega, Nat.add_comm]

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Encoding`. -/
section

/-!
# X448: encoding pairs of limbs

Seven output bytes encode two bounded limbs, and eight such pairs encode the
complete field element.
-/

namespace VG.Proof.X448

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leBytes)

theorem leNum_leBytes {n x : Nat} (hx : x < 256 ^ n) : leNum (leBytes n x) = x := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst x
    rfl
  | succ n ih =>
    rw [VG.Proof.X25519.leBytes_succ, leNum, ih (by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa only [Nat.pow_succ, Nat.mul_comm] using hx)]
    exact Nat.mod_add_div x 256

theorem decoded_packed {m : Mem} {p : Addr} {f : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix)
    (hc : ∀ i < 8, VG.Proof.X448.chunk m p i = f (2 * i) + VG.Proof.X448.radix * f (2 * i + 1)) :
    ∀ i < 16, VG.Proof.X448.decoded m p i = f i := by
  intro i hi
  have h := hc (i / 2) (by omega)
  have h0 := hf (2 * (i / 2)) (by omega)
  have h1 : VG.Proof.X448.radix = 268435456 := rfl
  unfold VG.Proof.X448.decoded
  rw [h]
  split
  · rename_i he
    have e : 2 * (i / 2) = i := by omega
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0, e]
  · rename_i he
    have e : 2 * (i / 2) + 1 = i := by omega
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h0, Nat.zero_add, e]

theorem packed_bytes {m : Mem} {p : Addr} {f : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix)
    (hc : ∀ i < 8, VG.Proof.X448.chunk m p i = f (2 * i) + VG.Proof.X448.radix * f (2 * i + 1)) :
    bytesAt m p 56 = leBytes 56 (VG.Proof.X448.valN f 16) := by
  have hv : leNum (bytesAt m p 56) = VG.Proof.X448.valN f 16 :=
    (VG.Proof.X448.decoded_val m p 8).symm.trans (VG.Proof.X448.valN_congr (VG.Proof.X448.decoded_packed hf hc))
  have out : bytesAt m p 56 = leBytes 56 (m.read p 56).toNat :=
    VG.Proof.X25519.bytesAt_leBytes m p 56
  rw [← VG.Proof.X448.leNum_bytesAt_read, hv] at out
  exact out

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Freeze`. -/
section

/-!
# X448: canonical reduction

For a normalized value below 2⁴⁴⁸, adding 1 + 2²²⁴ produces a carry exactly
when it is at least p. Selecting the carried result in that case gives the
canonical residue.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def freezeCoeff (f : Nat → Nat) (i : Nat) : Nat := f i + if i = 0 ∨ i = 8 then 1 else 0

theorem freezeCoeff_val (f : Nat → Nat) : VG.Proof.X448.valN (VG.Proof.X448.freezeCoeff f) 16 = VG.Proof.X448.valN f 16 + (VG.Proof.X448.half + 1) := by
  change VG.Proof.X448.valN (fun i => f i + if i = 0 ∨ i = 8 then 1 else 0) 16 = _
  rw [VG.Proof.X448.valN_add]
  congr 1

theorem freezeCoeff_bound {f : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix) :
    ∀ i < 16, VG.Proof.X448.freezeCoeff f i < 2 ^ 62 := by
  intro i hi
  have h := hf i hi
  have hr : VG.Proof.X448.radix + 1 < 2 ^ 62 := by decide
  simp only [VG.Proof.X448.freezeCoeff]
  split <;> omega

theorem freeze_carry {f : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix) :
    VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16 = if VG.Spec.X448.P ≤ VG.Proof.X448.valN f 16 then 1 else 0 := by
  have hv := VG.Proof.X448.valN_lt hf
  have hd := VG.Proof.X448.valN_lt (n := 16) (fun i _ => VG.Proof.X448.digit_lt (VG.Proof.X448.freezeCoeff f) i)
  have e := VG.Proof.X448.pass_eq (VG.Proof.X448.freezeCoeff f) 16
  rw [VG.Proof.X448.freezeCoeff_val] at e
  change VG.Proof.X448.valN f 16 < VG.Proof.X448.full at hv
  change VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.freezeCoeff f)) 16 < VG.Proof.X448.full at hd
  change VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.freezeCoeff f)) 16 + VG.Proof.X448.full * VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16 = _ at e
  have hp : VG.Proof.X448.half + 1 < VG.Spec.X448.P := by decide +kernel
  have he := VG.Proof.X448.full_eq
  have hq : VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16 ≤ 1 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left VG.Proof.X448.full (show 2 ≤ VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16 by omega)
    omega
  rcases Nat.eq_zero_or_pos (VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at e
    rw [ite_eq_right (by omega), h]
  · have h : VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16 = 1 := by omega
    rw [h, Nat.mul_one] at e
    rw [ite_eq_left (by omega), h]

theorem freeze_value {f : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix) :
    (if VG.Proof.X448.carry (VG.Proof.X448.freezeCoeff f) 16 = 1 then VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.freezeCoeff f)) 16 else VG.Proof.X448.valN f 16) =
      VG.Proof.X448.valN f 16 % VG.Spec.X448.P := by
  have hv := VG.Proof.X448.valN_lt hf
  change VG.Proof.X448.valN f 16 < VG.Proof.X448.full at hv
  have e := VG.Proof.X448.pass_eq (VG.Proof.X448.freezeCoeff f) 16
  rw [VG.Proof.X448.freezeCoeff_val, VG.Proof.X448.freeze_carry hf] at e
  rw [VG.Proof.X448.freeze_carry hf]
  have hp : VG.Proof.X448.half + 1 < VG.Spec.X448.P := by decide +kernel
  have he := VG.Proof.X448.full_eq
  by_cases h : VG.Spec.X448.P ≤ VG.Proof.X448.valN f 16
  · rw [ite_eq_left h, ite_eq_left rfl]
    rw [ite_eq_left h, Nat.mul_one] at e
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : valN f 16 - P < P)]
    change VG.Proof.X448.valN (VG.Proof.X448.digit (VG.Proof.X448.freezeCoeff f)) 16 + VG.Proof.X448.full = _ at e
    omega
  · rw [ite_eq_right h, ite_eq_right (by decide), Nat.mod_eq_of_lt (by omega)]

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Product`. -/
section

/-!
# X448: row multiplication and coefficient reduction

Multiplication adds one row at a time to a 32-word coefficient array. The
upper coefficients fold into sixteen limbs using the field prime's two
non-leading terms.
-/

namespace VG.Proof.X448

open VG.Spec.X448

def addAt (f : Nat → Nat) (k v : Nat) (i : Nat) : Nat :=
  if i = k then f i + v else f i

theorem addAt_val (f : Nat → Nat) {n k : Nat} (hk : k < n) (v : Nat) :
    VG.Proof.X448.valN (VG.Proof.X448.addAt f k v) n = VG.Proof.X448.valN f n + VG.Proof.X448.radix ^ k * v :=
  VG.Proof.X448.valN_update hk (fun _ _ => rfl)

/-- The first `n` products of a row, at displacement `i`. -/
def addRow (f : Nat → Nat) (a : Nat) (g : Nat → Nat) (i : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => VG.Proof.X448.addAt (VG.Proof.X448.addRow f a g i n) (i + n) (a * g n)

theorem addRow_val (f g : Nat → Nat) (a : Nat) {i n : Nat} (h : i + n ≤ 32) :
    VG.Proof.X448.valN (VG.Proof.X448.addRow f a g i n) 32 = VG.Proof.X448.valN f 32 + VG.Proof.X448.radix ^ i * a * VG.Proof.X448.valN g n := by
  induction n with
  | zero => simp only [VG.Proof.X448.addRow, VG.Proof.X448.valN, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    rw [VG.Proof.X448.addRow, VG.Proof.X448.addAt_val _ (by omega), ih (by omega), VG.Proof.X448.valN_succ g n, Nat.pow_add]
    generalize VG.Proof.X448.radix ^ i = A
    generalize VG.Proof.X448.radix ^ n = B
    grind

theorem addRow_at (f g : Nat → Nat) (a i n k : Nat) :
    VG.Proof.X448.addRow f a g i n k = f k + if i ≤ k ∧ k < i + n then a * g (k - i) else 0 := by
  induction n with
  | zero => simp only [VG.Proof.X448.addRow, Nat.add_zero, show ¬ (i ≤ k ∧ k < i) by omega,
      ite_false, Nat.add_zero]
  | succ n ih =>
    simp only [VG.Proof.X448.addRow, VG.Proof.X448.addAt]
    by_cases hk : k = i + n
    · subst k
      rw [ite_eq_left rfl, ih, ite_eq_right (by omega), Nat.add_zero,
        ite_eq_left (by omega), Nat.add_sub_cancel_left]
    · rw [ite_eq_right hk, ih]
      have he : (i ≤ k ∧ k < i + n) ↔ (i ≤ k ∧ k < i + (n + 1)) := by omega
      simp only [he]

/-- The first `n` rows of the product of two sixteen-limb operands. -/
def rows (f g : Nat → Nat) : Nat → Nat → Nat
  | 0 => fun _ => 0
  | n + 1 => VG.Proof.X448.addRow (VG.Proof.X448.rows f g n) (f n) g n 16

theorem rows_val (f g : Nat → Nat) {n : Nat} (hn : n ≤ 16) :
    VG.Proof.X448.valN (VG.Proof.X448.rows f g n) 32 = VG.Proof.X448.valN f n * VG.Proof.X448.valN g 16 := by
  induction n with
  | zero => simp only [VG.Proof.X448.rows, VG.Proof.X448.valN, Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | succ n ih =>
    rw [VG.Proof.X448.rows, VG.Proof.X448.addRow_val _ _ _ (by omega), ih (by omega), VG.Proof.X448.valN_succ f n, Nat.add_mul]

theorem rows_bound {f g : Nat → Nat} (hf : ∀ i < 16, f i < VG.Proof.X448.radix)
    (hg : ∀ i < 16, g i < VG.Proof.X448.radix) {n : Nat} (hn : n ≤ 16) (k : Nat) :
    VG.Proof.X448.rows f g n k ≤ n * (VG.Proof.X448.radix - 1) ^ 2 := by
  induction n with
  | zero => simp only [VG.Proof.X448.rows, Nat.zero_mul, Nat.le_refl]
  | succ n ih =>
    rw [VG.Proof.X448.rows, VG.Proof.X448.addRow_at]
    have hp := ih (by omega)
    split
    · rename_i hk
      have h1 := hf n (by omega)
      have h2 := hg (k - n) (by omega)
      have hprod : f n * g (k - n) ≤ (VG.Proof.X448.radix - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by omega) (by omega)
      rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

/-- Coefficients of degree 16–23 fold once; 24–31 fold twice. -/
def reduced (f : Nat → Nat) (k : Nat) : Nat :=
  f k + f (k + 16) + if k < 8 then f (k + 24) else f (k + 8) + f (k + 16)

theorem reduced_val (f : Nat → Nat) :
    VG.Proof.X448.valN (VG.Proof.X448.reduced f) 16 =
      (VG.Proof.X448.valN f 8 + VG.Proof.X448.valN (fun i => f (16 + i)) 8 + VG.Proof.X448.valN (fun i => f (24 + i)) 8) +
      VG.Proof.X448.half * (VG.Proof.X448.valN (fun i => f (8 + i)) 8 + VG.Proof.X448.valN (fun i => f (24 + i)) 8 +
        VG.Proof.X448.valN (fun i => f (16 + i)) 8 + VG.Proof.X448.valN (fun i => f (24 + i)) 8) := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.X448.valN_split]
  apply congrArg₂ (· + ·)
  · rw [← VG.Proof.X448.valN_add, ← VG.Proof.X448.valN_add]
    apply VG.Proof.X448.valN_congr
    intro i hi
    simp only [VG.Proof.X448.reduced, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (VG.Proof.X448.radix ^ 8 * ·)
    rw [← VG.Proof.X448.valN_add, ← VG.Proof.X448.valN_add, ← VG.Proof.X448.valN_add]
    apply VG.Proof.X448.valN_congr
    intro i _
    simp only [VG.Proof.X448.reduced, ite_eq_right (by omega : ¬ 8 + i < 8)]
    rw [show 8 + i + 16 = 24 + i by omega, show 8 + i + 8 = 16 + i by omega]
    simp only [Nat.reduceAdd]
    omega

theorem reduced_mod (f : Nat → Nat) : VG.Proof.X448.valN (VG.Proof.X448.reduced f) 16 % VG.Spec.X448.P = VG.Proof.X448.valN f 32 % VG.Spec.X448.P := by
  have hp : VG.Spec.X448.P = VG.Proof.X448.full - VG.Proof.X448.half - 1 := by decide +kernel
  have he : VG.Proof.X448.valN f 32 = VG.Proof.X448.valN (VG.Proof.X448.reduced f) 16 +
      VG.Spec.X448.P * (VG.Proof.X448.valN (fun i => f (16 + i)) 8 + (VG.Proof.X448.half + 1) * VG.Proof.X448.valN (fun i => f (24 + i)) 8) := by
    rw [VG.Proof.X448.reduced_val, show 32 = 16 + 16 from rfl, VG.Proof.X448.valN_split,
      show 16 = 8 + 8 from rfl, VG.Proof.X448.valN_split, VG.Proof.X448.valN_split]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, VG.Proof.X448.full, VG.Proof.X448.half, VG.Proof.X448.radix, Nat.reducePow]
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem reduced_bound {f : Nat → Nat} (h : ∀ i < 32, f i < 2 ^ 60) :
    ∀ i < 16, VG.Proof.X448.reduced f i < 2 ^ 62 := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 16) (by omega)
  simp only [VG.Proof.X448.reduced]
  split
  · have h2 := h (i + 24) (by omega); omega
  · have h2 := h (i + 8) (by omega); omega

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Radix16`. -/
section

/-!
# X448: radix-2¹⁶ arithmetic

The twenty-eight limbs of a field element, carries, and reduction using `2^448 =
2^224 + 1` modulo p. These lemmas do not depend on an instruction set.
-/

namespace VG.Proof.X448.Radix16

open VG.Spec.X448

def radix : Nat := 2 ^ 16
def full : Nat := VG.Proof.X448.Radix16.radix ^ 28
def half : Nat := VG.Proof.X448.Radix16.radix ^ 14

theorem full_eq : VG.Proof.X448.Radix16.full = VG.Spec.X448.P + (VG.Proof.X448.Radix16.half + 1) := by decide +kernel
theorem half_sq : VG.Proof.X448.Radix16.half * VG.Proof.X448.Radix16.half = VG.Proof.X448.Radix16.full := by decide +kernel

/-- Read `n` limbs, lowest first. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X448.Radix16.valN f n + VG.Proof.X448.Radix16.radix ^ n * f n

theorem valN_succ (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Radix16.valN f (n + 1) = VG.Proof.X448.Radix16.valN f n + VG.Proof.X448.Radix16.radix ^ n * f n := rfl

theorem valN_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ i < n, f i = g i) : VG.Proof.X448.Radix16.valN f n = VG.Proof.X448.Radix16.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem valN_add (f g : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Radix16.valN (fun i => f i + g i) n = VG.Proof.X448.Radix16.valN f n + VG.Proof.X448.Radix16.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, ih, Nat.mul_add]; omega

theorem valN_scale (c : Nat) (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Radix16.valN (fun i => c * f i) n = c * VG.Proof.X448.Radix16.valN f n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Radix16.valN, Nat.mul_zero]
  | succ n ih => rw [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, ih, Nat.mul_add, Nat.mul_left_comm (VG.Proof.X448.Radix16.radix ^ n) c]

theorem valN_split (f : Nat → Nat) (a b : Nat) :
    VG.Proof.X448.Radix16.valN f (a + b) = VG.Proof.X448.Radix16.valN f a + VG.Proof.X448.Radix16.radix ^ a * VG.Proof.X448.Radix16.valN (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, VG.Proof.X448.Radix16.valN, Nat.mul_zero]
  | succ b ih => rw [Nat.add_succ, VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < VG.Proof.X448.Radix16.radix) :
    VG.Proof.X448.Radix16.valN f n < VG.Proof.X448.Radix16.radix ^ n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Radix16.valN, Nat.pow_zero]; decide
  | succ n ih =>
    have hn := h n (by omega)
    have hp := ih fun i hi => h i (by omega)
    have hm := Nat.mul_le_mul_left (VG.Proof.X448.Radix16.radix ^ n) hn
    rw [Nat.mul_succ] at hm
    rw [VG.Proof.X448.Radix16.valN, Nat.pow_succ]
    omega

theorem valN_zero (n : Nat) : VG.Proof.X448.Radix16.valN (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.Radix16.valN, ih, Nat.mul_zero, Nat.add_zero]

/-- Changing one limb changes the value at that limb's weight. -/
theorem valN_update {f g : Nat → Nat} {n k v : Nat} (hk : k < n)
    (h : ∀ i < n, g i = if i = k then f i + v else f i) :
    VG.Proof.X448.Radix16.valN g n = VG.Proof.X448.Radix16.valN f n + VG.Proof.X448.Radix16.radix ^ k * v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : k = n
    · subst k
      have he : VG.Proof.X448.Radix16.valN g n = VG.Proof.X448.Radix16.valN f n := VG.Proof.X448.Radix16.valN_congr fun i hi => by
        rw [h i (by omega), ite_eq_right (by omega)]
      rw [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, he, h n (by omega), ite_eq_left rfl, Nat.mul_add]
      omega
    · rw [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, ih (by omega) (fun i hi => h i (by omega)),
        h n (by omega), ite_eq_right (Ne.symm hn)]
      omega

/-- The incoming carry at position `n`. -/
def carry (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n + VG.Proof.X448.Radix16.carry f n) / VG.Proof.X448.Radix16.radix

def digit (f : Nat → Nat) (i : Nat) : Nat := (f i + VG.Proof.X448.Radix16.carry f i) % VG.Proof.X448.Radix16.radix

theorem digit_lt (f : Nat → Nat) (i : Nat) : VG.Proof.X448.Radix16.digit f i < VG.Proof.X448.Radix16.radix :=
  Nat.mod_lt _ (by decide)

theorem pass_eq (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit f) n + VG.Proof.X448.Radix16.radix ^ n * VG.Proof.X448.Radix16.carry f n = VG.Proof.X448.Radix16.valN f n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.carry, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (f n + VG.Proof.X448.Radix16.carry f n) VG.Proof.X448.Radix16.radix
    change VG.Proof.X448.Radix16.digit f n + VG.Proof.X448.Radix16.radix * VG.Proof.X448.Radix16.carry f (n + 1) = f n + VG.Proof.X448.Radix16.carry f n at hd
    rw [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.valN, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hd,
      Nat.mul_add]
    omega

theorem carry_bound {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    VG.Proof.X448.Radix16.carry f n < 2 ^ 16 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Radix16.carry]; decide
  | succ n ih =>
    have hi := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    simp only [VG.Proof.X448.Radix16.radix] at hn hi ⊢
    simp only [VG.Proof.X448.Radix16.carry, VG.Proof.X448.Radix16.radix]
    omega

/-- The carry-out folded into the normalized limbs at positions 0 and 14. -/
def folded (f : Nat → Nat) (i : Nat) : Nat :=
  VG.Proof.X448.Radix16.digit f i + if i = 0 ∨ i = 14 then VG.Proof.X448.Radix16.carry f 28 else 0

theorem folded_val (f : Nat → Nat) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.folded f) 28 = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit f) 28 + (VG.Proof.X448.Radix16.half + 1) * VG.Proof.X448.Radix16.carry f 28 := by
  change VG.Proof.X448.Radix16.valN (fun i => VG.Proof.X448.Radix16.digit f i + if i = 0 ∨ i = 14 then VG.Proof.X448.Radix16.carry f 28 else 0) 28 = _
  rw [VG.Proof.X448.Radix16.valN_add]
  congr 1
  simp only [VG.Proof.X448.Radix16.valN, VG.Proof.X448.Radix16.half]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  grind

theorem fold_mod (lo hi : Nat) :
    (lo + VG.Proof.X448.Radix16.full * hi) % VG.Spec.X448.P = (lo + (VG.Proof.X448.Radix16.half + 1) * hi) % VG.Spec.X448.P := by
  rw [VG.Proof.X448.Radix16.full_eq, Nat.add_mul, Nat.add_left_comm lo, Nat.add_comm (VG.Spec.X448.P * hi), Nat.add_mul_mod_self_left]

theorem folded_mod (f : Nat → Nat) : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.folded f) 28 % VG.Spec.X448.P = VG.Proof.X448.Radix16.valN f 28 % VG.Spec.X448.P := by
  rw [VG.Proof.X448.Radix16.folded_val, ← VG.Proof.X448.Radix16.fold_mod, ← VG.Proof.X448.Radix16.pass_eq f 28]
  rfl

theorem folded_bound {f : Nat → Nat} (h : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    ∀ i < 28, VG.Proof.X448.Radix16.folded f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
  have hc := VG.Proof.X448.Radix16.carry_bound h
  intro i _
  have hd := VG.Proof.X448.Radix16.digit_lt f i
  simp only [VG.Proof.X448.Radix16.folded]
  split <;> simp only [VG.Proof.X448.Radix16.radix] at hd ⊢ <;> omega

/-- After two folds, no carry remains beyond the 448-bit field width. -/
theorem final_carry {f : Nat → Nat} (h : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f)) 28 = 0 := by
  by_contra hn
  have hn : 1 ≤ VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f)) 28 := Nat.pos_of_ne_zero hn
  have c0 := VG.Proof.X448.Radix16.carry_bound h
  have v0 := VG.Proof.X448.Radix16.valN_lt (n := 28) (fun i _ => VG.Proof.X448.Radix16.digit_lt f i)
  have v1 := VG.Proof.X448.Radix16.valN_lt (n := 28) (fun i _ => VG.Proof.X448.Radix16.digit_lt (VG.Proof.X448.Radix16.folded f) i)
  have e1 := VG.Proof.X448.Radix16.pass_eq (VG.Proof.X448.Radix16.folded f) 28
  have e2 := VG.Proof.X448.Radix16.pass_eq (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f)) 28
  rw [VG.Proof.X448.Radix16.folded_val] at e1 e2
  change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit f) 28 < VG.Proof.X448.Radix16.full at v0
  change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.folded f)) 28 < VG.Proof.X448.Radix16.full at v1
  change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.folded f)) 28 + VG.Proof.X448.Radix16.full * VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded f) 28 = _ at e1
  change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f))) 28 + VG.Proof.X448.Radix16.full * VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f)) 28 = _ at e2
  have small : (VG.Proof.X448.Radix16.half + 1) * (2 ^ 16 + 1) < VG.Proof.X448.Radix16.full := by decide +kernel
  have c1 : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded f) 28 ≤ 1 := by
    by_contra hc
    have hb := Nat.mul_le_mul_left (VG.Proof.X448.Radix16.half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left VG.Proof.X448.Radix16.full (show 2 ≤ VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded f) 28 from by omega)
    omega
  rcases Nat.eq_zero_or_pos (VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded f) 28) with hc | hc
  · rw [hc, Nat.mul_zero, Nat.add_zero] at e2
    have hp := Nat.mul_le_mul_left VG.Proof.X448.Radix16.full hn
    omega
  · have hc : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.folded f) 28 = 1 := by omega
    rw [hc, Nat.mul_one] at e1 e2
    have hb := Nat.mul_le_mul_left (VG.Proof.X448.Radix16.half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left VG.Proof.X448.Radix16.full hn
    omega

def normalized (f : Nat → Nat) : Nat → Nat := VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f))

theorem normalized_mod {f : Nat → Nat} (h : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.normalized f) 28 % VG.Spec.X448.P = VG.Proof.X448.Radix16.valN f 28 % VG.Spec.X448.P := by
  have e := VG.Proof.X448.Radix16.pass_eq (VG.Proof.X448.Radix16.folded (VG.Proof.X448.Radix16.folded f)) 28
  rw [VG.Proof.X448.Radix16.final_carry h, Nat.mul_zero, Nat.add_zero] at e
  rw [VG.Proof.X448.Radix16.normalized, e, VG.Proof.X448.Radix16.folded_mod, VG.Proof.X448.Radix16.folded_mod]


def bias (i : Nat) : Nat := if i = 14 then 2 * VG.Proof.X448.Radix16.radix - 4 else 2 * VG.Proof.X448.Radix16.radix - 2

theorem bias_val : VG.Proof.X448.Radix16.valN VG.Proof.X448.Radix16.bias 28 = 2 * VG.Spec.X448.P := by decide +kernel

theorem bias_bound (i : Nat) : VG.Proof.X448.Radix16.radix ≤ VG.Proof.X448.Radix16.bias i ∧ VG.Proof.X448.Radix16.bias i < 2 * VG.Proof.X448.Radix16.radix := by
  unfold VG.Proof.X448.Radix16.bias
  split <;> decide

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + VG.Proof.X448.Radix16.bias i - g i

theorem difference_bound {f g : Nat → Nat} (hf : ∀ i < 28, f i < VG.Proof.X448.Radix16.radix) :
    ∀ i < 28, VG.Proof.X448.Radix16.difference f g i < 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
  intro i hi
  have h1 := hf i hi
  have h2 := (VG.Proof.X448.Radix16.bias_bound i).2
  have hr : 3 * VG.Proof.X448.Radix16.radix < 2 ^ 32 - VG.Proof.X448.Radix16.radix := by decide
  simp only [VG.Proof.X448.Radix16.difference]
  omega

theorem difference_val {f g : Nat → Nat} (hg : ∀ i < 28, g i < VG.Proof.X448.Radix16.radix) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.difference f g) 28 + VG.Proof.X448.Radix16.valN g 28 = VG.Proof.X448.Radix16.valN f 28 + 2 * VG.Spec.X448.P := by
  rw [← VG.Proof.X448.Radix16.valN_add]
  have he : VG.Proof.X448.Radix16.valN (fun i => VG.Proof.X448.Radix16.difference f g i + g i) 28 = VG.Proof.X448.Radix16.valN (fun i => f i + VG.Proof.X448.Radix16.bias i) 28 := by
    apply VG.Proof.X448.Radix16.valN_congr
    intro i hi
    have h1 := hg i hi
    have h2 := (VG.Proof.X448.Radix16.bias_bound i).1
    simp only [VG.Proof.X448.Radix16.difference]
    omega
  rw [he, VG.Proof.X448.Radix16.valN_add, VG.Proof.X448.Radix16.bias_val]


def freezeCoeff (f : Nat → Nat) (i : Nat) : Nat := f i + if i = 0 ∨ i = 14 then 1 else 0

theorem freezeCoeff_val (f : Nat → Nat) : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.freezeCoeff f) 28 = VG.Proof.X448.Radix16.valN f 28 + (VG.Proof.X448.Radix16.half + 1) := by
  change VG.Proof.X448.Radix16.valN (fun i => f i + if i = 0 ∨ i = 14 then 1 else 0) 28 = _
  rw [VG.Proof.X448.Radix16.valN_add]
  congr 1

theorem freezeCoeff_bound {f : Nat → Nat} (hf : ∀ i < 28, f i < VG.Proof.X448.Radix16.radix) :
    ∀ i < 28, VG.Proof.X448.Radix16.freezeCoeff f i < 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
  intro i hi
  have h := hf i hi
  have hr : VG.Proof.X448.Radix16.radix + 1 < 2 ^ 32 - VG.Proof.X448.Radix16.radix := by decide
  simp only [VG.Proof.X448.Radix16.freezeCoeff]
  split <;> omega

theorem freeze_carry {f : Nat → Nat} (hf : ∀ i < 28, f i < VG.Proof.X448.Radix16.radix) :
    VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28 = if VG.Spec.X448.P ≤ VG.Proof.X448.Radix16.valN f 28 then 1 else 0 := by
  have hv := VG.Proof.X448.Radix16.valN_lt hf
  have hd := VG.Proof.X448.Radix16.valN_lt (n := 28) (fun i _ => VG.Proof.X448.Radix16.digit_lt (VG.Proof.X448.Radix16.freezeCoeff f) i)
  have e := VG.Proof.X448.Radix16.pass_eq (VG.Proof.X448.Radix16.freezeCoeff f) 28
  rw [VG.Proof.X448.Radix16.freezeCoeff_val] at e
  change VG.Proof.X448.Radix16.valN f 28 < VG.Proof.X448.Radix16.full at hv
  change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.freezeCoeff f)) 28 < VG.Proof.X448.Radix16.full at hd
  change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.freezeCoeff f)) 28 + VG.Proof.X448.Radix16.full * VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28 = _ at e
  have hp : VG.Proof.X448.Radix16.half + 1 < VG.Spec.X448.P := by decide +kernel
  have he := VG.Proof.X448.Radix16.full_eq
  have hq : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28 ≤ 1 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left VG.Proof.X448.Radix16.full (show 2 ≤ VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28 by omega)
    omega
  rcases Nat.eq_zero_or_pos (VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at e
    rw [ite_eq_right (by omega), h]
  · have h : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28 = 1 := by omega
    rw [h, Nat.mul_one] at e
    rw [ite_eq_left (by omega), h]

theorem freeze_value {f : Nat → Nat} (hf : ∀ i < 28, f i < VG.Proof.X448.Radix16.radix) :
    (if VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff f) 28 = 1 then VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.freezeCoeff f)) 28 else VG.Proof.X448.Radix16.valN f 28) =
      VG.Proof.X448.Radix16.valN f 28 % VG.Spec.X448.P := by
  have hv := VG.Proof.X448.Radix16.valN_lt hf
  change VG.Proof.X448.Radix16.valN f 28 < VG.Proof.X448.Radix16.full at hv
  have e := VG.Proof.X448.Radix16.pass_eq (VG.Proof.X448.Radix16.freezeCoeff f) 28
  rw [VG.Proof.X448.Radix16.freezeCoeff_val, VG.Proof.X448.Radix16.freeze_carry hf] at e
  rw [VG.Proof.X448.Radix16.freeze_carry hf]
  have hp : VG.Proof.X448.Radix16.half + 1 < VG.Spec.X448.P := by decide +kernel
  have he := VG.Proof.X448.Radix16.full_eq
  by_cases h : VG.Spec.X448.P ≤ VG.Proof.X448.Radix16.valN f 28
  · rw [ite_eq_left h, ite_eq_left rfl]
    rw [ite_eq_left h, Nat.mul_one] at e
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : valN f 28 - P < P)]
    change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.freezeCoeff f)) 28 + VG.Proof.X448.Radix16.full = _ at e
    omega
  · rw [ite_eq_right h, ite_eq_right (by decide), Nat.mod_eq_of_lt (by omega)]




/-- Row `i` of a product, before carrying. -/
def rowC (acc a b : Nat → Nat) (i j : Nat) : Nat := a i * b j + acc (i + j)

/-- The limbs after row `i`, including its carry. -/
def rowAcc (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 28 then VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.rowC acc a b i) (k - i)
  else VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.rowC acc a b i) 28

theorem row_val {acc a b : Nat → Nat} {i : Nat}
    (hv : VG.Proof.X448.Radix16.valN acc (i + 28) = VG.Proof.X448.Radix16.valN a i * VG.Proof.X448.Radix16.valN b 28) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.rowAcc acc a b i) (i + 29) = VG.Proof.X448.Radix16.valN a (i + 1) * VG.Proof.X448.Radix16.valN b 28 := by
  have e1 : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.rowAcc acc a b i) i = VG.Proof.X448.Radix16.valN acc i :=
    VG.Proof.X448.Radix16.valN_congr fun k hk => by simp only [VG.Proof.X448.Radix16.rowAcc, hk, ite_true]
  have e2 : VG.Proof.X448.Radix16.valN (fun k => VG.Proof.X448.Radix16.rowAcc acc a b i (i + k)) 29 =
      VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.rowC acc a b i)) 28 + VG.Proof.X448.Radix16.radix ^ 28 * VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.rowC acc a b i) 28 := by
    rw [VG.Proof.X448.Radix16.valN_succ, VG.Proof.X448.Radix16.valN_congr (g := VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.rowC acc a b i)) fun k hk => by
      simp only [VG.Proof.X448.Radix16.rowAcc, show ¬ i + k < i by omega, show i + k < i + 28 by omega,
        ite_false, ite_true, Nat.add_sub_cancel_left]]
    simp only [VG.Proof.X448.Radix16.rowAcc, show ¬ i + 28 < i by omega, Nat.lt_irrefl, ite_false]
  have e3 : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.rowC acc a b i) 28 = a i * VG.Proof.X448.Radix16.valN b 28 + VG.Proof.X448.Radix16.valN (fun k => acc (i + k)) 28 := by
    rw [← VG.Proof.X448.Radix16.valN_scale, ← VG.Proof.X448.Radix16.valN_add]; rfl
  rw [VG.Proof.X448.Radix16.valN_split _ i 29, e1, e2, VG.Proof.X448.Radix16.pass_eq, e3, VG.Proof.X448.Radix16.valN_succ a i, Nat.add_mul, ← hv,
    VG.Proof.X448.Radix16.valN_split acc i 28, Nat.mul_add, Nat.mul_assoc]
  omega

theorem rowC_bound {acc a b : Nat → Nat} {i j : Nat} (ha : a i < VG.Proof.X448.Radix16.radix) (hb : b j < VG.Proof.X448.Radix16.radix)
    (hacc : acc (i + j) < VG.Proof.X448.Radix16.radix) : VG.Proof.X448.Radix16.rowC acc a b i j ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
  simp only [VG.Proof.X448.Radix16.radix] at ha hb hacc ⊢
  have : a i * b j ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
  simp only [VG.Proof.X448.Radix16.rowC]
  omega

theorem rowAcc_lt {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < VG.Proof.X448.Radix16.radix)
    (hc : ∀ j < 28, VG.Proof.X448.Radix16.rowC acc a b i j ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    ∀ k < i + 29, VG.Proof.X448.Radix16.rowAcc acc a b i k < VG.Proof.X448.Radix16.radix := by
  intro k _
  simp only [VG.Proof.X448.Radix16.rowAcc]
  split
  · exact hacc k (by omega)
  · split
    · exact VG.Proof.X448.Radix16.digit_lt _ _
    · exact VG.Proof.X448.Radix16.carry_bound hc

/-- Coefficients of degree 28–23 fold once; 42–31 fold twice. -/
def reduced (f : Nat → Nat) (k : Nat) : Nat :=
  f k + f (k + 28) + if k < 14 then f (k + 42) else f (k + 14) + f (k + 28)

theorem reduced_val (f : Nat → Nat) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.reduced f) 28 =
      (VG.Proof.X448.Radix16.valN f 14 + VG.Proof.X448.Radix16.valN (fun i => f (28 + i)) 14 + VG.Proof.X448.Radix16.valN (fun i => f (42 + i)) 14) +
      VG.Proof.X448.Radix16.half * (VG.Proof.X448.Radix16.valN (fun i => f (14 + i)) 14 + VG.Proof.X448.Radix16.valN (fun i => f (42 + i)) 14 +
        VG.Proof.X448.Radix16.valN (fun i => f (28 + i)) 14 + VG.Proof.X448.Radix16.valN (fun i => f (42 + i)) 14) := by
  rw [show 28 = 14 + 14 from rfl, VG.Proof.X448.Radix16.valN_split]
  apply congrArg₂ (· + ·)
  · rw [← VG.Proof.X448.Radix16.valN_add, ← VG.Proof.X448.Radix16.valN_add]
    apply VG.Proof.X448.Radix16.valN_congr
    intro i hi
    simp only [VG.Proof.X448.Radix16.reduced, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (VG.Proof.X448.Radix16.radix ^ 14 * ·)
    rw [← VG.Proof.X448.Radix16.valN_add, ← VG.Proof.X448.Radix16.valN_add, ← VG.Proof.X448.Radix16.valN_add]
    apply VG.Proof.X448.Radix16.valN_congr
    intro i _
    simp only [VG.Proof.X448.Radix16.reduced, ite_eq_right (by omega : ¬ 14 + i < 14)]
    rw [show 14 + i + 28 = 42 + i by omega, show 14 + i + 14 = 28 + i by omega]
    simp only [Nat.reduceAdd]
    omega

theorem reduced_mod (f : Nat → Nat) : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.reduced f) 28 % VG.Spec.X448.P = VG.Proof.X448.Radix16.valN f 56 % VG.Spec.X448.P := by
  have hp : VG.Spec.X448.P = VG.Proof.X448.Radix16.full - VG.Proof.X448.Radix16.half - 1 := by decide +kernel
  have he : VG.Proof.X448.Radix16.valN f 56 = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.reduced f) 28 +
      VG.Spec.X448.P * (VG.Proof.X448.Radix16.valN (fun i => f (28 + i)) 14 + (VG.Proof.X448.Radix16.half + 1) * VG.Proof.X448.Radix16.valN (fun i => f (42 + i)) 14) := by
    rw [VG.Proof.X448.Radix16.reduced_val, show 56 = 28 + 28 from rfl, VG.Proof.X448.Radix16.valN_split,
      show 28 = 14 + 14 from rfl, VG.Proof.X448.Radix16.valN_split, VG.Proof.X448.Radix16.valN_split]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, VG.Proof.X448.Radix16.full, VG.Proof.X448.Radix16.half, VG.Proof.X448.Radix16.radix, Nat.reducePow]
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem reduced_bound {f : Nat → Nat} (h : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix) :
    ∀ i < 28, VG.Proof.X448.Radix16.reduced f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 28) (by omega)
  simp only [VG.Proof.X448.Radix16.radix] at h0 h1 ⊢
  simp only [VG.Proof.X448.Radix16.reduced]
  split
  · have h2 := h (i + 42) (by omega); simp only [VG.Proof.X448.Radix16.radix] at h2; omega
  · have h2 := h (i + 14) (by omega); simp only [VG.Proof.X448.Radix16.radix] at h2; omega


end VG.Proof.X448.Radix16

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Radix16Bytes`. -/
section

/-!
# X448: byte encoding of 16-bit limbs

Each limb is two bytes, least significant first, with all 448 input bits
retained.
-/

namespace VG.Proof.X448.Radix16

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leNum_append leBytes)

def byteN (m : Mem) (p : Addr) (i : Nat) : Nat := (m (p + BitVec.ofNat 64 i)).toNat

def decoded (m : Mem) (p : Addr) (k : Nat) : Nat :=
  VG.Proof.X448.Radix16.byteN m p (2 * k) + 256 * VG.Proof.X448.Radix16.byteN m p (2 * k + 1)

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n :=
  VG.Proof.X25519.bytesAt_succ m p n

theorem decoded_val (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (2 * n)) = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m p) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 from rfl, VG.Proof.X448.bytesAt_add, leNum_append, VG.Proof.X448.Radix16.decoded_val m p n,
      VG.Proof.X448.Radix16.valN_succ, VG.Proof.X448.length_bytesAt, show (256 : Nat) ^ (2 * n) = VG.Proof.X448.Radix16.radix ^ n by rw [Nat.pow_mul]; rfl]
    apply congrArg (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m p) n + VG.Proof.X448.Radix16.radix ^ n * ·)
    rw [VG.Proof.X448.Radix16.bytesAt_succ, VG.Proof.X448.Radix16.bytesAt_succ,
      show bytesAt m (p + BitVec.ofNat 64 (2 * n) + 1 + 1) 0 = [] from rfl]
    simp only [leNum, VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN, Nat.mul_zero, Nat.add_zero]
    rw [Offset.add_ofNat_add_one]

theorem decoded_lt (m : Mem) (p : Addr) (k : Nat) : VG.Proof.X448.Radix16.decoded m p k < VG.Proof.X448.Radix16.radix := by
  have h0 := (m (p + BitVec.ofNat 64 (2 * k))).isLt
  have h1 := (m (p + BitVec.ofNat 64 (2 * k + 1))).isLt
  simp only [VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN, VG.Proof.X448.Radix16.radix]
  omega

theorem decode_val (m : Mem) (p : Addr) :
    VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m p) 28 = decodeUCoordinate (bytesAt m p 56) := by
  rw [VG.Proof.X448.decodeUCoordinate_eq (VG.Proof.X448.length_bytesAt m p 56)]
  exact (VG.Proof.X448.Radix16.decoded_val m p 28).symm

theorem packed_bytes {m : Mem} {p : Addr} {f : Nat → Nat}
    (h : ∀ i < 28, VG.Proof.X448.Radix16.decoded m p i = f i) : bytesAt m p 56 = leBytes 56 (VG.Proof.X448.Radix16.valN f 28) := by
  have hv : leNum (bytesAt m p 56) = VG.Proof.X448.Radix16.valN f 28 :=
    (VG.Proof.X448.Radix16.decoded_val m p 28).trans (VG.Proof.X448.Radix16.valN_congr h)
  have out : bytesAt m p 56 = leBytes 56 (m.read p 56).toNat :=
    VG.Proof.X25519.bytesAt_leBytes m p 56
  rw [← VG.Proof.X448.leNum_bytesAt_read, hv] at out
  exact out

end VG.Proof.X448.Radix16

end
