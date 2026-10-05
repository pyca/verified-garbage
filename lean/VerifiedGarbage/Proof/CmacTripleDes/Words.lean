import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Impl.CmacTripleDes.Index
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Des`. -/
section

/-!
# DES: the bits of the specification's permutations and round function

The specification builds `permute` and the S-boxes' outputs one bit (or
four) at a time, most significant first. These lemmas say which input bit
each output bit is, so that the implementations, checked bit by bit, can be
compared with them.
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes

/-! ## Permutations -/

theorem getLsbD_one' {n j : Nat} : (1 : BitVec n).getLsbD j = (decide (0 < n) && decide (j = 0)) :=
  BitVec.getLsbD_one

theorem getLsbD_permute_prefix {n m : Nat} (pos : Vector Nat m) (x : BitVec n) (hn : 0 < n)
    (k : Nat) (j : Nat) (hj : j < m) :
    ((List.range k).foldl (fun (out : BitVec m) i =>
      (out <<< 1) ||| (((x >>> (n - pos.getD i 1)) &&& 1).setWidth m)) 0).getLsbD j =
      (decide (j < k) && x.getLsbD (n - pos.getD (k - 1 - j) 1)) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, VG.Proof.CmacTripleDes.getLsbD_one']
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hn, hj]
    · rw [ih (j - 1) (by omega)]
      simp only [hj, decide_true, Bool.true_and, show ¬ j < 1 by omega, decide_false,
        Bool.not_false, show j ≠ 0 by omega, Bool.and_false, Bool.or_false]
      by_cases hk : j < k + 1
      · rw [show k + 1 - 1 - j = k - 1 - (j - 1) by omega]
        simp [hk, show j - 1 < k by omega]
      · simp [hk, show ¬ j - 1 < k by omega]

/-- Bit `j` of `permute pos x` is bit `n − pos[m − 1 − j]` of `x`. -/
theorem getLsbD_permute {n m : Nat} (pos : Vector Nat m) (x : BitVec n) (hn : 0 < n)
    {j : Nat} (hj : j < m) :
    (permute pos x).getLsbD j = x.getLsbD (n - pos.getD (m - 1 - j) 1) := by
  have h := VG.Proof.CmacTripleDes.getLsbD_permute_prefix pos x hn m j hj
  simp only [hj, decide_true, Bool.true_and] at h
  exact h

/-! ## The round function -/

theorem getLsbD_concat4_prefix (g : Nat → BitVec 4) (k q : Nat) (hq : q < 32) :
    ((List.range k).foldl (fun (out : BitVec 32) i => (out <<< 4) ||| (g i).zeroExtend 32) 0).getLsbD q =
      (decide (q < 4 * k) && (g (k - 1 - q / 4)).getLsbD (q % 4)) := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h4 : q < 4
    · simp [hq, h4, show q < 4 * (k + 1) by omega, Nat.div_eq_of_lt h4, Nat.mod_eq_of_lt h4]
    · rw [ih (q - 4) (by omega)]
      have e1 : (q - 4) / 4 = q / 4 - 1 := by omega
      have e2 : (q - 4) % 4 = q % 4 := by omega
      simp only [hq, decide_true, Bool.true_and, h4, decide_false, Bool.not_false, e1, e2,
        BitVec.getLsbD_of_ge (g k) q (by omega), Bool.and_false, Bool.or_false]
      by_cases hk : q < 4 * (k + 1)
      · simp [hk, show q - 4 < 4 * k by omega, show k - 1 - (q / 4 - 1) = k + 1 - 1 - q / 4 by omega]
      · simp [hk, show ¬ q - 4 < 4 * k by omega]

/-- Box `i`'s input in the round with input `r` and round key `k`. -/
def chunk (r : BitVec 32) (k : BitVec 48) (i : Nat) : BitVec 6 :=
  ((permute expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem getLsbD_chunk (r : BitVec 32) (k : BitVec 48) {i t : Nat} (hi : i < 8) (ht : t < 6) :
    (VG.Proof.CmacTripleDes.chunk r k i).getLsbD t =
      (r.getLsbD (Impl.CmacTripleDes.expSrc (6 * (7 - i) + t)) ^^ k.getLsbD (6 * (7 - i) + t)) := by
  simp only [VG.Proof.CmacTripleDes.chunk, BitVec.getLsbD_setWidth, ht, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) (by omega)]
  rfl

/-- Bit `j` of `f(r, k)` is output bit `u % 4` of box `7 − u / 4`, where
`u = pSrc j`. -/
theorem getLsbD_roundFunction (r : BitVec 32) (k : BitVec 48) {j : Nat} (hj : j < 32) :
    (roundFunction r k).getLsbD j =
      let u := Impl.CmacTripleDes.pSrc j
      (sBox (7 - u / 4) (VG.Proof.CmacTripleDes.chunk r k (7 - u / 4))).getLsbD (u % 4) := by
  have hu : Impl.CmacTripleDes.pSrc j < 32 := by
    revert j; decide
  simp only [roundFunction]
  rw [VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) hj, VG.Proof.CmacTripleDes.getLsbD_concat4_prefix _ 8 _ (by exact hu)]
  simp only [show 32 - p.getD (32 - 1 - j) 1 = Impl.CmacTripleDes.pSrc j from rfl,
    show Impl.CmacTripleDes.pSrc j < 4 * 8 from hu, decide_true, Bool.true_and,
    show 8 - 1 - Impl.CmacTripleDes.pSrc j / 4 = 7 - Impl.CmacTripleDes.pSrc j / 4 by omega]
  rfl

end VG.Proof.CmacTripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Block`. -/
section

/-!
# TDEA: the passes, and the key schedule in memory

`des` is `IP`, sixteen rounds and `IP⁻¹`; TDEA's three passes share one
`IP` and one `IP⁻¹`, which cancel between them, so that the passes are the
rounds with the halves exchanged (`tdes_eq`). The key schedule's slots are
little-endian words (`scheduleAt_getD`).
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes

theorem vgetD {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (d : α) :
    xs.getD i d = xs[i] := by
  simp [Vector.getD, Array.getD, h]

/-! ## Words in memory -/

/-- Bit `i` of a little-endian word is bit `i % 8` of its byte `i / 8`. -/
theorem getLsbD_readW64 (m : Mem) (a : Addr) {i : Nat} (hi : i < 64) :
    (m.readW a 64).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega

theorem getLsbD_bytes_prefix (f : Nat → Byte) (k i : Nat) (hi : i < 64) :
    ((List.range k).foldl (fun (out : BitVec 64) j => out ||| (f j).zeroExtend 64 <<< (8 * j)) 0).getLsbD i =
      (decide (i < 8 * k) && (f (i / 8)).getLsbD (i % 8)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or, ih,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h : i < 8 * k
    · simp [h, show i < 8 * (k + 1) by omega]
    · by_cases h' : i < 8 * (k + 1)
      · have e : i / 8 = k := by omega
        simp [h, h', hi, show i - 8 * k = i % 8 by omega, e, show i % 8 < 64 by omega]
      · simp only [h, h', decide_false, Bool.false_and, Bool.false_or, hi, decide_true,
          Bool.true_and]
        rw [BitVec.getLsbD_of_ge _ _ (by omega)]
        simp

/-- Slot `n` of the key schedule is the word at `p + 8 n`. -/
theorem scheduleAt_getD (m : Mem) (p : Addr) {n : Nat} (hn : n < 48) :
    (scheduleAt m p).getD n 0 = m.readW (p + BitVec.ofNat 64 (8 * n)) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.CmacTripleDes.vgetD _ hn, scheduleAt, Vector.getElem_ofFn, VG.Proof.CmacTripleDes.getLsbD_bytes_prefix _ 8 i hi,
    VG.Proof.CmacTripleDes.getLsbD_readW64 _ _ hi, decide_eq_true hi, Bool.true_and, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Rounds -/

/-- Rounds `0 … n - 1` from the halves `(L, R)`, with the round keys `ks`. -/
def rounds (ks : Nat → BitVec 48) (n : Nat) (lr : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  (List.range n).foldl (fun lr j => (lr.2, lr.1 ^^^ roundFunction lr.2 (ks j))) lr

theorem rounds_succ (ks : Nat → BitVec 48) (n : Nat) (lr : BitVec 32 × BitVec 32) :
    VG.Proof.CmacTripleDes.rounds ks (n + 1) lr =
      ((VG.Proof.CmacTripleDes.rounds ks n lr).2, (VG.Proof.CmacTripleDes.rounds ks n lr).1 ^^^ roundFunction (VG.Proof.CmacTripleDes.rounds ks n lr).2 (ks n)) := by
  simp only [VG.Proof.CmacTripleDes.rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The round keys of `des keys dir`, in the order it uses them. -/
def keyOrder (keys : DesSchedule) (dir : Direction) (j : Nat) : BitVec 48 :=
  keys.getD (if dir = .encrypt then j else 15 - j) 0

/-- The halves `(L, R)` of a block. -/
def split (x : BitVec 64) : BitVec 32 × BitVec 32 := ((x >>> 32).setWidth 32, x.setWidth 32)

theorem des_eq (keys : DesSchedule) (dir : Direction) (x : BitVec 64) :
    des keys dir x =
      permute fp ((VG.Proof.CmacTripleDes.rounds (VG.Proof.CmacTripleDes.keyOrder keys dir) 16 (VG.Proof.CmacTripleDes.split (permute ip x))).2 ++
        (VG.Proof.CmacTripleDes.rounds (VG.Proof.CmacTripleDes.keyOrder keys dir) 16 (VG.Proof.CmacTripleDes.split (permute ip x))).1) := by
  have h : (fun (lr : BitVec 32 × BitVec 32) (j : Nat) =>
      match lr with
      | (l, r) =>
        let k := keys.getD (if dir = .encrypt then j else 15 - j) 0
        (r, l ^^^ roundFunction r k)) =
      fun lr j => (lr.2, lr.1 ^^^ roundFunction lr.2 (VG.Proof.CmacTripleDes.keyOrder keys dir j)) := by
    funext lr j; rfl
  simp only [des, h]
  rfl

theorem ip_fp (x : BitVec 64) : permute ip (permute fp x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h : ∀ j < 64, 64 - ip.getD (64 - 1 - j) 1 < 64 ∧
      64 - fp.getD (64 - 1 - (64 - ip.getD (64 - 1 - j) 1)) 1 = j := by decide
  rw [VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) hj, VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) (h j hj).1, (h j hj).2]

theorem split_append (r l : BitVec 32) : VG.Proof.CmacTripleDes.split (r ++ l) = (r, l) := by
  simp only [VG.Proof.CmacTripleDes.split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      ite_eq_right (by omega), Nat.add_sub_cancel_left, decide_eq_true hi, Bool.true_and]
  · rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, ite_eq_left hi, decide_eq_true hi, Bool.true_and]

/-! ## TDEA -/

/-- `(L, R)` exchanged. -/
def swap (lr : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 := (lr.2, lr.1)

/-- The round keys of TDEA's pass `p` (`E_K1`, `D_K2`, `E_K3`). -/
def passKeys (S : Schedule) (p : Nat) : Nat → BitVec 48 :=
  VG.Proof.CmacTripleDes.keyOrder (componentSchedule S p) (if p % 2 = 1 then .decrypt else .encrypt)

/-- The halves after `p` passes (the halves exchanged after each). -/
def passes (S : Schedule) : Nat → BitVec 32 × BitVec 32 → BitVec 32 × BitVec 32
  | 0, lr => lr
  | p + 1, lr => VG.Proof.CmacTripleDes.swap (VG.Proof.CmacTripleDes.rounds (VG.Proof.CmacTripleDes.passKeys S p) 16 (VG.Proof.CmacTripleDes.passes S p lr))

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of a 64-bit block. -/
def tdes (S : Schedule) (x : BitVec 64) : BitVec 64 :=
  des (componentSchedule S 2) .encrypt (des (componentSchedule S 1) .decrypt
    (des (componentSchedule S 0) .encrypt x))

/-- TDEA encryption of a 64-bit block: `IP`, the passes, `IP⁻¹`. -/
theorem tdes_eq (S : Schedule) (x : BitVec 64) :
    VG.Proof.CmacTripleDes.tdes S x =
      permute fp ((VG.Proof.CmacTripleDes.passes S 3 (VG.Proof.CmacTripleDes.split (permute ip x))).1 ++ (VG.Proof.CmacTripleDes.passes S 3 (VG.Proof.CmacTripleDes.split (permute ip x))).2) := by
  simp only [VG.Proof.CmacTripleDes.tdes, VG.Proof.CmacTripleDes.des_eq, VG.Proof.CmacTripleDes.ip_fp, VG.Proof.CmacTripleDes.split_append, VG.Proof.CmacTripleDes.passes, VG.Proof.CmacTripleDes.passKeys, VG.Proof.CmacTripleDes.swap]
  rfl

/-- Pass `p`'s round key `j` is the low 48 bits of slot `kpos p j`. -/
theorem passKeys_eq (S : Schedule) {p j : Nat} (hj : j < 16) :
    VG.Proof.CmacTripleDes.passKeys S p j = (S.getD (16 * p + if p % 2 = 1 then 15 - j else j) 0).setWidth 48 := by
  simp only [VG.Proof.CmacTripleDes.passKeys, VG.Proof.CmacTripleDes.keyOrder, componentSchedule]
  split <;> split <;> simp_all <;> rw [VG.Proof.CmacTripleDes.vgetD _ (by omega), Vector.getElem_ofFn]

end VG.Proof.CmacTripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Bytes`. -/
section

/-!
# TDEA-CMAC: blocks as bytes and as 64-bit integers

CMAC works on lists of bytes; TDEA on 64-bit integers, big-endian
(`decodeBlock`, `encodeBlock`); the implementations load and store
little-endian words (`le8`), and reverse their bytes (`byteRev64`). So the
cipher of the bytes of a word is the bytes of a word (`tdesWith_le8`), and
so is the doubling of §6.1 (`dbl_le8`).
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes Proof.Cmac Spec.Cmac

theorem getLsbD_byteRev64 (w : BitVec 64) {i : Nat} (hi : i < 64) :
    (byteRev64 w).getLsbD i = w.getLsbD (8 * (7 - i / 8) + i % 8) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [byteRev64, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem getLsbD_foldl_bytes (L : List Byte) (init : BitVec 64) {i : Nat} (hi : i < 64) :
    (L.foldl (fun (out : BitVec 64) (byte : Byte) => (out <<< 8) ||| byte.zeroExtend 64) init).getLsbD i =
      if i < 8 * L.length then (L.getD (L.length - 1 - i / 8) 0).getLsbD (i % 8)
      else init.getLsbD (i - 8 * L.length) := by
  induction L generalizing init with
  | nil => simp
  | cons b L ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h₁ : i < 8 * L.length
    · rw [ite_eq_left h₁, ite_eq_left (by omega)]
      rw [show L.length + 1 - 1 - i / 8 = (L.length - 1 - i / 8) + 1 by omega]
      simp
    · rw [ite_eq_right h₁]
      by_cases h₂ : i < 8 * (L.length + 1)
      · rw [ite_eq_left h₂, show L.length + 1 - 1 - i / 8 = 0 by omega, decide_eq_true (by omega : i - 8 * L.length < 64),
          decide_eq_true (by omega : i - 8 * L.length < 8), show i - 8 * L.length = i % 8 by omega]
        simp
      · rw [ite_eq_right h₂, decide_eq_true (by omega : i - 8 * L.length < 64),
          decide_eq_false (by omega : ¬ i - 8 * L.length < 8), BitVec.getLsbD_of_ge b _ (by omega),
          show i - 8 * L.length - 8 = i - 8 * (L.length + 1) by omega]
        simp

theorem getLsbD_decode (v : Block) {i : Nat} (hi : i < 64) :
    (decodeBlock v).getLsbD i = (v.toList.getD (7 - i / 8) 0).getLsbD (i % 8) := by
  rw [decodeBlock, VG.Proof.CmacTripleDes.getLsbD_foldl_bytes _ _ hi, Vector.length_toList, ite_eq_left (by omega)]

theorem getD_le8_bit (w : BitVec 64) {k j : Nat} (hk : k < 8) (hj : j < 8) :
    ((le8 w).getD k 0).getLsbD j = w.getLsbD (8 * k + j) := by
  rw [getD_le8 _ hk, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]

theorem decode_le8 (w : BitVec 64) : decodeBlock (Vector.ofFn fun i => (le8 w).getD i 0) = byteRev64 w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.CmacTripleDes.getLsbD_decode _ hi, VG.Proof.CmacTripleDes.getLsbD_byteRev64 _ hi, Vector.toList_ofFn, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp only [show 7 - i / 8 < 8 by omega, dite_true, Option.getD_some]
  rw [VG.Proof.CmacTripleDes.getD_le8_bit _ (by omega) (Nat.mod_lt _ (by decide))]

theorem encode_le8 (y : BitVec 64) : (encodeBlock y).toList = le8 (byteRev64 y) := by
  apply List.ext_getElem (by simp [le8])
  intro k h₁ h₂
  have hk : k < 8 := by simpa using h₁
  simp only [le8, List.getElem_map, List.getElem_range, encodeBlock, Vector.toList_ofFn, List.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, VG.Proof.CmacTripleDes.getLsbD_byteRev64 _ (by omega),
    BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ushiftRight]
  congr 1; omega

theorem tdesWith_le8 (S : Schedule) (w : BitVec 64) :
    Spec.Cmac.tdesWith S (le8 w) = le8 (byteRev64 (VG.Proof.CmacTripleDes.tdes S (byteRev64 w))) := by
  rw [Spec.Cmac.tdesWith, encryptBlock, VG.Proof.CmacTripleDes.decode_le8, VG.Proof.CmacTripleDes.encode_le8]
  rfl

/-- Bit `j` of byte `k` of a block as a big-endian integer. -/
theorem le8_rev_bit (y : BitVec 64) {k j : Nat} (hk : k < 8) (hj : j < 8) :
    ((le8 (byteRev64 y)).getD k 0).getLsbD j = y.getLsbD (8 * (7 - k) + j) := by
  rw [VG.Proof.CmacTripleDes.getD_le8_bit _ hk hj, VG.Proof.CmacTripleDes.getLsbD_byteRev64 _ (by omega)]
  congr 1; omega

/-- The 64-bit doubling. -/
def dbl64 (y : BitVec 64) : BitVec 64 := (y <<< 1) ^^^ (if y.msb then 0x1b else 0)

theorem ext8 {x y : List Byte} (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ k < 8, x.getD k 0 = y.getD k 0) : x = y := by
  apply List.ext_getElem (by rw [hx, hy])
  intro k h₁ h₂
  have := h k (by omega)
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem getD_rb8 : ∀ k < 8, (rb 8).getD k 0 = if k = 7 then 0x1b else 0 := by decide

theorem high_0x1b {p : Nat} (hp : 8 ≤ p) : (0x1b : BitVec 64).getLsbD p = false := by
  rw [show (0x1b : BitVec 64) = BitVec.ofNat 64 27 from rfl, BitVec.getLsbD_ofNat]
  have : Nat.testBit 27 p = false := by
    apply Nat.testBit_lt_two_pow
    calc 27 < 2 ^ 8 := by decide
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
  rw [this, Bool.and_false]

theorem bit_0x1b : ∀ j < 8, (0x1b : BitVec 64).getLsbD j = (0x1b : Byte).getLsbD j := by decide

theorem dbl_le8 (y : BitVec 64) : dbl 8 (le8 (byteRev64 y)) = le8 (byteRev64 (VG.Proof.CmacTripleDes.dbl64 y)) := by
  have hL : (le8 (byteRev64 y)).length = 8 := length_le8 _
  have hmsb : msb1 (le8 (byteRev64 y)) = y.msb := by
    have h := VG.Proof.CmacTripleDes.le8_rev_bit y (k := 0) (j := 7) (by decide) (by decide)
    rw [BitVec.msb_eq_getLsbD_last, show 64 - 1 = 8 * (7 - 0) + 7 from rfl, ← h, msb1,
      BitVec.msb_eq_getLsbD_last]
    rfl
  have hsl : (shiftLeft1 (le8 (byteRev64 y))).length = 8 := by simp [shiftLeft1, hL]
  refine VG.Proof.CmacTripleDes.ext8 (by unfold dbl; split <;> simp [length_xor, hsl, rb, zeros]) (length_le8 _) fun k hk => ?_
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [VG.Proof.CmacTripleDes.le8_rev_bit _ hk hj, VG.Proof.CmacTripleDes.dbl64]
  have hdbl : (dbl 8 (le8 (byteRev64 y))).getD k 0 = (shiftLeft1 (le8 (byteRev64 y))).getD k 0 ^^^
      (if msb1 (le8 (byteRev64 y)) then (rb 8).getD k 0 else 0) := by
    unfold dbl
    split
    · rw [getD_xor (by simp [hsl, rb, zeros]) (by rw [hsl]; exact hk)]
    · simp
  have hs : (shiftLeft1 (le8 (byteRev64 y))).getD k 0 =
      ((le8 (byteRev64 y)).getD k 0 <<< 1) ||| ((((le8 (byteRev64 y)).drop 1 ++ [0]).getD k 0 : Byte) >>> 7) := by
    simp [shiftLeft1, List.getD_eq_getElem?_getD, hL, hk]
  rw [hdbl, hs, VG.Proof.CmacTripleDes.getD_rb8 k hk, hmsb]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hj, decide_true, Bool.true_and]
  have hm : ∀ p, 8 ≤ p → (if y.msb = true then (0x1b : BitVec 64) else 0).getLsbD p = false := by
    intro p hp; split
    · exact VG.Proof.CmacTripleDes.high_0x1b hp
    · simp
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · have hm0 : (if y.msb = true then (if k = 7 then (0x1b : Byte) else 0) else 0).getLsbD j = false := by
      simp [show k ≠ 7 by omega]
    have hnext : ((le8 (byteRev64 y)).drop 1 ++ [0]).getD k 0 = (le8 (byteRev64 y)).getD (k + 1) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hL, hk7,
        List.getElem?_eq_getElem (show k + 1 < (le8 (byteRev64 y)).length by omega)]
    rw [hm0, hm _ (by omega), Bool.xor_false, Bool.xor_false, hnext]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show 8 * (7 - k) + 0 - 1 = 8 * (7 - (k + 1)) + 7 by omega, ← VG.Proof.CmacTripleDes.le8_rev_bit y (by omega) (by decide)]
      simp [show ¬ 8 * (7 - k) < 1 by omega, show 8 * (7 - k) < 64 by omega]
    · rw [show 8 * (7 - k) + j - 1 = 8 * (7 - k) + (j - 1) by omega, ← VG.Proof.CmacTripleDes.le8_rev_bit y hk (by omega),
        BitVec.getLsbD_of_ge _ (7 + j) (by omega)]
      simp [show ¬ j < 1 by omega, show ¬ 8 * (7 - k) + j < 1 by omega, show 8 * (7 - k) + j < 64 by omega]
  · have hk' : k = 7 := by omega
    subst hk'
    have hnext : ((le8 (byteRev64 y)).drop 1 ++ [0]).getD 7 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, hL]
    rw [hnext]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · cases hb : y.msb
      · simp
      · simp
    · rw [show 8 * (7 - 7) + j - 1 = 8 * (7 - 7) + (j - 1) by omega, ← VG.Proof.CmacTripleDes.le8_rev_bit y (k := 7) (by decide) (by omega)]
      cases hb : y.msb
      · simp [show ¬ j < 1 by omega, show j < 64 by omega]
      · simp [show ¬ j < 1 by omega, show j < 64 by omega]
        exact (VG.Proof.CmacTripleDes.bit_0x1b j hj).symm

end VG.Proof.CmacTripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Cmac`. -/
section

/-!
# TDEA-CMAC: the specification with 8-byte blocks

`Proof/Cmac/Spec.lean` and `Proof/Cmac/Block.lean` for 8-byte blocks: the
MAC of whole blocks and the last bytes (`macFull_split8`), the padded last
block in memory (`padded_bytes8`), and TDEA's subkeys as 64-bit integers
(`subkeys_tdes`).
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.Cmac Proof.Cmac

theorem blocks_eq8 {msg : List Byte} (last : List Byte) (q : Nat) (hq : msg.length = 8 * q) :
    (List.range q).map (fun i => ((msg ++ last).drop (8 * i)).take 8) = blocks 8 msg := by
  simp only [blocks, hq, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- §6.2 steps 3–6, for a message of whole blocks `msg` followed by `last`. -/
theorem macFull_split8 (ciph : Cipher) {msg last : List Byte} (hm : msg.length % 8 = 0)
    (hl : last.length ≤ 8) (hne : msg = [] ∨ 0 < last.length) :
    macFull ciph 8 (msg ++ last) =
      ciph (xor (chain ciph (zeros 8) (blocks 8 msg))
        (lastBlock 8 (subkeys ciph 8).1 (subkeys ciph 8).2 last)) := by
  obtain ⟨q, hq⟩ : ∃ q, msg.length = 8 * q := ⟨msg.length / 8, by omega⟩
  have hn : (if (msg ++ last).length = 0 then 1 else ((msg ++ last).length + 8 - 1) / 8) = q + 1 := by
    rw [List.length_append]
    split
    · omega
    · have hl0 : 0 < last.length := by
        rcases hne with h | h
        · subst h; simp only [List.length_nil] at *; omega
        · exact h
      omega
  simp only [macFull, hn, Nat.add_sub_cancel]
  rw [VG.Proof.CmacTripleDes.blocks_eq8 last q hq, chain_append, chain_single,
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

open VG.WriteBytes in
/-- The padded last block `Mₙ* ‖ 10ʲ`, from the bytes copied onto zeros. -/
theorem padded_bytes8 (m : Mem) (C : Addr) (xs : List Byte) (hL : xs.length < 8)
    (hz : Spec.Aes.bytesAt m C 8 = zeros 8) :
    Spec.Aes.bytesAt ((writeBytes m C xs).writeW (C + BitVec.ofNat 64 xs.length) (0x80 : Byte)) C 8 =
      xs ++ [0x80] ++ zeros (8 - xs.length - 1) := by
  refine VG.Proof.CmacTripleDes.ext8 (by simp [Spec.Aes.bytesAt]) (by simp [zeros]; omega) fun k hk => ?_
  rw [getD_bytesAt _ _ hk, writeW8_apply]
  have hz' : m (C + BitVec.ofNat 64 k) = 0 := by
    have := congrArg (fun l => l.getD k 0) hz
    rw [getD_bytesAt _ _ hk] at this
    rw [this]; simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk,
      ite_true, Option.getD_some]
  have hsub : (C + BitVec.ofNat 64 k - C).toNat = k := Mem.sub_ofNat_toNat C (by omega)
  have heq : (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) ↔ k = xs.length := by
    constructor
    · intro h
      have := congrArg (fun a => (a - C).toNat) h
      simp only [Mem.sub_ofNat_toNat C (show k < 2 ^ 64 by omega),
        Mem.sub_ofNat_toNat C (show xs.length < 2 ^ 64 by omega)] at this
      exact this
    · intro h; rw [h]
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, h, ite_true]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, show ¬ k < xs.length by omega, hz']
    obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, zeros, List.getElem?_replicate]
    simp only [show j < 8 - xs.length - 1 by omega, ite_true, Option.getD_some]

/-- TDEA's subkeys: `L = CIPH_K(0⁶⁴)` doubled once and twice, as 64-bit integers. -/
theorem subkeys_tdes (S : Spec.TripleDes.Schedule) :
    subkeys (tdesWith S) 8 =
      (le8 (byteRev64 (VG.Proof.CmacTripleDes.dbl64 (VG.Proof.CmacTripleDes.tdes S 0))), le8 (byteRev64 (VG.Proof.CmacTripleDes.dbl64 (VG.Proof.CmacTripleDes.dbl64 (VG.Proof.CmacTripleDes.tdes S 0))))) := by
  have hz : zeros 8 = le8 0 := le8_zero.symm
  have hr : byteRev64 0 = 0 := by decide
  simp only [subkeys, hz, VG.Proof.CmacTripleDes.tdesWith_le8, hr, VG.Proof.CmacTripleDes.dbl_le8]

/-! ## The key schedule from the key's bytes -/

/-- The offset of DES key `i` in a TDEA key of `n` bytes. -/
def keyOff (n i : Nat) : Nat := if i = 2 ∧ n = 16 then 0 else 8 * i

/-- Slot `16 i + j` of the key schedule: round key `j` of DES key `i`. -/
theorem expandKey_getD (key : List Byte) {i j : Nat} (hi : i < 3) (hj : j < 16) :
    (Spec.TripleDes.expandKey key).getD (16 * i + j) 0 =
      ((Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Vector.ofFn fun t => key.getD (VG.Proof.CmacTripleDes.keyOff key.length i + t.val) 0))).getD j 0).zeroExtend 64 := by
  rw [VG.Proof.CmacTripleDes.vgetD _ (by omega), Spec.TripleDes.expandKey, Vector.getElem_ofFn]
  simp only [show (16 * i + j) % 16 = j by omega, VG.Proof.CmacTripleDes.keyOff]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · simp [show j < 16 from hj]
  · simp [show ¬ 16 + j < 16 by omega, show 16 + j < 32 by omega]
  · simp [show ¬ 32 + j < 16 by omega, show ¬ 32 + j < 32 by omega]

/-- A DES key in memory, as a big-endian integer. -/
theorem decode_bytesAt (m : Mem) (p : Addr) {n off : Nat} (h : off + 8 ≤ n) :
    Spec.TripleDes.decodeBlock (Vector.ofFn fun t => (Spec.Aes.bytesAt m p n).getD (off + t.val) 0) =
      byteRev64 (m.readW (p + BitVec.ofNat 64 off) 64) := by
  rw [← VG.Proof.CmacTripleDes.decode_le8, le8_readW]
  congr 1
  apply Vector.ext
  intro t ht
  simp only [Vector.getElem_ofFn]
  rw [getD_bytesAt _ _ (by omega), getD_bytesAt _ _ ht, Offset.add_add]

theorem msb_shift (y : BitVec 64) : y >>> 63 = if y.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases hm : 2 ^ (64 - 1) ≤ y.toNat
  · rw [decide_eq_true hm]; simp; omega
  · rw [decide_eq_false hm]; simp; omega

/-- The doubling as `init` computes it. -/
theorem dbl64_eq (y : BitVec 64) :
    (y + y) ^^^ (((0 : BitVec 64) - (y >>> 63)) &&& BitVec.signExtend 64 (0x1b : BitVec 32)) = VG.Proof.CmacTripleDes.dbl64 y := by
  have h : y + y = y <<< 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [h, VG.Proof.CmacTripleDes.msb_shift, VG.Proof.CmacTripleDes.dbl64]
  congr 1
  split <;> decide

end VG.Proof.CmacTripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.IndexLit`. -/
section

/-!
# The key schedule's bit maps as tables, for the kernel

Each evaluated once, here: the code built from them on every target (the
round's, `IP`'s and `IP⁻¹`'s bit permutations, `roundKeys`), its checks and
`keyBit_eq` read the tables rather than evaluate the specification's
permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.expSrc 48
materialize_table Impl.CmacTripleDes.pSrc 32
materialize_table Impl.CmacTripleDes.ipSrc 64
materialize_table Impl.CmacTripleDes.fpSrc 64
materialize_table Impl.CmacTripleDes.pc1Src 56
materialize_table Impl.CmacTripleDes.rkSrc 16 48

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.KeySchedule`. -/
section

/-!
# DES's key schedule, bit by bit

`expandDesKey` only moves the key's bits: bit `q` of round key `j` is bit
`rkSrc j q` of the key (`getLsbD_expandDesKey`), as the implementations
compute it. The proof follows `C` and `D` through the specification's loop
as maps of bit indices (`cIdx`), and compares the result with `rkSrc` by
`decide`.
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes Impl.CmacTripleDes

/-- Bit `i` of a 28-bit word rotated left by `r` is bit `rotIdx r i` of the word. -/
def rotIdx (r i : Nat) : Nat := (i + 28 - r % 28) % 28

theorem getLsbD_rotateLeft28 (x : BitVec 28) (r : Nat) {i : Nat} (hi : i < 28) :
    (x.rotateLeft r).getLsbD i = x.getLsbD (VG.Proof.CmacTripleDes.rotIdx r i) := by
  rw [BitVec.getLsbD_rotateLeft, VG.Proof.CmacTripleDes.rotIdx]
  have := Nat.mod_lt r (show 0 < 28 by decide)
  split
  · congr 1; omega
  · rw [decide_eq_true hi, Bool.true_and]; congr 1; omega

theorem rotIdx_lt (r i : Nat) : VG.Proof.CmacTripleDes.rotIdx r i < 28 := Nat.mod_lt _ (by decide)

/-- Bit `i` of `C` (or `D`) after `n` rotations is bit `cIdx n i` of the first. -/
def cIdx : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => VG.Proof.CmacTripleDes.cIdx n (VG.Proof.CmacTripleDes.rotIdx (rotations.getD n 0) i)

theorem cIdx_lt (n : Nat) {i : Nat} (hi : i < 28) : VG.Proof.CmacTripleDes.cIdx n i < 28 := by
  induction n generalizing i with
  | zero => exact hi
  | succ n ih => exact ih (Nat.mod_lt _ (by decide))

/-- Bit `q` of a round key, from `C` and `D` after the round's rotations. -/
def keyBit (c d : BitVec 28) (n q : Nat) : Bool :=
  let u := 56 - pc2.getD (47 - q) 1
  if u < 28 then d.getLsbD (VG.Proof.CmacTripleDes.cIdx n u) else c.getLsbD (VG.Proof.CmacTripleDes.cIdx n (u - 28))

/-- The loop of `expandDesKey`. -/
def ksStep (b : BitVec 28 × BitVec 28 × DesSchedule) (a : Nat) : BitVec 28 × BitVec 28 × DesSchedule :=
  (b.1.rotateLeft (rotations.getD a 0), b.2.1.rotateLeft (rotations.getD a 0),
    b.2.2.set! a (permute pc2 (b.1.rotateLeft (rotations.getD a 0) ++ b.2.1.rotateLeft (rotations.getD a 0))))

theorem pc2_u : ∀ q < 48, 56 - pc2.getD (47 - q) 1 < 56 := by decide +kernel

theorem ksFold (c₀ d₀ : BitVec 28) {n : Nat} (hn : n ≤ 16) :
    let st := (List.range n).foldl VG.Proof.CmacTripleDes.ksStep (c₀, d₀, Vector.replicate 16 0)
    (∀ i < 28, st.1.getLsbD i = c₀.getLsbD (VG.Proof.CmacTripleDes.cIdx n i)) ∧
    (∀ i < 28, st.2.1.getLsbD i = d₀.getLsbD (VG.Proof.CmacTripleDes.cIdx n i)) ∧
    ∀ j < n, ∀ q < 48, (st.2.2.getD j 0).getLsbD q = VG.Proof.CmacTripleDes.keyBit c₀ d₀ (j + 1) q := by
  induction n with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨hc, hd, hk⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun j hj q hq => ?_⟩
    · rw [VG.Proof.CmacTripleDes.ksStep, VG.Proof.CmacTripleDes.getLsbD_rotateLeft28 _ _ hi, hc _ (VG.Proof.CmacTripleDes.rotIdx_lt _ _), VG.Proof.CmacTripleDes.cIdx]
    · rw [VG.Proof.CmacTripleDes.ksStep, VG.Proof.CmacTripleDes.getLsbD_rotateLeft28 _ _ hi, hd _ (VG.Proof.CmacTripleDes.rotIdx_lt _ _), VG.Proof.CmacTripleDes.cIdx]
    · simp only [VG.Proof.CmacTripleDes.ksStep]
      rw [VG.Proof.CmacTripleDes.vgetD _ (by omega)]
      by_cases hjn : j = n
      · subst hjn
        rw [Vector.getElem_set!_self (by omega), VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) hq, BitVec.getLsbD_append,
          VG.Proof.CmacTripleDes.keyBit]
        have hu := VG.Proof.CmacTripleDes.pc2_u q hq
        rw [show 48 - 1 - q = 47 - q by omega]
        split
        · rename_i hu'
          rw [VG.Proof.CmacTripleDes.getLsbD_rotateLeft28 _ _ hu', hd _ (VG.Proof.CmacTripleDes.rotIdx_lt _ _)]
          rfl
        · rename_i hu'
          rw [VG.Proof.CmacTripleDes.getLsbD_rotateLeft28 _ _ (by omega), hc _ (VG.Proof.CmacTripleDes.rotIdx_lt _ _)]
          rfl
      · rw [Vector.getElem_set!_ne (by omega) (Ne.symm hjn), ← VG.Proof.CmacTripleDes.vgetD _ (by omega)]
        exact hk j (by omega) q hq

/-- `keyBit` from the key: the indices compose to `rkSrc`. -/
theorem keyBit_eq : ∀ j < 16, ∀ q < 48,
    (let u := 56 - pc2.getD (47 - q) 1
     if u < 28 then pc1Src (VG.Proof.CmacTripleDes.cIdx (j + 1) u) else pc1Src (28 + VG.Proof.CmacTripleDes.cIdx (j + 1) (u - 28))) = rkSrc j q := by
  lit_decide

/-- Bit `q` of round key `j` is bit `rkSrc j q` of the key. -/
theorem getLsbD_expandDesKey (key : BitVec 64) {j q : Nat} (hj : j < 16) (hq : q < 48) :
    ((expandDesKey key).getD j 0).getLsbD q = key.getLsbD (rkSrc j q) := by
  have h : expandDesKey key = ((List.range 16).foldl VG.Proof.CmacTripleDes.ksStep
      ((permute pc1 key >>> 28).setWidth 28, (permute pc1 key).setWidth 28, Vector.replicate 16 0)).2.2 := by
    simp only [expandDesKey, Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
    rfl
  rw [h, (VG.Proof.CmacTripleDes.ksFold _ _ (Nat.le_refl 16)).2.2 j hj q hq, VG.Proof.CmacTripleDes.keyBit, ← VG.Proof.CmacTripleDes.keyBit_eq j hj q hq]
  have hu := VG.Proof.CmacTripleDes.pc2_u q hq
  split
  · rename_i hu'
    have hc := VG.Proof.CmacTripleDes.cIdx_lt (j + 1) hu'
    rw [BitVec.getLsbD_setWidth, decide_eq_true hc, Bool.true_and,
      VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) (by omega)]
    dsimp only
    rw [ite_eq_left hu']
    rfl
  · rename_i hu'
    have hc := VG.Proof.CmacTripleDes.cIdx_lt (j + 1) (show 56 - pc2.getD (47 - q) 1 - 28 < 28 by omega)
    rw [BitVec.getLsbD_setWidth, decide_eq_true hc, Bool.true_and, BitVec.getLsbD_ushiftRight,
      VG.Proof.CmacTripleDes.getLsbD_permute _ _ (by decide) (by omega)]
    dsimp only
    rw [ite_eq_right hu']
    rfl

end VG.Proof.CmacTripleDes

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Words`. -/
section

/-!
# TDEA-CMAC: 64-bit words as two 32-bit words

Untrusted: everything here is checked by Lean. For the 32-bit targets: a
key schedule slot's round key from its two little-endian 32-bit words, and
a block (as a big-endian 64-bit integer) from its two.
-/

namespace VG.Proof.CmacTripleDes

open VG

/-- Bit `i` of a little-endian 32-bit word is bit `i % 8` of its byte `i / 8`. -/
theorem getLsbD_readW32 (m : Mem) (a : Addr) {i : Nat} (hi : i < 32) :
    (m.readW a 32).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega

/-- A slot's round key: the low 16 bits of its high word, and its low word. -/
theorem setWidth48_readW (m : Mem) (a : Addr) :
    (m.readW a 64).setWidth 48 = (m.readW (a + BitVec.ofNat 64 4) 32).setWidth 16 ++ m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, decide_eq_true (by omega : i < 48), Bool.true_and,
    VG.Proof.CmacTripleDes.getLsbD_readW64 _ _ (by omega), BitVec.getLsbD_append]
  by_cases h : i < 32
  · rw [ite_eq_left h, VG.Proof.CmacTripleDes.getLsbD_readW32 _ _ h]
  · rw [ite_eq_right h, BitVec.getLsbD_setWidth, decide_eq_true (by omega : i - 32 < 16), Bool.true_and,
      VG.Proof.CmacTripleDes.getLsbD_readW32 _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 + (i - 32) / 8 = i / 8 by omega, show (i - 32) % 8 = i % 8 by omega]

/-- A little-endian 64-bit word: its high 32-bit word, then its low one. -/
theorem readW64_split (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.CmacTripleDes.getLsbD_readW64 _ _ hi, BitVec.getLsbD_append]
  by_cases h : i < 32
  · rw [ite_eq_left h, VG.Proof.CmacTripleDes.getLsbD_readW32 _ _ h]
  · rw [ite_eq_right h, VG.Proof.CmacTripleDes.getLsbD_readW32 _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 + (i - 32) / 8 = i / 8 by omega, show (i - 32) % 8 = i % 8 by omega]

theorem getLsbD_byteRev32 (w : BitVec 32) {i : Nat} (hi : i < 32) :
    (byteRev32 w).getLsbD i = w.getLsbD (8 * (3 - i / 8) + i % 8) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [byteRev32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- Two words byte-reversed, as one: the block `y ‖ x` (as a big-endian
integer) is the bytes of `x` then `y`. -/
theorem byteRev32_append (x y : BitVec 32) : byteRev32 x ++ byteRev32 y = byteRev64 (y ++ x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.CmacTripleDes.getLsbD_byteRev64 _ hi, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h : i < 32
  · rw [ite_eq_left h, VG.Proof.CmacTripleDes.getLsbD_byteRev32 _ h, ite_eq_right (by omega)]
    congr 1; omega
  · rw [ite_eq_right h, VG.Proof.CmacTripleDes.getLsbD_byteRev32 _ (by omega), ite_eq_left (by omega)]
    congr 1; omega

/-! ## Shifting and doubling `hi:lo` -/

/-- A round key's words: the high one's upper half is zero. -/
theorem append_of_hi (hi lo : BitVec 32) (h : hi >>> 16 = 0) :
    hi ++ lo = (hi.setWidth 16 ++ lo).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  rw [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, decide_eq_true hq, Bool.true_and, BitVec.getLsbD_append]
  by_cases h32 : q < 32
  · rw [ite_eq_left h32, ite_eq_left h32]
  · rw [ite_eq_right h32, ite_eq_right h32, BitVec.getLsbD_setWidth]
    by_cases h48 : q - 32 < 16
    · rw [decide_eq_true h48, Bool.true_and]
    · rw [decide_eq_false h48, Bool.false_and]
      have := congrArg (fun x => x.getLsbD (q - 48)) h
      simp only [BitVec.getLsbD_ushiftRight] at this
      rw [show 16 + (q - 48) = q - 32 by omega] at this
      exact this.trans (by simp)

/-- Shifting the 64-bit integer `hi:lo` left by one, a word at a time. -/
theorem shl_append (hi lo : BitVec 32) : (hi <<< 1 ||| lo >>> 31) ++ lo <<< 1 = (hi ++ lo) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have h64 : i < 64 := by omega
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  by_cases h0 : i = 0
  · subst h0; simp
  by_cases h32 : i < 32
  · simp [h32, h0, h64, show i - 1 < 32 by omega]
  by_cases h32' : i = 32
  · subst h32'; simp
  · have h1 : ¬ (i - 1 < 32) := by omega
    have h2 : ¬ (31 + (i - 32) < 32) := by omega
    simp [h32, h1, h0, h64, show i - 32 < 32 by omega, show i - 1 - 32 = i - 32 - 1 by omega,
      show ¬ (i - 32 < 1) by omega, BitVec.getLsbD_of_ge lo (31 + (i - 32)) (by omega)]

theorem shr31 (x : BitVec 32) : x >>> 31 = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0; split <;> simp_all
  · rw [BitVec.getLsbD_of_ge x _ (by omega)]
    split <;> simp [BitVec.getLsbD_one, BitVec.getLsbD_zero, h0]

/-- `dbl` doubles `hi:lo` (`dbl64`). -/
theorem dbl_append (hi lo : BitVec 32) :
    (hi <<< 1 ||| lo >>> 31) ++ (lo <<< 1 ^^^ (((0 : BitVec 32) - (hi >>> 31)) &&& (0x1b : BitVec 32))) =
      VG.Proof.CmacTripleDes.dbl64 (hi ++ lo) := by
  have hm : (hi ++ lo).msb = hi.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_append]; simp
  have hc : ((0 : BitVec 32) - (if hi.msb then (1 : BitVec 32) else 0)) &&& (0x1b : BitVec 32) =
      if hi.msb then 0x1b else 0 := by split <;> rfl
  rw [VG.Proof.CmacTripleDes.dbl64, hm, ← VG.Proof.CmacTripleDes.shl_append, VG.Proof.CmacTripleDes.shr31 hi, hc]
  split
  · rw [show (0x1b : BitVec 64) = (0 : BitVec 32) ++ (0x1b : BitVec 32) from rfl, BitVec.xor_append]
    simp
  · rw [show (0 : BitVec 64) = (0 : BitVec 32) ++ (0 : BitVec 32) from rfl, BitVec.xor_append]
    simp

/-- Doubling a word by adding it to itself. -/
theorem add_self (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

end VG.Proof.CmacTripleDes

end
