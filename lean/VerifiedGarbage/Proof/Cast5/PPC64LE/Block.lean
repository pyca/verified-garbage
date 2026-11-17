module

import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `Cast5.PPC64LE.Scan`, which this module and modules that import it used -/

section

/-!
# CAST5 on PPC64LE: the scan of a table

`scan` visits the 256 entries of the table at `tbl`, in order, eight at a
time, and leaves in `r18 + k` word `k` of the entry whose number is in
`r14 + k` (`scan_ok`), zero-extended. The vectors are reasoned about a byte
at a time: byte `i` of a vector is in lane `i / 4`, which serves lookup
`lk i` (a loaded entry holds word `k` in lane `k XOR 1`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE


/-- Word `k` of entry `e` of the table at `T`, zero-extended. -/
abbrev tw (m : Mem) (T : Addr) (e k : Nat) : BitVec 64 := (ent m T e k).setWidth 64

/-- The registers the scan writes. -/
def loopRegs : List Reg := [tmp, wd, num, ep, .r18, .r19, .r20, .r21]

/-- What a scan needs: the indices below 256, zero in `r0`, and the table,
4096 bytes at `tbl`, readable. -/
structure ScanPre (s : State) : Prop where
  idx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256
  zero : s.gpr .r0 = 0
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr

/-! ## The setup -/

theorem hi64 (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]

theorem lo64 (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]


/-- `y` (below 256) in every byte of the low word. -/
def rep4 (y : BitVec 64) : BitVec 64 := y ||| y <<< 8 ||| (y ||| y <<< 8) <<< 16

/-- The lanes `y 1, y 0, y 3, y 2`, each replicated. -/
def pack (y : Nat → BitVec 64) : BitVec 128 :=
  (rep4 (y 0) ||| rep4 (y 1) <<< 32) ++ (rep4 (y 2) ||| rep4 (y 3) <<< 32)

/-- The lookup lane `i / 4` serves: word `k` of an entry is in lane `k XOR 1`. -/
def lk (i : Nat) : Nat := [1, 0, 3, 2].getD (i / 4) 0

theorem rep4_bit (b : Byte) {n : Nat} (hn : n < 64) :
    (rep4 (b.setWidth 64)).getLsbD n = (decide (n < 32) && b.getLsbD (n % 8)) := by
  obtain z : ∀ m, 8 ≤ m → b.getLsbD m = false := fun m h => BitVec.getLsbD_of_ge b m h
  simp only [rep4, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hn, decide_true,
    Bool.true_and]
  by_cases h8 : n < 8
  · simp [h8, show n < 32 by omega_using [h8], show n < 16 by omega_using [h8], Nat.mod_eq_of_lt h8]
  by_cases h16 : n < 16
  · simp [h8, h16, show n < 32 by omega_using [h16], show n - 8 < 8 by omega_using [h16], z n (by omega_using [h8]),
      show n % 8 = n - 8 by omega_using [h8, h16], show n - 8 < 64 by omega_using [hn]]
  by_cases h24 : n < 24
  · simp [h8, h16, show n < 32 by omega_using [h24], z n (by omega_using [h8]), z (n - 8) (by omega_using [h16]),
      show n % 8 = n - 16 by omega_using [h16, h24], show n - 16 < 64 by omega_using [hn], show n - 16 < 8 by omega_using [h24], show n - 8 < 64 by omega_using [hn]]
  by_cases h32 : n < 32
  · simp [h8, h16, h32, z n (by omega_using [h8]), z (n - 8) (by omega_using [h16]), z (n - 16) (by omega_using [h24]),
      show n % 8 = n - 24 by omega_using [h24, h32], show n - 16 - 8 = n - 24 by omega_using [], show n - 24 < 8 by omega_using [h32],
      show n - 16 < 64 by omega_using [hn], show n - 8 < 64 by omega_using [hn], show ¬ n - 16 < 8 by omega_using [h24],
      show n - 24 < 64 by omega_using [hn]]
  · simp [h8, h16, h32, z n (by omega_using [h8]), z (n - 8) (by omega_using [h16]), z (n - 16) (by omega_using [h24]),
      z (n - 16 - 8) (by omega_using [h32]), show n - 16 < 64 by omega_using [hn], show n - 8 < 64 by omega_using [hn]]

theorem vbyte_pack (b : Nat → Byte) {i : Nat} (hi : i < 16) :
    vbyte (pack fun k => (b k).setWidth 64) i = b (lk i) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, pack, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hr, decide_true, Bool.true_and]
  rcases (by omega_using [hi] : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with h | h | h | h
  · rw [show lk i = 1 by simp [lk, h]]
    simp only [show ¬ 8 * (15 - i) + r < 64 by omega_using [h], ite_false]
    rw [rep4_bit _ (by omega_using [hr]), rep4_bit _ (by omega_using [hr])]
    simp [show ¬ 8 * (15 - i) + r - 64 < 32 by omega_using [h], show 8 * (15 - i) + r - 64 < 64 by omega_using [hr],
      show (8 * (15 - i) + r - 64 - 32) % 8 = r by omega_using [hr, h], show 8 * (15 - i) + r - 64 - 32 < 32 by omega_using [hr]]
  · rw [show lk i = 0 by simp [lk, h]]
    simp only [show ¬ 8 * (15 - i) + r < 64 by omega_using [h], ite_false]
    rw [rep4_bit _ (by omega_using [hr])]
    simp [show 8 * (15 - i) + r - 64 < 32 by omega_using [hr, h], show (8 * (15 - i) + r - 64) % 8 = r by omega_using [hr, h]]
  · rw [show lk i = 3 by simp [lk, h]]
    simp only [show 8 * (15 - i) + r < 64 by omega_using [hr, h], ite_true]
    rw [rep4_bit _ (by omega_using [hr, h]), rep4_bit _ (by omega_using [hr, h])]
    simp [show ¬ 8 * (15 - i) + r < 32 by omega_using [h],
      show (8 * (15 - i) + r - 32) % 8 = r by omega_using [hr, h], show 8 * (15 - i) + r - 32 < 32 by omega_using [hr, h]]
  · rw [show lk i = 2 by simp [lk, h]]
    simp only [show 8 * (15 - i) + r < 64 by omega_using [hr, h], ite_true]
    rw [rep4_bit _ (by omega_using [hr, h])]
    simp [show 8 * (15 - i) + r < 32 by omega_using [hr, h], show (8 * (15 - i) + r) % 8 = r by omega_using [hr]]

/-- Byte `p` of the 32-byte one-hot vector in `hotLo` and `hotHi`. -/
def hotByte (u : State) (p : Nat) : Byte := if p < 16 then vbyte (u.vpr hotLo) p else vbyte (u.vpr hotHi) (p - 16)

theorem start_ok (s : State) :
    WP isa (.block scanStart) s fun t =>
      t.vpr lowV = pack (fun k => s.gpr (idxReg k) &&& 7#64) ∧
      t.vpr grpV = pack (fun k => s.gpr (idxReg k) >>> 3) ∧ t.vpr zV = 0 ∧
      (∃ u : BitVec 64, t.vpr (bitV 0) = permSelf (0x00FF00FF00FF00FF#64 ++ u) (t.vpr lowV)) ∧
      (∃ u : BitVec 64, t.vpr (bitV 1) = permSelf (0x0000FFFF0000FFFF#64 ++ u) (t.vpr lowV)) ∧
      (∃ u : BitVec 64, t.vpr (bitV 2) = permSelf (0x00000000FFFFFFFF#64 ++ u) (t.vpr lowV)) ∧
      t.vpr hotLo = 0xFF000000000000000000000000000000#128 ∧ t.vpr hotHi = 0#128 ∧
      t.gpr ep = s.gpr tbl ∧ t.gpr num = 16#64 ∧ t.gpr .r19 = 32#64 ∧ t.gpr .r21 = 48#64 ∧
      t.mem = s.mem := by
  unfold scanStart lanes lane rep
  c5run [reduceVOpEval, lowV, grpV, aV, bV, tV, zV, hotLo, hotHi, bitV, vpr_writeV, gpr_writeV, mem_writeV,
    sldoi8_eq, hi64, lo64, pack, rep4, BitVec.xor_self]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, by decide⟩

/-! ## A group -/

theorem read_sixteen (m : Mem) (a : Addr) : m.read a 16 = m.readW a 128 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- `vsel`: `b` where the mask is set, `a` elsewhere. -/
def vsel (a b m : BitVec 128) : BitVec 128 := (a &&& ~~~m) ||| (b &&& m)

theorem body_run (u : State) {E : Addr} {M : BitVec 128} (h23 : u.gpr ep = E) (h0 : u.gpr .r0 = 0#64)
    (h22 : u.gpr num = 16#64) (h19 : u.gpr .r19 = 32#64) (h21 : u.gpr .r21 = 48#64)
    (hM : (ofVBytes fun i => if (vbyte (u.vpr .v2) i).toNat % 32 < 16 then
        vbyte (u.vpr .v6) ((vbyte (u.vpr .v2) i).toNat % 32)
      else vbyte (u.vpr .v7) ((vbyte (u.vpr .v2) i).toNat % 32 - 16)) = M)
    (r : ∀ a ∈ [E, E + 16#64, E + 32#64, E + 48#64, E + 64#64, E + 64#64 + 16#64, E + 64#64 + 32#64,
      E + 64#64 + 48#64], InRegions (u.rd ++ u.wr) a 16) :
    WP isa (.block scanBody) u fun t =>
      let L := fun a => swapDwords (u.mem.readW a 128)
      let B := fun b => u.vpr (bitV b)
      t.vpr accV = vsel (u.vpr accV)
        (vsel (vsel (vsel (L E) (L (E + 16#64)) (B 0)) (vsel (L (E + 32#64)) (L (E + 48#64)) (B 0)) (B 1))
          (vsel (vsel (L (E + 64#64)) (L (E + 64#64 + 16#64)) (B 0))
            (vsel (L (E + 64#64 + 32#64)) (L (E + 64#64 + 48#64)) (B 0)) (B 1)) (B 2)) M ∧
      t.vpr hotLo = BitVec.extractLsb' 128 128 ((u.vpr zV ++ u.vpr hotLo) <<< 120) ∧
      t.vpr hotHi = BitVec.extractLsb' 128 128 ((u.vpr hotLo ++ u.vpr hotHi) <<< 120) ∧
      t.vpr zV = u.vpr zV ∧ t.vpr grpV = u.vpr grpV ∧ t.vpr (bitV 0) = u.vpr (bitV 0) ∧
      t.vpr (bitV 1) = u.vpr (bitV 1) ∧ t.vpr (bitV 2) = u.vpr (bitV 2) ∧
      t.gpr ep = E + 64#64 + 64#64 ∧ t.gpr tmp = E + 64#64 + 64#64 - u.gpr tbl - 4096#64 ∧
      t.mem = u.mem := by
  obtain r0 := r E (by simp)
  obtain r1 := r (E + 16#64) (by simp)
  obtain r2 := r (E + 32#64) (by simp)
  obtain r3 := r (E + 48#64) (by simp)
  obtain r4 := r (E + 64#64) (by simp)
  obtain r5 := r (E + 64#64 + 16#64) (by simp)
  obtain r6 := r (E + 64#64 + 32#64) (by simp)
  obtain r7 := r (E + 64#64 + 48#64) (by simp)
  unfold scanBody four pick
  c5run [reduceVOpEval, eV, bitV, mV, hotLo, hotHi, grpV, zV, accV, vpr_writeV, gpr_writeV, mem_writeV,
    rd_writeV, wr_writeV, ↓read_sixteen, h23, h0, h22, h19, h21, r0, r1, r2, r3, r4, r5, r6, r7, hM, vsel]

/-! ## Bytes -/

theorem vbyte_zero (i : Nat) : vbyte 0#128 i = 0#8 := by simp [vbyte]

theorem vbyte_and (a b : BitVec 128) (i : Nat) : vbyte (a &&& b) i = vbyte a i &&& vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_or (a b : BitVec 128) (i : Nat) : vbyte (a ||| b) i = vbyte a i ||| vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_not (a : BitVec 128) {i : Nat} (hi : i < 16) : vbyte (~~~a) i = ~~~vbyte a i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp [vbyte, hr, show 8 * (15 - i) + r < 128 by omega]

theorem vbyte_vsel (a b m : BitVec 128) {i : Nat} (hi : i < 16) {c : Bool}
    (h : vbyte m i = if c then 255#8 else 0#8) : vbyte (vsel a b m) i = if c then vbyte b i else vbyte a i := by
  rw [vsel, vbyte_or, vbyte_and, vbyte_and, vbyte_not _ hi, h]
  cases c
  · simp only [Bool.false_eq_true, ite_false, show ~~~(0#8 : Byte) = BitVec.allOnes 8 by decide,
      BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]
  · simp only [ite_true, show (255#8 : Byte) = BitVec.allOnes 8 by decide, BitVec.not_allOnes, BitVec.and_zero,
      BitVec.zero_or, BitVec.and_allOnes]

theorem vbyte_load (m : Mem) (a : Addr) {k : Nat} (hk : k < 16) :
    vbyte (swapDwords (m.readW a 128)) k = m (a + BitVec.ofNat 64 (k ^^^ 7)) := by
  obtain e : ∀ k < 16, 15 - (if k < 8 then k + 8 else k - 8) = k ^^^ 7 := by decide
  rw [vbyte_swapDwords _ hk, vbyte, Mem.readW, BitVec.setWidth_eq, ← e k hk]
  exact Mem.extractLsb'_read m a (n := 16) (by split <;> omega_using [])

theorem vbyte_shift15 (x y : BitVec 128) {k : Nat} (hk : k < 16) :
    vbyte (BitVec.extractLsb' 128 128 ((x ++ y) <<< 120)) k = if k = 0 then vbyte x 15 else vbyte y (k - 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
    decide_true, Bool.true_and, show 128 + (8 * (15 - k) + r) < 128 + 128 by omega_using [hr],
    show ¬ 128 + (8 * (15 - k) + r) < 120 by omega_using [], decide_false, Bool.not_false]
  by_cases h0 : k = 0
  · rw [ite_eq_left h0, ite_eq_right (show ¬ 128 + (8 * (15 - k) + r) - 120 < 128 by omega_using [h0]),
      BitVec.getLsbD_extractLsb', decide_eq_true (show 8 * (15 - k) + r < 128 by omega_using [hr]), Bool.true_and,
      decide_eq_true hr, Bool.true_and]
    exact congrArg x.getLsbD (by omega_using [h0])
  · rw [ite_eq_right h0, ite_eq_left (show 128 + (8 * (15 - k) + r) - 120 < 128 by omega_using [hr, h0]),
      BitVec.getLsbD_extractLsb', decide_eq_true (show 8 * (15 - k) + r < 128 by omega_using [hr]), Bool.true_and,
      decide_eq_true hr, Bool.true_and]
    exact congrArg y.getLsbD (by omega_using [hk, h0])

theorem vbyte_perm2 (n m c : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (ofVBytes fun i => if (vbyte c i).toNat % 32 < 16 then vbyte n ((vbyte c i).toNat % 32)
      else vbyte m ((vbyte c i).toNat % 32 - 16)) i =
      if (vbyte c i).toNat % 32 < 16 then vbyte n ((vbyte c i).toNat % 32)
      else vbyte m ((vbyte c i).toNat % 32 - 16) := vbyte_packed _ hi

/-- The entry of the eight that the low three bits of `n` name. -/
theorem tree_sel {α : Type} (e : Nat → α) (n : Nat) :
    (if n.testBit 2 then (if n.testBit 1 then (if n.testBit 0 then e 7 else e 6) else
        (if n.testBit 0 then e 5 else e 4)) else
      (if n.testBit 1 then (if n.testBit 0 then e 3 else e 2) else (if n.testBit 0 then e 1 else e 0))) =
      e (n % 8) := by
  obtain tb : ∀ b < 3, n.testBit b = (n % 8).testBit b := fun b hb => by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp [hb]
  rw [tb 0 (by decide), tb 1 (by decide), tb 2 (by decide)]
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize n % 8 = r at this ⊢
  rcases (by omega_using [this] : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem toNat_small {y : BitVec 64} (h : y.toNat < 256) : (y.setWidth 8).setWidth 64 = y := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega_using [h]

/-- A lane's bytes: the low three bits of its index, or its group. -/
theorem vbyte_lanes (y : Nat → BitVec 64) (hy : ∀ k < 4, (y k).toNat < 256) {i : Nat} (hi : i < 16) :
    vbyte (pack y) i = BitVec.ofNat 8 (y (lk i)).toNat := by
  obtain hl : lk i < 4 := by unfold lk; rcases (by omega_using [hi] : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with
    h | h | h | h <;> simp [h]
  obtain e : pack y = pack fun k => (if k < 4 then (y k).setWidth 8 else (y k).setWidth 8).setWidth 64 := by
    unfold pack; simp only [show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide,
      show (3 : Nat) < 4 by decide, ite_true]
    rw [toNat_small (hy 0 (by decide)), toNat_small (hy 1 (by decide)), toNat_small (hy 2 (by decide)),
      toNat_small (hy 3 (by decide))]
  rw [e, vbyte_pack (fun k => if k < 4 then (y k).setWidth 8 else (y k).setWidth 8) hi]
  simp only [ite_self]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The doubleword of constants whose byte `j` is all ones exactly if bit `b`
of `j` is set. -/
def bitsWord : Nat → BitVec 64
  | 0 => 0x00FF00FF00FF00FF#64 | 1 => 0x0000FFFF0000FFFF#64 | _ => 0x00000000FFFFFFFF#64

theorem vbyte_bits (u : BitVec 64) {b j : Nat} (hb : b < 3) (hj : j < 8) :
    vbyte (bitsWord b ++ u) j = if j.testBit b then 255#8 else 0#8 := by
  obtain e : vbyte (bitsWord b ++ u) j = (bitsWord b).extractLsb' (8 * (7 - j)) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
      show ¬ 8 * (15 - j) + i < 64 by omega_using [hj], ite_false]
    congr 1; omega_using [hj]
  rw [e]
  have : ∀ b < 3, ∀ j < 8, (bitsWord b).extractLsb' (8 * (7 - j)) 8 = if j.testBit b then 255#8 else 0#8 := by
    decide
  exact this b hb j hj

/-! ## The loop -/

/-- The index of lookup `k`. -/
abbrev ix (s₀ : State) (k : Nat) : Nat := (s₀.gpr (idxReg k)).toNat

/-- The scan's state after `g` groups of eight entries, from `s₀`. -/
structure VScan (s₀ : State) (T : Addr) (g : Nat) (u : State) : Prop where
  le : g ≤ 32
  z : u.vpr zV = 0#128
  grp : ∀ i < 16, vbyte (u.vpr grpV) i = BitVec.ofNat 8 (ix s₀ (lk i) / 8)
  bits : ∀ b < 3, ∀ i < 16, vbyte (u.vpr (bitV b)) i = if (ix s₀ (lk i)).testBit b then 255#8 else 0#8
  hot : ∀ p < 32, hotByte u p = if p = g then 255#8 else 0#8
  acc : ∀ i < 16, ix s₀ (lk i) / 8 < g →
    vbyte (u.vpr accV) i = s₀.mem (T + BitVec.ofNat 64 (16 * ix s₀ (lk i) + (i ^^^ 7)))
  ep : u.gpr ep = T + BitVec.ofNat 64 (128 * g)
  o16 : u.gpr num = 16#64
  o32 : u.gpr .r19 = 32#64
  o48 : u.gpr .r21 = 48#64
  zero : u.gpr .r0 = 0
  tblR : u.gpr tbl = T
  keep : Keep loopRegs s₀ u
  mem : u.mem = s₀.mem

theorem lk_lt {i : Nat} (hi : i < 16) : lk i < 4 := by
  unfold lk; rcases (by omega_using [hi] : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with h | h | h | h <;> simp [h]

theorem body_step {s₀ : State} {T : Addr} (hidx : ∀ k < 4, ix s₀ k < 256)
    (hrT : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) {g : Nat} (hg : g < 32) {u : State} (I : VScan s₀ T g u) :
    WP isa (.block scanBody) u fun t =>
      VScan s₀ T (g + 1) t ∧ t.gpr tmp = BitVec.ofNat 64 (128 * (g + 1)) - BitVec.ofNat 64 4096 := by
  obtain hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  obtain ad : ∀ o, o + 16 ≤ 128 → InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (128 * g + o)) 16 := fun o ho => by
    rw [hrd]; exact ⟨_, hrT, Offset.contains_base T (by omega_using [hg, ho]) (by omega_using [hg, ho])⟩
  obtain f1 : ∀ o, T + BitVec.ofNat 64 (128 * g) + BitVec.ofNat 64 o = T + BitVec.ofNat 64 (128 * g + o) :=
    fun o => Offset.add_add _ _ _
  obtain f2 : ∀ o, T + BitVec.ofNat 64 (128 * g) + 64#64 + BitVec.ofNat 64 o = T + BitVec.ofNat 64 (128 * g + (64 + o)) :=
    fun o => by rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Offset.add_add, Offset.add_add]

  -- The eight addresses, as the code makes them, and their bytes.
  have e0 : T + BitVec.ofNat 64 (128 * g) = T + BitVec.ofNat 64 (128 * g + 16 * 0) := rfl
  obtain e1 : T + BitVec.ofNat 64 (128 * g) + 16#64 = T + BitVec.ofNat 64 (128 * g + 16 * 1) := f1 16
  obtain e2 : T + BitVec.ofNat 64 (128 * g) + 32#64 = T + BitVec.ofNat 64 (128 * g + 16 * 2) := f1 32
  obtain e3 : T + BitVec.ofNat 64 (128 * g) + 48#64 = T + BitVec.ofNat 64 (128 * g + 16 * 3) := f1 48
  obtain e4 : T + BitVec.ofNat 64 (128 * g) + 64#64 = T + BitVec.ofNat 64 (128 * g + 16 * 4) := f1 64
  obtain e5 : T + BitVec.ofNat 64 (128 * g) + 64#64 + 16#64 = T + BitVec.ofNat 64 (128 * g + 16 * 5) := f2 16
  obtain e6 : T + BitVec.ofNat 64 (128 * g) + 64#64 + 32#64 = T + BitVec.ofNat 64 (128 * g + 16 * 6) := f2 32
  obtain e7 : T + BitVec.ofNat 64 (128 * g) + 64#64 + 48#64 = T + BitVec.ofNat 64 (128 * g + 16 * 7) := f2 48
  obtain rin : ∀ a ∈ [T + BitVec.ofNat 64 (128 * g), T + BitVec.ofNat 64 (128 * g) + 16#64, T + BitVec.ofNat 64 (128 * g) + 32#64, T + BitVec.ofNat 64 (128 * g) + 48#64, T + BitVec.ofNat 64 (128 * g) + 64#64, T + BitVec.ofNat 64 (128 * g) + 64#64 + 16#64, T + BitVec.ofNat 64 (128 * g) + 64#64 + 32#64,
      T + BitVec.ofNat 64 (128 * g) + 64#64 + 48#64], InRegions (u.rd ++ u.wr) a 16 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h | h | h | h <;> rw [h]
    · rw [e0]; exact ad _ (by omega_using [])
    · rw [e1]; exact ad _ (by omega_using [])
    · rw [e2]; exact ad _ (by omega_using [])
    · rw [e3]; exact ad _ (by omega_using [])
    · rw [e4]; exact ad _ (by omega_using [])
    · rw [e5]; exact ad _ (by omega_using [])
    · rw [e6]; exact ad _ (by omega_using [])
    · rw [e7]; exact ad _ (by omega_using [])
  refine WP.mono (WP.keep [tmp, ep] (body_run u I.ep I.zero I.o16 I.o32 I.o48 rfl rin) (by decide) rfl)
    fun t ⟨⟨ta, tlo, thi, tz, tg, tb0, tb1, tb2, tep, ttmp, tm⟩, tk⟩ => ?_
  have hB : ∀ b < 3, ∀ i < 16, vbyte (u.vpr (bitV b)) i =
      if (ix s₀ (lk i)).testBit b then 255#8 else 0#8 := I.bits
  refine ⟨⟨by omega_using [hg], by rw [tz, I.z], fun i hi => by rw [tg, I.grp i hi], fun b hb i hi => ?_, fun p hp => ?_,
    fun i hi hlt => ?_, ?_, by rw [tk.gpr (by decide), I.o16], by rw [tk.gpr (by decide), I.o32],
    by rw [tk.gpr (by decide), I.o48], by rw [tk.gpr (by decide), I.zero], by rw [tk.gpr (by decide), I.tblR],
    (I.keep.trans tk).mono (by decide), tm.trans I.mem⟩, ?_⟩
  · rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
    · rw [tb0]; exact I.bits 0 (by decide) i hi
    · rw [tb1]; exact I.bits 1 (by decide) i hi
    · rw [tb2]; exact I.bits 2 (by decide) i hi
  · have h0 := I.hot
    unfold hotByte at h0 ⊢
    by_cases hp16 : p < 16
    · rw [ite_eq_left hp16, tlo, vbyte_shift15 _ _ hp16, I.z, vbyte_zero]
      by_cases e : p = 0
      · rw [ite_eq_left e, ite_eq_right (by omega_using [e])]
      · rw [ite_eq_right e]
        have := h0 (p - 1) (by omega_using [hp])
        rw [ite_eq_left (by omega_using [hp16])] at this
        rw [this]
        by_cases e' : p - 1 = g
        · rw [ite_eq_left e', ite_eq_left (by omega_using [e, e'])]
        · rw [ite_eq_right e', ite_eq_right (by omega_using [e'])]
    · rw [ite_eq_right hp16, thi, vbyte_shift15 _ _ (by omega_using [hp])]
      by_cases e : p - 16 = 0
      · rw [ite_eq_left e]
        have := h0 15 (by omega_using [])
        rw [ite_eq_left (by omega_using [])] at this
        rw [this]
        by_cases e' : 15 = g
        · rw [ite_eq_left e', ite_eq_left (by omega_using [hp16, e, e'])]
        · rw [ite_eq_right e', ite_eq_right (by omega_using [hp16, e, e'])]
      · rw [ite_eq_right e]
        have := h0 (p - 1) (by omega_using [hp])
        rw [ite_eq_right (by omega_using [e]), show p - 1 - 16 = p - 16 - 1 by omega_using []] at this
        rw [this]
        by_cases e' : p - 1 = g
        · rw [ite_eq_left e', ite_eq_left (by omega_using [hp16, e'])]
        · rw [ite_eq_right e', ite_eq_right (by omega_using [e'])]
  · -- The kept entries.
    obtain hl := lk_lt hi
    obtain hx := hidx _ hl
    obtain hm : vbyte (ofVBytes fun i => if (vbyte (u.vpr .v2) i).toNat % 32 < 16 then
        vbyte (u.vpr .v6) ((vbyte (u.vpr .v2) i).toNat % 32)
      else vbyte (u.vpr .v7) ((vbyte (u.vpr .v2) i).toNat % 32 - 16)) i =
        if decide (ix s₀ (lk i) / 8 = g) then 255#8 else 0#8 := by
      rw [vbyte_perm2 _ _ _ hi, show VReg.v2 = grpV from rfl, I.grp i hi, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show ix s₀ (lk i) / 8 < 2 ^ 8 by omega_using [hx]), Nat.mod_eq_of_lt (show ix s₀ (lk i) / 8 < 32 by omega_using [hx])]
      have := I.hot (ix s₀ (lk i) / 8) (by omega_using [hx])
      unfold hotByte at this
      rw [show VReg.v6 = hotLo from rfl, show VReg.v7 = hotHi from rfl, this]; simp
    rw [ta, vbyte_vsel _ _ _ hi hm]
    obtain hb : ∀ b < 3, vbyte (u.vpr (bitV b)) i = if (ix s₀ (lk i)).testBit b then 255#8 else 0#8 :=
      fun b hb => I.bits b hb i hi
    simp only [vbyte_vsel _ _ _ hi (hb 0 (by decide)), vbyte_vsel _ _ _ hi (hb 1 (by decide)),
      vbyte_vsel _ _ _ hi (hb 2 (by decide))]
    by_cases e : ix s₀ (lk i) / 8 = g
    · rw [ite_eq_left (by simpa using e), e7, e6, e5, e4, e3, e2, e1, e0,
        tree_sel (fun t => vbyte (swapDwords (u.mem.readW (T + BitVec.ofNat 64 (128 * g + 16 * t)) 128)) i),
        vbyte_load _ _ hi, Offset.add_add, I.mem]
      congr 3; omega_using [e]
    · rw [ite_eq_right (by simpa using e)]
      exact I.acc i hi (by omega_using [hlt, e])
  · rw [tep, e4, show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Offset.add_add]
    congr 2 <;> omega
  · rw [ttmp, I.tblR, e4, show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Offset.add_add,
      Offset.add_sub_cancel_left, show (4096#64 : BitVec 64) = BitVec.ofNat 64 4096 from rfl]
    congr 2 <;> omega

theorem start_inv (s : State) (h : ScanPre s) :
    WP isa (.block scanStart) s (VScan s (s.gpr tbl) 0) := by
  refine WP.mono (WP.keep [wd, tmp, .r18, .r19, .r20, .r21, ep, num] (start_ok s) (by decide) rfl)
    fun u ⟨⟨ul, ug, uz, ⟨u0, hu0⟩, ⟨u1, hu1⟩, ⟨u2, hu2⟩, ulo, uhi, uep, unum, u19, u21, um⟩, uk⟩ => ?_
  have hx : ∀ k < 4, ix s k < 256 := h.idx
  obtain hlow : ∀ i < 16, vbyte (u.vpr lowV) i = BitVec.ofNat 8 (ix s (lk i) % 8) := fun i hi => by
    rw [ul, vbyte_lanes _ (fun k hk => by rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) hi,
      BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  obtain bit : ∀ b < 3, ∀ (w : BitVec 64), ∀ i < 16, vbyte (permSelf (bitsWord b ++ w) (u.vpr lowV)) i =
      if (ix s (lk i)).testBit b then 255#8 else 0#8 := fun b hb w i hi => by
    obtain hm : ix s (lk i) % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [permSelf, vbyte_packed _ hi]
    simp only [hlow i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ix s (lk i) % 8 < 2 ^ 8 by omega_using []),
      Nat.mod_eq_of_lt (show ix s (lk i) % 8 < 32 by omega_using []), show ix s (lk i) % 8 < 16 by omega_using [], ite_true,
      vbyte_bits w hb hm]
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp [hb]
  refine ⟨by decide, uz, fun i hi => ?_, fun b hb i hi => ?_, fun p hp => ?_, fun i _ h => absurd h (by omega_using []),
    by rw [uep, BitVec.add_zero], unum, u19, u21, by rw [uk.gpr (by decide)]; exact h.zero,
    by rw [uk.gpr (by decide)], uk.mono (by decide), um⟩
  · rw [ug, vbyte_lanes _ (fun k hk => by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := hx k hk; simp only [ix] at this; omega_using [this]) hi,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
    · rw [hu0]; exact bit 0 (by decide) u0 i hi
    · rw [hu1]; exact bit 1 (by decide) u1 i hi
    · rw [hu2]; exact bit 2 (by decide) u2 i hi
  · unfold hotByte
    rw [ulo, uhi]
    have : ∀ p < 32, (if p < 16 then vbyte 0xFF000000000000000000000000000000#128 p else vbyte 0#128 (p - 16)) =
        if p = 0 then 255#8 else 0#8 := by decide
    exact this p hp

theorem scanLoop_run {s₀ : State} {T : Addr} (hidx : ∀ k < 4, ix s₀ k < 256)
    (hrT : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) {u : State} (I : VScan s₀ T 0 u) :
    WP isa (.loop (.block scanBody) (.nonzero .d tmp)) u (VScan s₀ T 32) := by
  refine WP.loop (M := isa) (Q := VScan s₀ T 32)
    (fun (n : Nat) (v : State) => ∃ g, g < 32 ∧ n = 32 - g ∧ VScan s₀ T g v) ?_ 32 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨g, hg, hn, J⟩
  refine WP.mono (body_step hidx hrT hg J) fun v' ⟨J', hz⟩ => ?_
  obtain hne : (BitVec.ofNat 64 (128 * (g + 1)) - BitVec.ofNat 64 4096 != 0#64) = !decide (g + 1 = 32) := by
    by_cases e : g + 1 = 32
    · rw [e]; rfl
    · have : BitVec.ofNat 64 (128 * (g + 1)) - BitVec.ofNat 64 4096 ≠ 0#64 := fun h' => by
        have := congrArg BitVec.toNat h'
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega_using [hg, e, this]
      simp [this, e]
  obtain ev : isa.eval (.nonzero .d tmp) v' = some (!decide (g + 1 = 32)) := by
    simp only [eval, State.read, BitVec.setWidth_eq]; rw [hz]; exact congrArg some hne
  by_cases e : g + 1 = 32
  · left
    exact ⟨by rw [ev, e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by rw [ev]; simp [e], n - 1, by omega_using [hg, hn], g + 1, by omega_using [hg, e], by omega_using [hn], J'⟩

/-! ## The words -/

/-- Bits `base` to `base + 31` of `v`, from its bytes. -/
theorem bits_of_bytes (v : BitVec 128) (w : BitVec 32) {base : Nat} (hb : base % 8 = 0) (hb' : base + 32 ≤ 128)
    (h : ∀ c < 4, vbyte v (15 - base / 8 - c) = w.extractLsb' (8 * c) 8) {n : Nat} (hn : n < 32) :
    v.getLsbD (base + n) = w.getLsbD n := by
  have := congrArg (BitVec.getLsbD · (n % 8)) (h (n / 8) (by omega_using [hn]))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show n % 8 < 8 by omega_using [], decide_true, Bool.true_and] at this
  rw [show base + n = 8 * (15 - (15 - base / 8 - n / 8)) + n % 8 by omega_using [hb, hb', hn], this]
  exact congrArg w.getLsbD (by omega_using [])

theorem lo_half (v : BitVec 128) (w : BitVec 32) {o : Nat} (ho : o = 0 ∨ o = 64)
    (h : ∀ c < 4, vbyte v (15 - o / 8 - c) = w.extractLsb' (8 * c) 8) :
    (v.extractLsb' o 64 <<< 32) >>> 32 = w.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro n hn
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  by_cases h32 : n < 32
  · simp only [show 32 + n < 64 by omega_using [h32], decide_true, Bool.true_and, show ¬ 32 + n < 32 by omega_using [],
      decide_false, Bool.not_false, show 32 + n - 32 = n by omega_using [], show n < 64 by omega_using [hn]]
    exact bits_of_bytes v w (by omega_using [ho]) (by omega_using [ho]) h h32
  · rw [BitVec.getLsbD_of_ge w n (by omega_using [h32])]
    simp [show ¬ 32 + n < 64 by omega_using [h32]]

theorem hi_half (v : BitVec 128) (w : BitVec 32) {o : Nat} (ho : o = 0 ∨ o = 64)
    (h : ∀ c < 4, vbyte v (15 - (o + 32) / 8 - c) = w.extractLsb' (8 * c) 8) :
    v.extractLsb' o 64 >>> 32 = w.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro n hn
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h32 : n < 32
  · simp only [show 32 + n < 64 by omega_using [h32], decide_true, Bool.true_and, show n < 64 by omega_using [hn]]
    rw [show o + (32 + n) = (o + 32) + n by omega_using []]
    exact bits_of_bytes v w (by omega_using [ho]) (by omega_using [ho]) h h32
  · rw [BitVec.getLsbD_of_ge w n (by omega_using [h32])]
    simp [show ¬ 32 + n < 64 by omega_using [h32]]

theorem end_run (v : State) :
    WP isa (.block scanEnd) v fun t =>
      t.gpr .r18 = ((v.vpr accV).extractLsb' 64 64 <<< 32) >>> 32 ∧
      t.gpr .r19 = (v.vpr accV).extractLsb' 64 64 >>> 32 ∧
      t.gpr .r20 = ((v.vpr accV).extractLsb' 0 64 <<< 32) >>> 32 ∧
      t.gpr .r21 = (v.vpr accV).extractLsb' 0 64 >>> 32 ∧ t.mem = v.mem := by
  unfold scanEnd
  c5run [reduceVOpEval, accV, tV, vpr_writeV, gpr_writeV, mem_writeV, sldoi8_eq, hi64, lo64, vdword]

/-- The scan: `r18 + k` is word `k` of the entry of the table whose number
is in `r14 + k`, zero-extended; only the scan's registers are written. -/
theorem scan_ok (s : State) (h : ScanPre s) :
    WP isa scan s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.gpr tbl) (s.gpr (idxReg k)).toNat k) ∧
      Keep loopRegs s t ∧ t.mem = s.mem := by
  unfold scan
  apply WP.seq
  refine WP.mono (start_inv s h) fun u U => ?_
  apply WP.seq
  refine WP.mono (scanLoop_run h.idx (h.trd) U) fun v V => ?_
  refine WP.mono (WP.keep [.r18, .r19, .r20, .r21] (end_run v) (by decide) rfl)
    fun t ⟨⟨t18, t19, t20, t21, tm⟩, tk⟩ => ⟨fun k hk => ?_, (V.keep.trans tk).mono (by decide), tm.trans V.mem⟩
  obtain byte : ∀ i < 16, vbyte (v.vpr accV) i =
      s.mem (s.gpr tbl + BitVec.ofNat 64 (16 * ix s (lk i) + (i ^^^ 7))) := fun i hi =>
    V.acc i hi (by have := h.idx _ (lk_lt hi); show (s.gpr (idxReg (lk i))).toNat / 8 < 32; omega_using [this])
  -- Byte `c` of word `k` is byte `i` of the vector, in lookup `lk i = k`'s lane.
  obtain wb : ∀ k < 4, ∀ i c, i < 16 → c < 4 → lk i = k → i ^^^ 7 = 4 * k + c →
      vbyte (v.vpr accV) i = (ent s.mem (s.gpr tbl) (ix s k) k).extractLsb' (8 * c) 8 := by
    intro k hk i c hi hc hl hx
    rw [byte i hi, ent, ← Mem.readW_byte _ _ hc, Offset.add_add, hl, hx, Nat.add_assoc]
  obtain l7 : ∀ c < 4, lk (7 - c) = 0 ∧ (7 - c) ^^^ 7 = 4 * 0 + c := by decide
  obtain l3 : ∀ c < 4, lk (3 - c) = 1 ∧ (3 - c) ^^^ 7 = 4 * 1 + c := by decide
  obtain l15 : ∀ c < 4, lk (15 - c) = 2 ∧ (15 - c) ^^^ 7 = 4 * 2 + c := by decide
  obtain l11 : ∀ c < 4, lk (11 - c) = 3 ∧ (11 - c) ^^^ 7 = 4 * 3 + c := by decide
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [show accReg 0 = .r18 from rfl, t18]
    exact lo_half _ _ (.inr rfl) fun c hc => wb 0 (by decide) _ c (by omega_using []) hc (l7 c hc).1 (l7 c hc).2
  · rw [show accReg 1 = .r19 from rfl, t19]
    exact hi_half _ _ (.inr rfl) fun c hc => wb 1 (by decide) _ c (by omega_using []) hc (l3 c hc).1 (l3 c hc).2
  · rw [show accReg 2 = .r20 from rfl, t20]
    exact lo_half _ _ (.inl rfl) fun c hc => wb 2 (by decide) _ c (by omega_using []) hc (l15 c hc).1 (l15 c hc).2
  · rw [show accReg 3 = .r21 from rfl, t21]
    exact hi_half _ _ (.inl rfl) fun c hc => wb 3 (by decide) _ c (by omega_using []) hc (l11 c hc).1 (l11 c hc).2

end VG.Proof.Cast5.PPC64LE

end

end

/-! ### `Cast5.PPC64LE.Round`, which only this module used -/

section

/-!
# CAST5 on PPC64LE: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`r14`–`r17` (`spread`), scans `VG_CAST5_S1234` and combines the four values
into `f` (`byType comb`), makes the Feistel step (`feistel`), and moves the
round's number modulo 3 and the count of rounds left on (`next`). The
code's words are the low words of registers (`lo`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE

/-! ## Choosing by the type -/

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t < 3)
    (hv : s.gpr typ = BitVec.ofNat 64 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [tmp] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl
  · exact WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => hQ _ (Keep.refl _ _) rfl)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (by decide) (by decide) fun u hu => wp_nil ?_)
    obtain k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => hQ _ k hu.mem)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_subi (by decide) (by decide) fun u hu => wp_nil ?_)
    obtain k : Keep [tmp] s u := ⟨fun r hr => hu.other r (by simpa using hr), hu.rd, hu.wr⟩
    refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide))
      (fun _ => hQ _ k hu.mem)

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t < 3) {kmw d : Spec.Cast5.Word}
    (hR : lo (s.gpr xR) = d) (hin : InRegions (s.rd ++ s.wr) (s.gpr km) 4)
    (hv : s.mem.readW (s.gpr km) 32 = kmw) :
    WP isa (.block (Impl.Cast5.PPC64LE.mix t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.mix t kmw d ∧ Keep [vI] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.PPC64LE.mix
    c5run [hin, hv]
    refine ⟨?_, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [hr, ite_false], rfl, rfl⟩⟩
    simp only [lo_add, lo_sub, lo_xor, lo_ext, hR]
    rfl

/-- Bit `b` of `k` as the rotation's mask: zero if it is set, all ones if not. -/
theorem rotMask_eq (k : BitVec 64) {b : Nat} (hb : b < 64) :
    (k <<< (63 - b)) >>> 63 - 1#64 = if k.getLsbD b then 0 else BitVec.allOnes 64 := by
  obtain e : (k <<< (63 - b)) >>> 63 = if k.getLsbD b then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases h0 : i = 0
    · subst h0
      obtain e1 : 63 - (63 - b) = b := by omega_using [hb]
      rw [Nat.add_zero, e1, decide_eq_true (show 63 < 64 by decide),
        decide_eq_false (show ¬ 63 < 63 - b by omega_using [])]
      cases k.getLsbD b <;> decide
    · rw [decide_eq_false (show ¬ 63 + i < 64 by omega_using [h0]), Bool.false_and]
      have : ∀ c : Bool, (if c then 1#64 else 0#64).getLsbD i = false := fun c => by
        cases c <;> simp [BitVec.getLsbD_one, h0]
      exact (this _).symm
  rw [e]
  split <;> decide

/-- Step `b` of the rotation of `a` (the low word of `vI`) by `k` (`vKr`):
the rotation by `2 ^ b` if bit `b` of `k` is set. -/
theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a : BitVec 32} {k : BitVec 64}
    (hI : lo (s.gpr vI) = a) (hK : s.gpr vKr = k) :
    WP isa (.block (rotateStep b)) s fun u =>
      lo (u.gpr vI) = a.rotateLeft (2 ^ b * (k.toNat / 2 ^ b % 2)) ∧ u.gpr vKr = k ∧
      Keep [msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
  obtain hn : 32 - 2 ^ b < 32 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  obtain hr : a.rotateRight (32 - 2 ^ b) = a.rotateLeft (2 ^ b) :=
    Proof.Cast5.rotateRight_eq_rotateLeft a (Nat.pow_pos (by decide)) (by
      rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
        subst h <;> decide)
  unfold rotateStep
  c5run [hK, hn, show 63 - b < 64 by omega_using []]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  rw [rotMask_eq k (by omega_using [hb])]
  simp only [lo_xor, lo_and, lo_ext, hI]
  rw [hr]
  obtain hb' : k.getLsbD b = (k.toNat / 2 ^ b % 2 == 1) := by
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
    simp [Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (k.toNat / 2 ^ b) with h | h
  · have hg : k.getLsbD b = false := by rw [hb', h]; rfl
    rw [hg, h, Nat.mul_zero, show lo (if false = true then 0 else BitVec.allOnes 64) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes, BitVec.xor_comm a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
  · have hg : k.getLsbD b = true := by rw [hb', h]; rfl
    rw [hg, h, Nat.mul_one]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]

theorem rotate_ok (s : State) {a kr : BitVec 32} (hI : lo (s.gpr vI) = a)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 4)
    (hv : s.mem.readW (s.gpr km + BitVec.ofNat 64 64) 32 = kr) :
    WP isa (.block rotate) s fun u =>
      lo (u.gpr vI) = a.rotateLeft (kr.toNat % 32) ∧ Keep [vKr, msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
  have e : rotate = [.load .w vKr km 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  obtain k0 : WP isa (.block [.load .w vKr km 64]) s fun u =>
      u.gpr vKr = kr.setWidth 64 ∧ lo (u.gpr vI) = a ∧ Keep [vKr, msk, tmp, wd, vI] s u ∧ u.mem = s.mem := by
    c5run [hin, hv]
    exact ⟨hI, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp only [hr.1, ite_false], rfl, rfl⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  obtain hk : (kr.setWidth 64).toNat = kr.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := kr.isLt; omega_using [])
  refine ⟨?_, ((((p₀.trans p₁).trans p₂).trans p₃).trans p₄).trans p₅ |>.mono fun r hr => ?_,
    by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  · rw [a₅]
    simp only [Proof.Cast5.rotateLeft_rotateLeft, hk]
    rw [← BitVec.rotateLeft_mod_eq_rotateLeft]
    congr 1
    simp only [Nat.reducePow, Nat.div_one, Nat.one_mul]
    omega_using []
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with ((((h | h | h | h | h) | h | h | h | h) | h | h | h | h) | h | h | h | h) | h | h | h | h <;>
      simp only [h, true_or, or_true]

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
abbrev idxOf (i : BitVec 32) (k : Nat) : Nat := i.toNat / 2 ^ (8 * k) % 256

theorem idxOf_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idxOf i k) = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, idxOf]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] <;> omega_using []

theorem and255_toNat (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem spread_ok (s : State) {i : BitVec 32} (hI : lo (s.gpr vI) = i) (h255 : s.gpr c255 = 255#64) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, (u.gpr (idxReg k)).toNat = idxOf i k) ∧ Keep [.r14, .r15, .r16, .r17] s u ∧ u.mem = s.mem := by
  unfold spread
  c5run [h255]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · have hi : i.toNat = (s.gpr .r28).toNat % 2 ^ 32 := by
      rw [← hI, BitVec.toNat_setWidth]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
      simp only [idxReg_0, idxReg_1, idxReg_2, idxReg_3, reduceCtorEq, ↓reduceIte, and255_toNat,
        BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, idxOf, Nat.reduceMul,
        Nat.reducePow, hi] <;>
      omega_using []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t < 3) :
    WP isa (.block (Impl.Cast5.PPC64LE.comb t)) s fun u =>
      lo (u.gpr vI) = Proof.Cast5.comb t (lo (s.gpr .r21)) (lo (s.gpr .r20)) (lo (s.gpr .r19))
        (lo (s.gpr .r18)) ∧ Keep [vI] s u ∧ u.mem = s.mem := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.PPC64LE.comb
    c5run
    refine ⟨?_, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [hr, ite_false], rfl, rfl⟩⟩
    simp only [lo_add, lo_sub, lo_xor]
    rfl

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr xL = s.gpr xR ∧ u.gpr xR = s.gpr vI ^^^ s.gpr xL ∧
      u.gpr km = (if up then s.gpr km + 4#64 else s.gpr km - 4#64) ∧ Keep [vI, xL, xR, km] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    c5run
    refine ⟨fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The number modulo 3 of the round after the one numbered `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 2 then 0 else t + 1) else (if t = 0 then 2 else t - 1)

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t < 3) (hv : s.gpr typ = BitVec.ofNat 64 t) :
    WP isa (next up) s fun u =>
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep [tmp, typ, left] s u ∧ u.mem = s.mem := by
  cases up <;>
  refine WP.mono (WP.keep [tmp, typ, left] (Q := fun u => u.gpr typ = BitVec.ofNat 64 (nextT _ t) ∧
    u.gpr left = s.gpr left - 1#64 ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩ <;>
  unfold next <;> rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega_using [ht]) with rfl | rfl | rfl <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · refine WP.seq (WP.ite true (by rw [eval_zero, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide)))
    c5run
    c5run [nextT]
  · refine WP.seq (WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_))
    c5run [hv]
    c5run [nextT]
    rfl
  · refine WP.seq (WP.ite false (by rw [eval_zero, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_))
    c5run [hv]
    c5run [nextT]
    rfl
  all_goals refine WP.seq (WP.seq (wp_subi (by decide) (by decide) fun u hu => wp_nil ?_))
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    obtain ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    obtain ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite false (by rw [eval_zero, hu.gpr, hv]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    obtain ut : u.gpr typ = s.gpr typ := hu.other _ (by decide)
    obtain ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run [ut, hv]
    c5run [ul, nextT, hu.mem]
    rfl
  · refine WP.ite true (by rw [eval_zero, hu.gpr, hv]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ul : u.gpr left = s.gpr left := hu.other _ (by decide)
    c5run
    c5run [ul, nextT, hu.mem]

/-! ## The round -/

/-- `f` of a round numbered `t` modulo 3 with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in the low words of `(r8, r9)`; `Kmᵢ` at
`km` and `Krᵢ` at `km + 64`; the round's number modulo 3 in `typ`; zero and
255 in their registers; and the table `VG_CAST5_S1234` at `tbl`, readable. -/
structure RoundPre (s : State) (kmw krw l r : Spec.Cast5.Word) (t : Nat) : Prop where
  xL : lo (s.gpr xL) = l
  xR : lo (s.gpr xR) = r
  inM : InRegions (s.rd ++ s.wr) (s.gpr km) 4
  valM : s.mem.readW (s.gpr km) 32 = kmw
  inR : InRegions (s.rd ++ s.wr) (s.gpr km + BitVec.ofNat 64 64) 4
  valR : s.mem.readW (s.gpr km + BitVec.ofNat 64 64) 32 = krw
  ht : t < 3
  typ : s.gpr typ = BitVec.ofNat 64 t
  zero : s.gpr .r0 = 0
  c255 : s.gpr c255 = 255#64
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234

/-- The registers a round writes. -/
def roundRegs : List Reg := [tmp, wd, num, ep, .r18, .r19, .r20, .r21, .r14, .r15, .r16, .r17, vI, vKr, msk,
  xL, xR, km, typ, left]

theorem round_ok (s : State) (up : Bool) {kmw krw l r : Spec.Cast5.Word} {t : Nat}
    (h : RoundPre s kmw krw l r t) :
    WP isa (round up) s fun u =>
      lo (u.gpr xL) = r ∧ lo (u.gpr xR) = l ^^^ fT t kmw krw r ∧
      u.gpr km = (if up then s.gpr km + 4#64 else s.gpr km - 4#64) ∧
      u.gpr typ = BitVec.ofNat 64 (nextT up t) ∧ u.gpr left = s.gpr left - 1#64 ∧
      Keep roundRegs s u ∧ u.mem = s.mem := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (WP.mono (byType_ok s Impl.Cast5.PPC64LE.mix (Q := fun v => lo (v.gpr vI) =
      Proof.Cast5.mix t kmw r ∧ Keep [tmp, vI] s v ∧ v.mem = s.mem) ht h.typ fun u uk um => ?_) fun v hv => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = s.gpr q := uk.gpr (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.xR)
      (by rw [uk.2.1, uk.2.2, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.trans vk), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [tmp, vI]) : v.gpr q = s.gpr q := vk.gpr hq
  -- The rotation and the indices.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rotate_ok v v1 (kr := krw) (by rw [vk.2.1, vk.2.2, gv _ (by decide)]; exact h.inR)
    (by rw [vm, gv _ (by decide)]; exact h.valR)) fun w ⟨w1, wk, wm⟩ => ?_
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t kmw r).rotateLeft (krw.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  obtain kw := vk.trans wk
  refine WP.mono (spread_ok w w1 (by rw [kw.gpr (by decide)]; exact h.c255)) fun x ⟨xi, xk, xm⟩ => ?_
  obtain kx := kw.trans xk
  obtain mx : x.mem = s.mem := xm.trans (wm.trans vm)
  obtain tx : x.gpr tbl = s.gpr tbl := kx.gpr (by decide)
  -- The scan.
  obtain sp : ScanPre x :=
    { idx := fun k hk => by rw [xi k hk]; exact Nat.mod_lt _ (by decide)
      zero := by rw [kx.gpr (by decide)]; exact h.zero
      trd := by rw [tx, kx.2.1, kx.2.2]; exact h.trd }
  refine WP.seq (WP.mono (scan_ok x sp) fun y ⟨ya, yk, ym⟩ => ?_)
  obtain ky := kx.trans yk
  obtain my : y.mem = s.mem := ym.trans mx
  obtain ty : y.gpr typ = BitVec.ofNat 64 t := by rw [ky.gpr (by decide)]; exact h.typ
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.PPC64LE.comb (Q := fun z => lo (z.gpr vI) = fT t kmw krw r ∧
      Keep [tmp, vI] y z ∧ z.mem = y.mem) ht ty fun u uk um => ?_) fun z ⟨z1, zk, zm⟩ => ?_)
  · have g (q : Reg) (hq : q ≠ tmp) : u.gpr q = y.gpr q := uk.gpr (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, uk.trans zk, zm.trans um⟩
    have ent' (k : Nat) (hk : k < 4) : lo (y.gpr (accReg k)) = Proof.Cast5.tableEnt Spec.Cast5.S4 Spec.Cast5.S3
        Spec.Cast5.S2 Spec.Cast5.S1 (idxOf i k) k := by
      rw [ya k hk, mx, xi k hk, tx, lo_ext]
      exact ent_table h.held (Nat.mod_lt _ (by decide)) hk
    obtain a0 : lo (y.gpr .r18) = _ := ent' 0 (by decide)
    obtain a1 : lo (y.gpr .r19) = _ := ent' 1 (by decide)
    obtain a2 : lo (y.gpr .r20) = _ := ent' 2 (by decide)
    obtain a3 : lo (y.gpr .r21) = _ := ent' 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [Proof.Cast5.tableEnt, idxOf_byte i (show 0 < 4 by decide), idxOf_byte i (show 1 < 4 by decide),
      idxOf_byte i (show 2 < 4 by decide), idxOf_byte i (show 3 < 4 by decide)]
  obtain kz := ky.trans zk
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, akm, ak, am⟩ => ?_)
  obtain ka := kz.trans ak
  refine WP.mono (next_ok a up ht (by rw [ka.gpr (by decide)]; exact h.typ)) fun b ⟨bt, bl, bk, bm⟩ => ?_
  obtain kb := ka.trans bk
  have gb (q : Reg) (hq : q ∉ [tmp, typ, left]) : b.gpr q = a.gpr q := bk.gpr hq
  refine ⟨by rw [gb _ (by decide), a2, kz.gpr (by decide)]; exact h.xR, ?_, ?_, bt,
    by rw [bl, ka.gpr (by decide)], kb.mono (by decide), by rw [bm, am, zm, my]⟩
  · rw [gb _ (by decide), a3, lo_xor, z1, kz.gpr (by decide), h.xL, BitVec.xor_comm]
  · rw [gb _ (by decide), akm, kz.gpr (by decide)]

end VG.Proof.Cast5.PPC64LE

end

end


/-!
# CAST5 on PPC64LE: the block function

`crypt up pr` encrypts (`up`) or decrypts the block at `pr` in place, with
the schedule at `sch` and the number of rounds in `rnd` (`crypt_ok`): it
loads the halves, runs the rounds in a loop (`rounds_ok`), each from the
state of the rounds (`RInv`), and stores them. It writes no memory but the
block's.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)

/-- `fT` of round `i`'s number modulo 3 is the spec's `f`. -/
theorem fT_eq (i : Nat) (km kr d : Spec.Cast5.Word) : fT (i % 3) km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]; rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- What the block function needs: the block at `p` in `pr` (a register
the rounds keep), writable; the schedule at `kb` in `sch`, readable; the
number of rounds `n` in `rnd`; zero and 255 in their registers; and the
table `VG_CAST5_S1234` at `tbl`, readable. -/
structure BPre (s : State) (pr : Reg) (p kb : Addr) (n : Nat) : Prop where
  ptr : s.gpr pr = p
  prOk : pr ∉ roundRegs ∧ pr ≠ .r0
  sched : s.gpr sch = kb
  rounds : s.gpr rnd = BitVec.ofNat 64 n
  nv : n = 12 ∨ n = 16
  zero : s.gpr .r0 = 0
  c255 : s.gpr c255 = 255#64
  trd : (⟨s.gpr tbl, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.gpr tbl) Impl.Cast5.s1234
  inP : ∃ r ∈ s.wr, ∀ off, off + 4 ≤ 8 → r.Contains (p + BitVec.ofNat 64 off) 4
  inK : (⟨kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  kfit : kb.toNat + 128 ≤ 2 ^ 64

section
variable {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
include h

theorem BPre.inK' {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.inK, Offset.contains_base _ hw (by have := h.kfit; omega_arith)⟩

theorem BPre.inP' {off : Nat} (hw : off + 4 ≤ 8) : InRegions s.wr (p + BitVec.ofNat 64 off) 4 :=
  let ⟨r, hr, hc⟩ := h.inP; ⟨r, hr, hc off hw⟩

end

/-! ## The rounds -/

/-- The state of a block's rounds, from `s`: the halves `lr`, the next
round's subkeys at `kp`, its number modulo 3 `t` and `left` rounds left. -/
structure RInv (s : State) (lr : Spec.Cast5.Word × Spec.Cast5.Word) (kp : Addr) (t nl : Nat)
    (u : State) : Prop where
  vL : lo (u.gpr xL) = lr.1
  vR : lo (u.gpr xR) = lr.2
  vkm : u.gpr km = kp
  vtyp : u.gpr typ = BitVec.ofNat 64 t
  vleft : u.gpr left = BitVec.ofNat 64 nl
  keep : Keep roundRegs s u
  mem : u.mem = s.mem

/-- The subkeys of round `i` (`1 … 16`) at `kp`. -/
theorem key_at (s : State) (kb : Addr) {j : Nat} (hj : j < 32) :
    s.mem.readW (kb + BitVec.ofNat 64 (4 * j)) 32 = (Spec.Cast5.scheduleAt s.mem kb).getD j 0 :=
  (Proof.Cast5.scheduleAt_getD _ _ hj).symm

/-- A round, from the state of the rounds. -/
theorem round_step {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {nl i : Nat}
    (hu : RInv s lr (kb + BitVec.ofNat 64 (4 * (i - 1))) (i % 3) nl u) (up : Bool)
    (hi : 1 ≤ i ∧ i ≤ 16) (hl : 1 ≤ nl ∧ nl < 2 ^ 64) :
    WP isa (round up) u fun v =>
      RInv s (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr)
        (if up then kb + BitVec.ofNat 64 (4 * (i - 1)) + 4#64 else kb + BitVec.ofNat 64 (4 * (i - 1)) - 4#64)
        (nextT up (i % 3)) (nl - 1) v := by
  have g (q : Reg) (hq : q ∉ roundRegs := by decide) : u.gpr q = s.gpr q := hu.keep.gpr hq
  obtain e64 : u.gpr km + BitVec.ofNat 64 64 = kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.vkm, Offset.add_add]; congr 2; omega_arith
  obtain pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem kb).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem kb).getD (15 + i) 0) lr.1 lr.2 (i % 3) :=
    { xL := hu.vL
      xR := hu.vR
      inM := by rw [hu.vkm, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valM := by rw [hu.vkm, hu.mem]; exact key_at s kb (by omega_arith)
      inR := by rw [e64, hu.keep.2.1, hu.keep.2.2]; exact h.inK' (by omega_arith)
      valR := by rw [e64, hu.mem]; exact key_at s kb (by omega_arith)
      ht := Nat.mod_lt _ (by decide)
      typ := hu.vtyp
      zero := by rw [g _]; exact h.zero
      c255 := by rw [g _]; exact h.c255
      trd := by rw [g tbl, hu.keep.2.1, hu.keep.2.2]; exact h.trd
      held := by rw [g tbl, hu.mem]; exact h.held }
  refine WP.mono (round_ok u up pre) fun v ⟨v1, v2, vkm, vt, vl, vk, vm⟩ => ⟨v1, ?_, ?_, vt, ?_,
    (hu.keep.trans vk).mono (by decide), vm.trans hu.mem⟩
  · rw [v2, show (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) i lr).2 =
      lr.1 ^^^ Spec.Cast5.f i lr.2 _ _ from rfl, fT_eq]
  · rw [vkm, hu.vkm]
  · rw [vl, hu.vleft]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-- The rounds loop, for any order of the rounds: round `idx i` is the
`i`-th, with its subkeys at `kpf i`, and the halves before it `fold i`. -/
theorem rounds_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool)
    (idx : Nat → Nat) (kpf : Nat → Addr) (fold : Nat → Spec.Cast5.Word × Spec.Cast5.Word)
    (hidx : ∀ i < n, 1 ≤ idx i ∧ idx i ≤ 16) (hkp : ∀ i < n, kpf i = kb + BitVec.ofNat 64 (4 * (idx i - 1)))
    (hfold : ∀ i < n, fold (i + 1) = Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem kb) (idx i) (fold i))
    (hnext : ∀ i, i + 1 < n → kpf (i + 1) = (if up then kpf i + 4#64 else kpf i - 4#64) ∧
      idx (i + 1) % 3 = nextT up (idx i % 3))
    (h0 : RInv s (fold 0) (kpf 0) (idx 0 % 3) n u) :
    WP isa (.loop (round up) (.nonzero .d left)) u fun v => ∃ kp t, RInv s (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧
      RInv s (fold i) (kpf i) (idx i % 3) (n - i) v) ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (hidx i hi) (by omega_arith)) fun w hw => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  obtain ev : isa.eval (.nonzero .d left) w = some (BitVec.ofNat 64 (n - i - 1) != 0) := by
    rw [eval_nonzero, hw.vleft]
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega_arith] at hw; exact hw⟩
    rw [ev, show n - i - 1 = 0 by omega_arith]; rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega_arith)
    refine .inr ⟨?_, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ?_⟩
    · rw [ev]
      congr 1
      have : BitVec.ofNat 64 (n - i - 1) ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega_arith
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega_arith]
      exact hw

/-! ## The block function -/

theorem _root_.VG.PPC64LE.Upd.keep {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr⟩

theorem rev32_eq (x : BitVec 32) : rev32 x = byteRev32 x := rfl

theorem BPre.ne {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {r : Reg}
    (hr : r ∈ roundRegs) : pr ≠ r := fun e => h.prOk.1 (e ▸ hr)

/-- The halves into `xL`, `xR`. -/
theorem load_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep [xL, tmp, xR] s u → u.mem = s.mem →
      lo (u.gpr xL) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).1 →
      lo (u.gpr xR) = (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p)).2 → WP isa (.block is) u Q) :
    WP isa (.block (([.loadRev .w xL pr zero, .addi tmp pr 4, .loadRev .w xR tmp zero] : List Instr) ++ is)) s Q := by
  obtain in0 : InRegions (s.rd ++ s.wr) p 4 := by
    obtain ⟨g, hg, hc⟩ := h.inP' (off := 0) (by decide)
    exact ⟨g, List.mem_append_right _ hg, by simpa using hc⟩
  obtain in4 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.inP' (off := 4) (by decide)
    exact ⟨g, List.mem_append_right _ hg, hc⟩
  obtain dec := Proof.Cast5.decodeBlock_blockAt s.mem p
  refine wp_lwbrx (ea := p) h.prOk.2 (by rw [h.ptr, h.zero]; simp) in0 fun u₁ h₁ => ?_
  refine wp_addi h.prOk.2 (by decide) fun u₂ h₂ => ?_
  obtain p₂ : u₂.gpr tmp = p + BitVec.ofNat 64 4 := by rw [h₂.gpr, h₁.other _ (h.ne (by decide)), h.ptr]
  refine wp_lwbrx (ea := p + BitVec.ofNat 64 4) (by decide) (by rw [p₂, h₂.other _ (by decide), h₁.other _ (by decide), h.zero]; simp) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact in4) fun u₃ h₃ => ?_
  refine k u₃ ((h₁.keep.trans (h₂.keep.trans h₃.keep)).mono (by decide)) (by rw [h₃.mem, h₂.mem, h₁.mem])
    ?_ ?_
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, dec, lo_ext, rev32_eq]
  · rw [h₃.gpr, h₂.mem, h₁.mem, dec, lo_ext, rev32_eq]

theorem startEnc_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startEnc pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * 0)) ((0 + 1) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_mr fun u₁ h₁ => wp_mr fun u₂ h₂ => wp_li (by decide) fun u₃ h₃ => wp_nil ?_
  exact
    { vL := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, uk.gpr (by decide), h.sched]; simp
      vtyp := by rw [h₃.gpr]
      vleft := by rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), uk.gpr (by decide), h.rounds]
      keep := (((uk.trans h₁.keep).trans h₂.keep).trans h₃.keep).mono (by decide)
      mem := by rw [h₃.mem, h₂.mem, h₁.mem, um] }

theorem startDec_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) :
    WP isa (.block (startDec pr)) s (RInv s (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem p))
      (kb + BitVec.ofNat 64 (4 * ((n - 0) - 1))) ((n - 0) % 3) n) := by
  refine load_ok h fun u uk um uL uR => ?_
  refine wp_lsl (by decide) fun u₁ h₁ => wp_add fun u₂ h₂ => wp_subi (by decide) (by decide) fun u₃ h₃ =>
    wp_mr fun u₄ h₄ => wp_lsr (by decide) fun u₅ h₅ => wp_subi (by decide) (by decide) fun u₆ h₆ => wp_nil ?_
  obtain r4 : u.gpr rnd = BitVec.ofNat 64 n := by rw [uk.gpr (by decide), h.rounds]
  obtain r3 : u.gpr sch = kb := by rw [uk.gpr (by decide), h.sched]
  obtain kmv : u₃.gpr km = kb + (BitVec.ofNat 64 n <<< 2) - BitVec.ofNat 64 4 := by
    rw [h₃.gpr, h₂.gpr, h₁.other _ (by decide), h₁.gpr, r3, r4]
  obtain tv : u₆.gpr typ = (BitVec.ofNat 64 n >>> 2) - BitVec.ofNat 64 3 := by
    rw [h₆.gpr, h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide),
      h₁.other _ (by decide), r4]
  exact
    { vL := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uL
      vR := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide)]; exact uR
      vkm := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.other _ (by decide), kmv]
        rcases h.nv with rfl | rfl
        · rw [show (BitVec.ofNat 64 12 <<< 2) = BitVec.ofNat 64 48 by decide, Offset.add_ofNat_sub _ (by decide)]
        · rw [show (BitVec.ofNat 64 16 <<< 2) = BitVec.ofNat 64 64 by decide, Offset.add_ofNat_sub _ (by decide)]
      vtyp := by rw [tv]; rcases h.nv with rfl | rfl <;> decide
      vleft := by
        rw [h₆.other _ (by decide), h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide),
          h₂.other _ (by decide), h₁.other _ (by decide), r4]
      keep := (((((((uk.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
        h₆.keep)).mono (by decide)
      mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, um] }

/-- What the block function does: the block at `p` is `out`, and nothing
else in memory changed. -/
structure BPost (s : State) (p : Addr) (out : Spec.Cast5.Block) (t : State) : Prop where
  blk : Spec.Cast5.blockAt t.mem p = out
  frame : Frame [⟨p, 8⟩] s.mem t.mem
  keep : Keep roundRegs s t

theorem finish_ok {s u : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : Addr} {t : Nat} (hu : RInv s lr kp t 0 u) :
    WP isa (.block (finish pr)) u (BPost s p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have g (q : Reg) (hq : q ∉ roundRegs) : u.gpr q = s.gpr q := hu.keep.gpr hq
  obtain hp : u.gpr pr = p := by rw [g _ h.prOk.1, h.ptr]
  obtain h0 : u.gpr .r0 = 0 := by rw [g _ (by decide), h.zero]
  obtain o0 : InRegions u.wr p 4 := by rw [hu.keep.2.2]; simpa using h.inP' (off := 0) (by decide)
  obtain o4 : InRegions u.wr (p + BitVec.ofNat 64 4) 4 := by rw [hu.keep.2.2]; exact h.inP' (by decide)
  refine wp_stwbrx (ea := p) h.prOk.2 (by rw [hp, h0]; simp) o0 fun u₁ h₁ => ?_
  refine wp_addi h.prOk.2 (by decide) fun u₂ h₂ => ?_
  obtain p₂ : u₂.gpr tmp = p + BitVec.ofNat 64 4 := by rw [h₂.gpr, h₁.gpr, hp]
  refine wp_stwbrx (ea := p + BitVec.ofNat 64 4) (by decide)
    (by rw [p₂, h₂.other _ (by decide), h₁.gpr, h0]; simp) (by rw [h₂.wr, h₁.wr]; exact o4) fun u₃ h₃ => ?_
  refine wp_nil ⟨?_, ?_, ?_⟩
  · rw [h₃.mem, h₂.mem, h₁.mem, h₂.other _ (by decide), h₁.gpr, rev32_eq, rev32_eq, hu.mem,
      Proof.Cast5.blockAt_write]
    exact congrArg _ (Prod.ext hu.vR hu.vL)
  · rw [h₃.mem, h₂.mem, h₁.mem, hu.mem]
    obtain f1 := (Frame.refl [(⟨p, 8⟩ : Region)] s.mem).writeW List.mem_cons_self
      (rev32 ((u.gpr xR).setWidth 32)) (Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))
    rw [BitVec.add_zero] at f1
    exact f1.writeW List.mem_cons_self _
      (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [h₃.gpr, h₂.other r fun e => hr (e ▸ by decide), h₁.gpr]; exact hu.keep.gpr hr
    · rw [h₃.rd, h₂.rd, h₁.rd]; exact hu.keep.2.1
    · rw [h₃.wr, h₂.wr, h₁.wr]; exact hu.keep.2.2

theorem crypt_ok {s : State} {pr : Reg} {p kb : Addr} {n : Nat} (h : BPre s pr p kb n) (up : Bool) :
    WP isa (crypt up pr) s (BPost s p (cipher up (Spec.Cast5.scheduleAt s.mem kb) n
      (Spec.Cast5.blockAt s.mem p))) := by
  have hn := h.nv
  cases up
  · unfold crypt
    simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (startDec_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h false (fun i => n - i) (fun i => kb + BitVec.ofNat 64 (4 * (n - i - 1)))
      (fun i => decFold _ n i _) (fun i hi => by omega_arith) (fun i hi => rfl)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - i - 1 = n - (i + 1) - 1 + 1 by omega_arith, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 64 (4 * i))
      (fun i => encFold _ i _) (fun i hi => by omega_arith)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu)
      fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
    · simp only [nextT, ite_true]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.PPC64LE
