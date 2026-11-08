module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.Run
public import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

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
    show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

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
  have z : ∀ m, 8 ≤ m → b.getLsbD m = false := fun m h => BitVec.getLsbD_of_ge b m h
  simp only [rep4, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hn, decide_true,
    Bool.true_and]
  by_cases h8 : n < 8
  · simp [h8, show n < 32 by omega, show n < 16 by omega, Nat.mod_eq_of_lt h8]
  by_cases h16 : n < 16
  · simp [h8, h16, show n < 32 by omega, show n - 8 < 8 by omega, z n (by omega),
      show n % 8 = n - 8 by omega, show n - 8 < 64 by omega]
  by_cases h24 : n < 24
  · simp [h8, h16, show n < 32 by omega, z n (by omega), z (n - 8) (by omega),
      show n % 8 = n - 16 by omega, show n - 16 < 64 by omega, show n - 16 < 8 by omega, show n - 8 < 64 by omega]
  by_cases h32 : n < 32
  · simp [h8, h16, h32, z n (by omega), z (n - 8) (by omega), z (n - 16) (by omega),
      show n % 8 = n - 24 by omega, show n - 16 - 8 = n - 24 by omega, show n - 24 < 8 by omega,
      show n - 16 < 64 by omega, show n - 8 < 64 by omega, show ¬ n - 16 < 8 by omega,
      show n - 24 < 64 by omega]
  · simp [h8, h16, h32, z n (by omega), z (n - 8) (by omega), z (n - 16) (by omega),
      z (n - 16 - 8) (by omega), show n - 16 < 64 by omega, show n - 8 < 64 by omega]

theorem vbyte_pack (b : Nat → Byte) {i : Nat} (hi : i < 16) :
    vbyte (pack fun k => (b k).setWidth 64) i = b (lk i) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, pack, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hr, decide_true, Bool.true_and]
  rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with h | h | h | h
  · rw [show lk i = 1 by simp [lk, h]]
    simp only [show ¬ 8 * (15 - i) + r < 64 by omega, ite_false]
    rw [rep4_bit _ (by omega), rep4_bit _ (by omega)]
    simp [show ¬ 8 * (15 - i) + r - 64 < 32 by omega, show 8 * (15 - i) + r - 64 < 64 by omega,
      show (8 * (15 - i) + r - 64 - 32) % 8 = r by omega, show 8 * (15 - i) + r - 64 - 32 < 32 by omega]
  · rw [show lk i = 0 by simp [lk, h]]
    simp only [show ¬ 8 * (15 - i) + r < 64 by omega, ite_false]
    rw [rep4_bit _ (by omega)]
    simp [show 8 * (15 - i) + r - 64 < 32 by omega, show (8 * (15 - i) + r - 64) % 8 = r by omega]
  · rw [show lk i = 3 by simp [lk, h]]
    simp only [show 8 * (15 - i) + r < 64 by omega, ite_true]
    rw [rep4_bit _ (by omega), rep4_bit _ (by omega)]
    simp [show ¬ 8 * (15 - i) + r < 32 by omega,
      show (8 * (15 - i) + r - 32) % 8 = r by omega, show 8 * (15 - i) + r - 32 < 32 by omega]
  · rw [show lk i = 2 by simp [lk, h]]
    simp only [show 8 * (15 - i) + r < 64 by omega, ite_true]
    rw [rep4_bit _ (by omega)]
    simp [show 8 * (15 - i) + r < 32 by omega, show (8 * (15 - i) + r) % 8 = r by omega]

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
  have r0 := r E (by simp)
  have r1 := r (E + 16#64) (by simp)
  have r2 := r (E + 32#64) (by simp)
  have r3 := r (E + 48#64) (by simp)
  have r4 := r (E + 64#64) (by simp)
  have r5 := r (E + 64#64 + 16#64) (by simp)
  have r6 := r (E + 64#64 + 32#64) (by simp)
  have r7 := r (E + 64#64 + 48#64) (by simp)
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
  have e : ∀ k < 16, 15 - (if k < 8 then k + 8 else k - 8) = k ^^^ 7 := by decide
  rw [vbyte_swapDwords _ hk, vbyte, Mem.readW, BitVec.setWidth_eq, ← e k hk]
  exact Mem.extractLsb'_read m a (n := 16) (by split <;> omega)

theorem vbyte_shift15 (x y : BitVec 128) {k : Nat} (hk : k < 16) :
    vbyte (BitVec.extractLsb' 128 128 ((x ++ y) <<< 120)) k = if k = 0 then vbyte x 15 else vbyte y (k - 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
    decide_true, Bool.true_and, show 128 + (8 * (15 - k) + r) < 128 + 128 by omega,
    show ¬ 128 + (8 * (15 - k) + r) < 120 by omega, decide_false, Bool.not_false]
  by_cases h0 : k = 0
  · rw [ite_eq_left h0, ite_eq_right (show ¬ 128 + (8 * (15 - k) + r) - 120 < 128 by omega),
      BitVec.getLsbD_extractLsb', decide_eq_true (show 8 * (15 - k) + r < 128 by omega), Bool.true_and,
      decide_eq_true hr, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · rw [ite_eq_right h0, ite_eq_left (show 128 + (8 * (15 - k) + r) - 120 < 128 by omega),
      BitVec.getLsbD_extractLsb', decide_eq_true (show 8 * (15 - k) + r < 128 by omega), Bool.true_and,
      decide_eq_true hr, Bool.true_and]
    exact congrArg y.getLsbD (by omega)

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
  have tb : ∀ b < 3, n.testBit b = (n % 8).testBit b := fun b hb => by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp [hb]
  rw [tb 0 (by decide), tb 1 (by decide), tb 2 (by decide)]
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize n % 8 = r at this ⊢
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem toNat_small {y : BitVec 64} (h : y.toNat < 256) : (y.setWidth 8).setWidth 64 = y := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega

/-- A lane's bytes: the low three bits of its index, or its group. -/
theorem vbyte_lanes (y : Nat → BitVec 64) (hy : ∀ k < 4, (y k).toNat < 256) {i : Nat} (hi : i < 16) :
    vbyte (pack y) i = BitVec.ofNat 8 (y (lk i)).toNat := by
  have hl : lk i < 4 := by unfold lk; rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with
    h | h | h | h <;> simp [h]
  have e : pack y = pack fun k => (if k < 4 then (y k).setWidth 8 else (y k).setWidth 8).setWidth 64 := by
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
  have e : vbyte (bitsWord b ++ u) j = (bitsWord b).extractLsb' (8 * (7 - j)) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
      show ¬ 8 * (15 - j) + i < 64 by omega, ite_false]
    congr 1; omega
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
  unfold lk; rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with h | h | h | h <;> simp [h]

theorem body_step {s₀ : State} {T : Addr} (hidx : ∀ k < 4, ix s₀ k < 256)
    (hrT : (⟨T, 4096⟩ : Region) ∈ s₀.rd ++ s₀.wr) {g : Nat} (hg : g < 32) {u : State} (I : VScan s₀ T g u) :
    WP isa (.block scanBody) u fun t =>
      VScan s₀ T (g + 1) t ∧ t.gpr tmp = BitVec.ofNat 64 (128 * (g + 1)) - BitVec.ofNat 64 4096 := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have ad : ∀ o, o + 16 ≤ 128 → InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (128 * g + o)) 16 := fun o ho => by
    rw [hrd]; exact ⟨_, hrT, Offset.contains_base T (by omega) (by omega)⟩
  have f1 : ∀ o, T + BitVec.ofNat 64 (128 * g) + BitVec.ofNat 64 o = T + BitVec.ofNat 64 (128 * g + o) :=
    fun o => Offset.add_add _ _ _
  have f2 : ∀ o, T + BitVec.ofNat 64 (128 * g) + 64#64 + BitVec.ofNat 64 o = T + BitVec.ofNat 64 (128 * g + (64 + o)) :=
    fun o => by rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Offset.add_add, Offset.add_add]

  -- The eight addresses, as the code makes them, and their bytes.
  have e0 : T + BitVec.ofNat 64 (128 * g) = T + BitVec.ofNat 64 (128 * g + 16 * 0) := rfl
  have e1 : T + BitVec.ofNat 64 (128 * g) + 16#64 = T + BitVec.ofNat 64 (128 * g + 16 * 1) := f1 16
  have e2 : T + BitVec.ofNat 64 (128 * g) + 32#64 = T + BitVec.ofNat 64 (128 * g + 16 * 2) := f1 32
  have e3 : T + BitVec.ofNat 64 (128 * g) + 48#64 = T + BitVec.ofNat 64 (128 * g + 16 * 3) := f1 48
  have e4 : T + BitVec.ofNat 64 (128 * g) + 64#64 = T + BitVec.ofNat 64 (128 * g + 16 * 4) := f1 64
  have e5 : T + BitVec.ofNat 64 (128 * g) + 64#64 + 16#64 = T + BitVec.ofNat 64 (128 * g + 16 * 5) := f2 16
  have e6 : T + BitVec.ofNat 64 (128 * g) + 64#64 + 32#64 = T + BitVec.ofNat 64 (128 * g + 16 * 6) := f2 32
  have e7 : T + BitVec.ofNat 64 (128 * g) + 64#64 + 48#64 = T + BitVec.ofNat 64 (128 * g + 16 * 7) := f2 48
  have rin : ∀ a ∈ [T + BitVec.ofNat 64 (128 * g), T + BitVec.ofNat 64 (128 * g) + 16#64, T + BitVec.ofNat 64 (128 * g) + 32#64, T + BitVec.ofNat 64 (128 * g) + 48#64, T + BitVec.ofNat 64 (128 * g) + 64#64, T + BitVec.ofNat 64 (128 * g) + 64#64 + 16#64, T + BitVec.ofNat 64 (128 * g) + 64#64 + 32#64,
      T + BitVec.ofNat 64 (128 * g) + 64#64 + 48#64], InRegions (u.rd ++ u.wr) a 16 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h | h | h | h <;> rw [h]
    · rw [e0]; exact ad _ (by omega)
    · rw [e1]; exact ad _ (by omega)
    · rw [e2]; exact ad _ (by omega)
    · rw [e3]; exact ad _ (by omega)
    · rw [e4]; exact ad _ (by omega)
    · rw [e5]; exact ad _ (by omega)
    · rw [e6]; exact ad _ (by omega)
    · rw [e7]; exact ad _ (by omega)
  refine WP.mono (WP.keep [tmp, ep] (body_run u I.ep I.zero I.o16 I.o32 I.o48 rfl rin) (by decide) rfl)
    fun t ⟨⟨ta, tlo, thi, tz, tg, tb0, tb1, tb2, tep, ttmp, tm⟩, tk⟩ => ?_
  have hB : ∀ b < 3, ∀ i < 16, vbyte (u.vpr (bitV b)) i =
      if (ix s₀ (lk i)).testBit b then 255#8 else 0#8 := I.bits
  refine ⟨⟨by omega, by rw [tz, I.z], fun i hi => by rw [tg, I.grp i hi], fun b hb i hi => ?_, fun p hp => ?_,
    fun i hi hlt => ?_, ?_, by rw [tk.gpr (by decide), I.o16], by rw [tk.gpr (by decide), I.o32],
    by rw [tk.gpr (by decide), I.o48], by rw [tk.gpr (by decide), I.zero], by rw [tk.gpr (by decide), I.tblR],
    (I.keep.trans tk).mono (by decide), tm.trans I.mem⟩, ?_⟩
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
    · rw [tb0]; exact I.bits 0 (by decide) i hi
    · rw [tb1]; exact I.bits 1 (by decide) i hi
    · rw [tb2]; exact I.bits 2 (by decide) i hi
  · have h0 := I.hot
    unfold hotByte at h0 ⊢
    by_cases hp16 : p < 16
    · rw [ite_eq_left hp16, tlo, vbyte_shift15 _ _ hp16, I.z, vbyte_zero]
      by_cases e : p = 0
      · rw [ite_eq_left e, ite_eq_right (by omega)]
      · rw [ite_eq_right e]
        have := h0 (p - 1) (by omega)
        rw [ite_eq_left (by omega)] at this
        rw [this]
        by_cases e' : p - 1 = g
        · rw [ite_eq_left e', ite_eq_left (by omega)]
        · rw [ite_eq_right e', ite_eq_right (by omega)]
    · rw [ite_eq_right hp16, thi, vbyte_shift15 _ _ (by omega)]
      by_cases e : p - 16 = 0
      · rw [ite_eq_left e]
        have := h0 15 (by omega)
        rw [ite_eq_left (by omega)] at this
        rw [this]
        by_cases e' : 15 = g
        · rw [ite_eq_left e', ite_eq_left (by omega)]
        · rw [ite_eq_right e', ite_eq_right (by omega)]
      · rw [ite_eq_right e]
        have := h0 (p - 1) (by omega)
        rw [ite_eq_right (by omega), show p - 1 - 16 = p - 16 - 1 by omega] at this
        rw [this]
        by_cases e' : p - 1 = g
        · rw [ite_eq_left e', ite_eq_left (by omega)]
        · rw [ite_eq_right e', ite_eq_right (by omega)]
  · -- The kept entries.
    have hl := lk_lt hi
    have hx := hidx _ hl
    have hm : vbyte (ofVBytes fun i => if (vbyte (u.vpr .v2) i).toNat % 32 < 16 then
        vbyte (u.vpr .v6) ((vbyte (u.vpr .v2) i).toNat % 32)
      else vbyte (u.vpr .v7) ((vbyte (u.vpr .v2) i).toNat % 32 - 16)) i =
        if decide (ix s₀ (lk i) / 8 = g) then 255#8 else 0#8 := by
      rw [vbyte_perm2 _ _ _ hi, show VReg.v2 = grpV from rfl, I.grp i hi, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show ix s₀ (lk i) / 8 < 2 ^ 8 by omega), Nat.mod_eq_of_lt (show ix s₀ (lk i) / 8 < 32 by omega)]
      have := I.hot (ix s₀ (lk i) / 8) (by omega)
      unfold hotByte at this
      rw [show VReg.v6 = hotLo from rfl, show VReg.v7 = hotHi from rfl, this]; simp
    rw [ta, vbyte_vsel _ _ _ hi hm]
    have hb : ∀ b < 3, vbyte (u.vpr (bitV b)) i = if (ix s₀ (lk i)).testBit b then 255#8 else 0#8 :=
      fun b hb => I.bits b hb i hi
    simp only [vbyte_vsel _ _ _ hi (hb 0 (by decide)), vbyte_vsel _ _ _ hi (hb 1 (by decide)),
      vbyte_vsel _ _ _ hi (hb 2 (by decide))]
    by_cases e : ix s₀ (lk i) / 8 = g
    · rw [ite_eq_left (by simpa using e), e7, e6, e5, e4, e3, e2, e1, e0,
        tree_sel (fun t => vbyte (swapDwords (u.mem.readW (T + BitVec.ofNat 64 (128 * g + 16 * t)) 128)) i),
        vbyte_load _ _ hi, Offset.add_add, I.mem]
      congr 3; omega
    · rw [ite_eq_right (by simpa using e)]
      exact I.acc i hi (by omega)
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
  have hlow : ∀ i < 16, vbyte (u.vpr lowV) i = BitVec.ofNat 8 (ix s (lk i) % 8) := fun i hi => by
    rw [ul, vbyte_lanes _ (fun k hk => by rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) hi,
      BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have bit : ∀ b < 3, ∀ (w : BitVec 64), ∀ i < 16, vbyte (permSelf (bitsWord b ++ w) (u.vpr lowV)) i =
      if (ix s (lk i)).testBit b then 255#8 else 0#8 := fun b hb w i hi => by
    have hm : ix s (lk i) % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [permSelf, vbyte_packed _ hi]
    simp only [hlow i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ix s (lk i) % 8 < 2 ^ 8 by omega),
      Nat.mod_eq_of_lt (show ix s (lk i) % 8 < 32 by omega), show ix s (lk i) % 8 < 16 by omega, ite_true,
      vbyte_bits w hb hm]
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp [hb]
  refine ⟨by decide, uz, fun i hi => ?_, fun b hb i hi => ?_, fun p hp => ?_, fun i _ h => absurd h (by omega),
    by rw [uep, BitVec.add_zero], unum, u19, u21, by rw [uk.gpr (by decide)]; exact h.zero,
    by rw [uk.gpr (by decide)], uk.mono (by decide), um⟩
  · rw [ug, vbyte_lanes _ (fun k hk => by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := hx k hk; simp only [ix] at this; omega) hi,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
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
  have hne : (BitVec.ofNat 64 (128 * (g + 1)) - BitVec.ofNat 64 4096 != 0#64) = !decide (g + 1 = 32) := by
    by_cases e : g + 1 = 32
    · rw [e]; rfl
    · have : BitVec.ofNat 64 (128 * (g + 1)) - BitVec.ofNat 64 4096 ≠ 0#64 := fun h' => by
        have := congrArg BitVec.toNat h'
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp [this, e]
  have ev : isa.eval (.nonzero .d tmp) v' = some (!decide (g + 1 = 32)) := by
    simp only [eval, State.read, BitVec.setWidth_eq]; rw [hz]; exact congrArg some hne
  by_cases e : g + 1 = 32
  · left
    exact ⟨by rw [ev, e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by rw [ev]; simp [e], n - 1, by omega, g + 1, by omega, by omega, J'⟩

/-! ## The words -/

/-- Bits `base` to `base + 31` of `v`, from its bytes. -/
theorem bits_of_bytes (v : BitVec 128) (w : BitVec 32) {base : Nat} (hb : base % 8 = 0) (hb' : base + 32 ≤ 128)
    (h : ∀ c < 4, vbyte v (15 - base / 8 - c) = w.extractLsb' (8 * c) 8) {n : Nat} (hn : n < 32) :
    v.getLsbD (base + n) = w.getLsbD n := by
  have := congrArg (BitVec.getLsbD · (n % 8)) (h (n / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show n % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rw [show base + n = 8 * (15 - (15 - base / 8 - n / 8)) + n % 8 by omega, this]
  exact congrArg w.getLsbD (by omega)

theorem lo_half (v : BitVec 128) (w : BitVec 32) {o : Nat} (ho : o = 0 ∨ o = 64)
    (h : ∀ c < 4, vbyte v (15 - o / 8 - c) = w.extractLsb' (8 * c) 8) :
    (v.extractLsb' o 64 <<< 32) >>> 32 = w.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro n hn
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  by_cases h32 : n < 32
  · simp only [show 32 + n < 64 by omega, decide_true, Bool.true_and, show ¬ 32 + n < 32 by omega,
      decide_false, Bool.not_false, show 32 + n - 32 = n by omega, show n < 64 by omega]
    exact bits_of_bytes v w (by omega) (by omega) h h32
  · rw [BitVec.getLsbD_of_ge w n (by omega)]
    simp [show ¬ 32 + n < 64 by omega]

theorem hi_half (v : BitVec 128) (w : BitVec 32) {o : Nat} (ho : o = 0 ∨ o = 64)
    (h : ∀ c < 4, vbyte v (15 - (o + 32) / 8 - c) = w.extractLsb' (8 * c) 8) :
    v.extractLsb' o 64 >>> 32 = w.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro n hn
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h32 : n < 32
  · simp only [show 32 + n < 64 by omega, decide_true, Bool.true_and, show n < 64 by omega]
    rw [show o + (32 + n) = (o + 32) + n by omega]
    exact bits_of_bytes v w (by omega) (by omega) h h32
  · rw [BitVec.getLsbD_of_ge w n (by omega)]
    simp [show ¬ 32 + n < 64 by omega]

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
  have byte : ∀ i < 16, vbyte (v.vpr accV) i =
      s.mem (s.gpr tbl + BitVec.ofNat 64 (16 * ix s (lk i) + (i ^^^ 7))) := fun i hi =>
    V.acc i hi (by have := h.idx _ (lk_lt hi); show (s.gpr (idxReg (lk i))).toNat / 8 < 32; omega)
  -- Byte `c` of word `k` is byte `i` of the vector, in lookup `lk i = k`'s lane.
  have wb : ∀ k < 4, ∀ i c, i < 16 → c < 4 → lk i = k → i ^^^ 7 = 4 * k + c →
      vbyte (v.vpr accV) i = (ent s.mem (s.gpr tbl) (ix s k) k).extractLsb' (8 * c) 8 := by
    intro k hk i c hi hc hl hx
    rw [byte i hi, ent, ← Mem.readW_byte _ _ hc, Offset.add_add, hl, hx, Nat.add_assoc]
  have l7 : ∀ c < 4, lk (7 - c) = 0 ∧ (7 - c) ^^^ 7 = 4 * 0 + c := by decide
  have l3 : ∀ c < 4, lk (3 - c) = 1 ∧ (3 - c) ^^^ 7 = 4 * 1 + c := by decide
  have l15 : ∀ c < 4, lk (15 - c) = 2 ∧ (15 - c) ^^^ 7 = 4 * 2 + c := by decide
  have l11 : ∀ c < 4, lk (11 - c) = 3 ∧ (11 - c) ^^^ 7 = 4 * 3 + c := by decide
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [show accReg 0 = .r18 from rfl, t18]
    exact lo_half _ _ (.inr rfl) fun c hc => wb 0 (by decide) _ c (by omega) hc (l7 c hc).1 (l7 c hc).2
  · rw [show accReg 1 = .r19 from rfl, t19]
    exact hi_half _ _ (.inr rfl) fun c hc => wb 1 (by decide) _ c (by omega) hc (l3 c hc).1 (l3 c hc).2
  · rw [show accReg 2 = .r20 from rfl, t20]
    exact lo_half _ _ (.inl rfl) fun c hc => wb 2 (by decide) _ c (by omega) hc (l15 c hc).1 (l15 c hc).2
  · rw [show accReg 3 = .r21 from rfl, t21]
    exact hi_half _ _ (.inl rfl) fun c hc => wb 3 (by decide) _ c (by omega) hc (l11 c hc).1 (l11 c hc).2

end VG.Proof.Cast5.PPC64LE
