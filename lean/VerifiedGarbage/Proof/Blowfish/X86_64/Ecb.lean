module

import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
public import VerifiedGarbage.Impl.Blowfish.X86_64

/-! ### `Blowfish.X86_64.Block`, which this module and modules that import it used -/

section

/-! ### `Blowfish.X86_64.F`, which this module and modules that import it used -/

section

/-! ### `Blowfish.X86_64.Scan`, which only this module used -/

section

/-!
# One row of a byte plane's scan

`scanAcc p x r`: the accumulator of a plane `p` (its 256 bytes) after the
rows `< r`, scanning for entry `x`: in byte lane `x % 16`, `p x` if `x`'s row
is one of them, and zero elsewhere (`row_acc`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64
open VG.Proof.Rc2.X86_64.Sse2 (mask_eq word_por)

theorem itT {c : Prop} [Decidable c] {α : Type} (a b : α) (h : c) : ite c a b = a :=
  ite_eq_left_of_eq_true a b (eq_true h)
theorem itF {c : Prop} [Decidable c] {α : Type} (a b : α) (h : ¬ c) : ite c a b = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

def scanAcc (p : Nat → Byte) (x r : Nat) : BitVec 128 :=
  ofWords fun w => if x / 16 < r ∧ x % 16 / 2 = w then ((p x).setWidth 16 <<< (8 * (x % 2))) else 0

theorem scanAcc_zero (p : Nat → Byte) (x : Nat) : scanAcc p x 0 = 0 :=
  ext_word fun i hi => by
    rw [scanAcc, word_ofWords _ hi]
    simp only [Nat.not_lt_zero, false_and, ite_false]
    exact (BitVec.extractLsb'_zero ..).symm

theorem word_or (a b : BitVec 128) (i : Nat) : word (a ||| b) i = word a i ||| word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_or, decide_eq_true hj, Bool.true_and]

theorem word_pand (a b : BitVec 128) (i : Nat) : word (a &&& b) i = word a i &&& word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_and, decide_eq_true hj, Bool.true_and]

theorem word_pxor (a b : BitVec 128) (i : Nat) : word (a ^^^ b) i = word a i ^^^ word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_xor, decide_eq_true hj, Bool.true_and]

/-- The even bytes of a value, as words. -/
theorem word_low (a : BitVec 128) {i : Nat} (hi : i < 8) :
    word (a &&& wordsOf 0xFF) i = (byte a (2 * i)).setWidth 16 := by
  rw [word_pand, wordsOf, word_ofWords _ hi]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_and, decide_eq_true hj, Bool.true_and, byte,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
  by_cases h : j < 8
  · simp [h, show 8 * (2 * i) + j = 16 * i + j by omega_using []]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [h]
  · simp only [h, decide_false, Bool.false_and]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [h]

/-- The word of a mask. -/
theorem word_mask (x : Byte) (k : Nat) (hk : k < 256) :
    ((BitVec.ofNat 16 k ^^^ x.setWidth 16) - 1).sshiftRight 15 =
      if x.toNat = k then BitVec.allOnes 16 else 0 := by
  have e : BitVec.ofNat 16 k = (BitVec.ofNat 8 k).setWidth 16 := by
    apply BitVec.eq_of_toNat_eq; simp; omega_using [hk]
  rw [e, BitVec.xor_comm, mask_eq]
  congr 1
  apply propext; constructor
  · intro h; rw [h, BitVec.toNat_ofNat]; omega_using [hk]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega_using [h]

/-- The byte mask of a row's word. -/
def byteMask (x k : Nat) : BitVec 16 :=
  (if x = k then 255#16 else 0#16) ||| (if x = k + 1 then 65280#16 else 0#16)

/-- One row: the selected byte stays in its original byte lane. -/
theorem row_acc (p : Nat → Byte) (x : Byte) {r : Nat} (data mE : BitVec 128)
    (hd : ∀ e < 16, byte data e = p (16 * r + e))
    (hE : ∀ w < 8, word mE w = byteMask x.toNat (16 * r + 2 * w)) :
    scanAcc p x.toNat r ||| (data &&& mE) = scanAcc p x.toNat (r + 1) := by
  have hx := x.isLt
  refine ext_word fun w hw => ?_
  rw [word_por, word_pand, hE w hw, scanAcc, scanAcc, word_ofWords _ hw, word_ofWords _ hw]
  have lo : word data w &&& 255#16 = (p (16 * r + 2 * w)).setWidth 16 := by
    have h := word_low data hw
    rw [word_pand, wordsOf, word_ofWords _ hw, hd _ (by omega_using [hw])] at h
    exact h
  have hi : word data w &&& 65280#16 = (p (16 * r + (2 * w + 1))).setWidth 16 <<< 8 := by
    rw [← hd _ (by omega_using [hw])]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, getLsbD_word, byte, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> exact congrArg _ (by omega_using [])
  by_cases h1 : x.toNat = 16 * r + 2 * w
  · rw [byteMask, ite_eq_left h1, ite_eq_right (show ¬ x.toNat = 16 * r + 2 * w + 1 by omega_using [h1]),
      BitVec.or_zero, lo,
      ite_eq_right (show ¬ (x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w) by omega_using [h1]),
      ite_eq_left (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega_using [hw, h1])]
    rw [show x.toNat % 2 = 0 by omega_using [h1], h1]
    simp
  · by_cases h2 : x.toNat = 16 * r + 2 * w + 1
    · rw [byteMask, ite_eq_right h1, ite_eq_left h2, BitVec.zero_or, hi,
        ite_eq_right (show ¬ (x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w) by omega_using [h2]),
        ite_eq_left (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega_using [hw, h2])]
      rw [show x.toNat % 2 = 1 by omega_using [h2], h2]
      simp [Nat.add_assoc]
    · rw [byteMask, ite_eq_right h1, ite_eq_right h2, BitVec.or_zero, BitVec.and_zero, BitVec.or_zero]
      by_cases h3 : x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w
      · rw [itT _ _ h3, itT _ _ (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega_using [h3])]
      · rw [itF _ _ h3, itF _ _ (show ¬ (x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w) by omega_using [h1, h2, h3])]

end VG.Proof.Blowfish.X86_64

end

end

/-! ### `Blowfish.X86_64.Row`, which only this module used -/

section

/-!
# A row of the scan, instruction by instruction

`masks_run`: the masks of the row; `plane_run`: one plane's row into its
accumulator.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64

theorem exec_xop (s : State) (op : XOp) : exec (.xop op) s = some (op.exec s) := rfl

theorem byte_readW128 (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    byte (m.readW a 128) e = m (a + BitVec.ofNat 64 e) := by
  rw [← Mem.extractLsb'_read m a (n := 16) he]
  simp only [byte, Mem.readW]
  rfl

theorem word_psubw (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .psubw a b) i = word a i - word b i := by
  simp only [reduceXBinOpEval]; exact word_ofWords _ hi

theorem word_paddw (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .paddw a b) i = word a i + word b i := by
  simp only [reduceXBinOpEval]; exact word_ofWords _ hi

theorem word_psraw15 (a : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XShiftOp.eval .psraw a (BitVec.ofNat 8 15)) i = (word a i).sshiftRight 15 := by
  simp only [XShiftOp.eval, word_ofWords _ hi]
  rfl

theorem runXops : ∀ (l : List XOp) (t : State),
    runBlock isa (l.map .xop) t = some (l.foldl (fun t op => op.exec t) t)
  | [], _ => runBlock_nil
  | op :: l, t => by rw [List.map_cons, runBlock_cons, exec_xop, runStep_some, runXops l]; rfl

/-- The row's even entries' numbers. -/
def rowK (r : Nat) : BitVec 128 := ofWords fun w => BitVec.ofNat 16 (16 * r + 2 * w)

/-- The index in every word. -/
def bcast (x : Byte) : BitVec 128 := ofWords fun _ => x.setWidth 16

theorem wordMasks_run (u : State) (x : Byte) {r : Nat} (hr : r < 16) (hk : u.xmm kReg = rowK r)
    (hx : u.xmm idxReg = bcast x) (h1 : u.xmm onesReg = wordsOf 1) :
    ∃ u', runBlock isa wordMasks u = some u' ∧
      (∀ w < 8, word (u'.xmm mEven) w = if x.toNat = 16 * r + 2 * w then BitVec.allOnes 16 else 0) ∧
      (∀ w < 8, word (u'.xmm mOdd) w = if x.toNat = 16 * r + 2 * w + 1 then BitVec.allOnes 16 else 0) ∧
      (∀ d, d ≠ mEven → d ≠ mOdd → u'.xmm d = u.xmm d) ∧ u' = { u with xmm := u'.xmm } := by
  let ops : List XOp := [.bin .movdqa mEven kReg, .bin .pxor mEven idxReg, .bin .psubw mEven onesReg,
    .shift .psraw mEven (BitVec.ofNat 8 15), .bin .movdqa mOdd kReg, .bin .paddw mOdd onesReg,
    .bin .pxor mOdd idxReg, .bin .psubw mOdd onesReg, .shift .psraw mOdd (BitVec.ofNat 8 15)]
  let u' := ops.foldl (fun t op => op.exec t) u
  refine ⟨u', runXops ops u, fun w hw => ?_, fun w hw => ?_, fun d h1 h2 => ?_, ?_⟩
  · simp (disch := decide) only [u', ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, hk, hx, h1]
    rw [word_psraw15 _ hw, word_psubw _ _ hw]
    simp only [reduceXBinOpEval]
    rw [word_pxor, rowK, bcast, wordsOf, word_ofWords _ hw, word_ofWords _ hw, word_ofWords _ hw]
    exact word_mask x _ (by omega_arith)
  · simp (disch := decide) only [u', ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, hk, hx, h1]
    rw [word_psraw15 _ hw, word_psubw _ _ hw]
    simp only [reduceXBinOpEval]
    rw [word_pxor, word_ofWords _ hw, rowK, bcast, wordsOf, word_ofWords _ hw, word_ofWords _ hw,
      word_ofWords _ hw, show BitVec.ofNat 16 (16 * r + 2 * w) + BitVec.ofNat 16 1 =
        BitVec.ofNat 16 (16 * r + 2 * w + 1) by rw [BitVec.ofNat_add_ofNat]]
    exact word_mask x _ (by omega_arith)
  · simp only [u', ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2]
  · simp only [u', ops, List.foldl, XOp.exec, State.setXmm]

theorem masks_run (u : State) (x : Byte) {r : Nat} (hr : r < 16) (hk : u.xmm kReg = rowK r)
    (hx : u.xmm idxReg = bcast x) (h1 : u.xmm onesReg = wordsOf 1)
    (hl : u.xmm lowReg = wordsOf 0xFF) :
    ∃ u', runBlock isa masks u = some u' ∧
      (∀ w < 8, word (u'.xmm mEven) w = byteMask x.toNat (16 * r + 2 * w)) ∧
      (∀ d, d ≠ mEven → d ≠ mOdd → u'.xmm d = u.xmm d) ∧ u' = { u with xmm := u'.xmm } := by
  obtain ⟨v, run, hE, hO, keep, eq⟩ := wordMasks_run u x hr hk hx h1
  let ops : List XOp := [.bin .pand mEven lowReg, .shift .psllw mOdd 8, .bin .por mEven mOdd]
  let u' := ops.foldl (fun t op => op.exec t) v
  refine ⟨u', ?_, fun w hw => ?_, fun d hE hO => ?_, ?_⟩
  · rw [masks, runBlock_append, run]
    exact runXops ops v
  · simp (disch := decide) only [u', ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne,
      reduceXBinOpEval]
    rw [word_or, word_pand, keep lowReg (by decide) (by decide), hl]
    rw [hE w hw]
    simp only [XShiftOp.eval, show (8 : BitVec 8).toNat = 8 by rfl, show ¬ 15 < 8 by decide, ite_false]
    rw [word_ofWords _ hw, hO w hw, wordsOf, word_ofWords _ hw]
    simp only [byteMask]
    by_cases he : x.toNat = 16 * r + 2 * w <;>
      by_cases ho : x.toNat = 16 * r + 2 * w + 1 <;> simp [he, ho]
  · simp only [u', ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ hE, xmm_setXmm_of_ne _ _ hO]
    exact keep d hE hO
  · simp only [u', ops, List.foldl, XOp.exec, State.setXmm]
    rw [eq]

theorem accReg_ne : ∀ b < 4, accReg b ≠ tmp ∧ accReg b ≠ tmp2 ∧ accReg b ≠ mEven ∧ accReg b ≠ mOdd ∧
    accReg b ≠ lowReg ∧ accReg b ≠ kReg ∧ accReg b ≠ idxReg ∧ accReg b ≠ onesReg ∧ accReg b ≠ sixteenReg ∧
    accReg b ≠ xL ∧ accReg b ≠ xR ∧ accReg b ≠ fReg := by decide

theorem exec_movdquLoad {s : State} {d : XReg} {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    exec (.movdquLoad d m) s = some (s.setXmm d (s.mem.readW (s.ea m) 128)) := by
  simp only [exec, State.load128, h, ite_true, Option.map_some]

/-- One plane's row, masked into its accumulator. -/
theorem plane_run (u : State) (sch : Reg) (j : Nat) {b : Nat} (hb : b < 4)
    (hR : InRegions (u.rd ++ u.wr) (u.ea (rowMem sch j b)) 16) :
    ∃ u', runBlock isa (plane sch j b) u = some u' ∧
      u'.xmm (accReg b) = u.xmm (accReg b) |||
        (u.mem.readW (u.ea (rowMem sch j b)) 128 &&& u.xmm mEven) ∧
      (∀ d, d ≠ tmp → d ≠ tmp2 → d ≠ accReg b → u'.xmm d = u.xmm d) ∧
      u' = { u with xmm := u'.xmm } := by
  obtain ⟨n1, n2, n3, n4, n5, -⟩ := accReg_ne b hb
  let T := u.mem.readW (u.ea (rowMem sch j b)) 128
  let u₁ := u.setXmm tmp T
  let ops : List XOp := [.bin .pand tmp mEven, .bin .por (accReg b) tmp]
  refine ⟨ops.foldl (fun t op => op.exec t) u₁, ?_, ?_, fun d h1 h2 h3 => ?_, ?_⟩
  · rw [plane, runBlock_cons, exec_movdquLoad hR, runStep_some]
    exact runXops ops u₁
  · simp (disch := first | decide | with_reducible assumption | exact Ne.symm ‹_›) only [ops, u₁, List.foldl, XOp.exec,
      xmm_setXmm_self, xmm_setXmm_of_ne, reduceXBinOpEval]
    rfl
  · simp (disch := decide) only [ops, u₁, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h3]
  · simp only [ops, u₁, List.foldl, XOp.exec, State.setXmm]

theorem cat_run {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁]; exact h₂

/-- Byte `e` of plane `b` of S-box `j` of the schedule at `S`. -/
def pl (S : Addr) (j b : Nat) (m : Mem) (e : Nat) : Byte := m (S + BitVec.ofNat 64 (planeOff j b + e))

/-- The S-boxes' planes are readable at `S`. -/
def Readable (s : State) (S : Addr) : Prop :=
  ∀ off, off + 16 ≤ 4096 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 off) 16

/-- What the rows need of the state the scan starts in. -/
structure ScanEnv (sch : Reg) (S : Addr) (x : Byte) (j : Nat) (u₀ : State) : Prop where
  j4 : j < 4
  hsch : u₀.gpr sch = S
  ne8 : sch ≠ Reg.r8
  ne9 : sch ≠ Reg.r9
  rd : Readable u₀ S
  idx : u₀.xmm idxReg = bcast x
  ones : u₀.xmm onesReg = wordsOf 1
  sixteen : u₀.xmm sixteenReg = wordsOf 16
  low : u₀.xmm lowReg = wordsOf 0xFF

/-- The vector registers the rows write. -/
def rowXRegs : List XReg := [kReg, tmp, tmp2, mEven, mOdd, .xmm8, .xmm9, .xmm10, .xmm11]

/-- After `r` rows. -/
structure RowInv (sch : Reg) (S : Addr) (x : Byte) (j : Nat) (u₀ : State) (r : Nat) (u : State) : Prop where
  le : r ≤ 16
  r8 : u.gpr .r8 = BitVec.ofNat 64 (16 * r)
  r9 : u.gpr .r9 = BitVec.ofNat 64 (16 - r)
  k : u.xmm kReg = rowK r
  acc : ∀ b < 4, u.xmm (accReg b) = scanAcc (pl S j b u₀.mem) x.toNat r
  xmm : ∀ d, d ∉ rowXRegs → u.xmm d = u₀.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → u.gpr g = u₀.gpr g
  eq : u = { u₀ with gpr := u.gpr, xmm := u.xmm, cf := u.cf, zf := u.zf, sf := u.sf, of := u.of }

theorem rowK_succ (r : Nat) : XBinOp.eval .paddw (rowK r) (wordsOf 16) = rowK (r + 1) :=
  ext_word fun w hw => by
    rw [word_paddw _ _ hw, rowK, rowK, wordsOf, word_ofWords _ hw, word_ofWords _ hw, word_ofWords _ hw,
      BitVec.ofNat_add_ofNat]
    congr 1; omega_arith

theorem ea_row (t : State) (sch : Reg) (S : Addr) (j b r : Nat) (h1 : t.gpr sch = S)
    (h2 : t.gpr .r8 = BitVec.ofNat 64 (16 * r)) :
    t.ea (rowMem sch j b) = S + BitVec.ofNat 64 (planeOff j b + 16 * r) := by
  simp only [State.ea, rowMem, h1, h2, BitVec.mul_one, Rc2.X86_64.offset_nat]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

/-- After the masks and the planes `< b` of a row. -/
structure PlaneInv (sch : Reg) (S : Addr) (x : Byte) (j : Nat) (u₀ : State) (r : Nat) (u t : State)
    (mE mO : BitVec 128) (b : Nat) : Prop where
  eq : t = { u with xmm := t.xmm }
  mE : t.xmm mEven = mE
  mO : t.xmm mOdd = mO
  done : ∀ b' < b, t.xmm (accReg b') = scanAcc (pl S j b' u₀.mem) x.toNat (r + 1)
  todo : ∀ b', b ≤ b' → b' < 4 → t.xmm (accReg b') = scanAcc (pl S j b' u₀.mem) x.toNat r
  keep : ∀ d, d ∉ rowXRegs → t.xmm d = u.xmm d
  k : t.xmm kReg = rowK r

theorem plane_step {sch : Reg} {S : Addr} {x : Byte} {j : Nat} {u₀ : State} (E : ScanEnv sch S x j u₀)
    {r : Nat} (hr : r < 16) {u : State} (I : RowInv sch S x j u₀ r u) {mE mO : BitVec 128}
    (hE : ∀ w < 8, word mE w = byteMask x.toNat (16 * r + 2 * w))
    {b : Nat} (hb : b < 4) {t : State} (P : PlaneInv sch S x j u₀ r u t mE mO b) :
    ∃ t', runBlock isa (plane sch j b) t = some t' ∧ PlaneInv sch S x j u₀ r u t' mE mO (b + 1) := by
  have hg : t.gpr = u.gpr := by rw [P.eq]
  have hm : t.mem = u₀.mem := by rw [P.eq, I.eq]
  have ea := ea_row t sch S j b r (by rw [hg, I.gpr _ E.ne8 E.ne9, E.hsch]) (by rw [hg, I.r8])
  have hoff : planeOff j b + 16 * r + 16 ≤ 4096 := by have := E.j4; unfold planeOff; omega_arith
  have hR : InRegions (t.rd ++ t.wr) (t.ea (rowMem sch j b)) 16 := by
    rw [ea, show t.rd = u₀.rd by rw [P.eq, I.eq], show t.wr = u₀.wr by rw [P.eq, I.eq]]
    exact E.rd _ hoff
  obtain ⟨t', run, hacc, keep, e'⟩ := plane_run t sch j hb hR
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := accReg_ne b hb
  refine ⟨t', run, ⟨by rw [e', P.eq], ?_, ?_, fun b' hb' => ?_, fun b' h1 h2 => ?_, fun d hd => ?_, ?_⟩⟩
  · rw [keep _ (by decide) (by decide) (Ne.symm n3), P.mE]
  · rw [keep _ (by decide) (by decide) (Ne.symm n4), P.mO]
  · by_cases h : b' = b
    · subst h
      rw [hacc, P.todo _ (Nat.le_refl _) hb, P.mE]
      refine row_acc _ x _ _ (fun e he => ?_) hE
      rw [ea, byte_readW128 _ _ he, hm, pl, Offset.add_add, Nat.add_assoc]
    · have ne : accReg b' ≠ accReg b := by
        have : ∀ a < 4, ∀ c < 4, a ≠ c → accReg a ≠ accReg c := by decide
        exact this _ (by omega_arith) _ hb h
      rw [keep _ (fun e => by obtain ⟨-, -⟩ := accReg_ne b' (by omega_arith); exact (accReg_ne b' (by omega_arith)).1 e)
        (fun e => (accReg_ne b' (by omega_arith)).2.1 e) ne]
      exact P.done _ (by omega_arith)
  · have ne : accReg b' ≠ accReg b := by
      have : ∀ a < 4, ∀ c < 4, a ≠ c → accReg a ≠ accReg c := by decide
      exact this _ h2 _ hb (by omega_arith)
    rw [keep _ (accReg_ne b' h2).1 (accReg_ne b' h2).2.1 ne]
    exact P.todo _ (by omega_arith) h2
  · have : d ≠ tmp ∧ d ≠ tmp2 ∧ d ≠ accReg b := by
      refine ⟨fun e => hd (by subst e; decide), fun e => hd (by subst e; decide), fun e => hd ?_⟩
      subst e
      have : ∀ c < 4, accReg c ∈ rowXRegs := by decide
      exact this b hb
    rw [keep _ this.1 this.2.1 this.2.2, P.keep _ hd]
  · rw [keep _ (by decide) (by decide) (Ne.symm n6), P.k]

/-- The end of a row. -/
theorem rowTail_run (t : State) :
    ∃ t', runBlock isa [bin .paddw kReg sixteenReg, .alu .add .r8 (.imm 16), .alu .sub .r9 (.imm 1)] t = some t' ∧
      t'.xmm = (t.setXmm kReg (XBinOp.eval .paddw (t.xmm kReg) (t.xmm sixteenReg))).xmm ∧
      t'.gpr .r8 = t.gpr .r8 + 16 ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧ t'.zf = some (t.gpr .r9 - 1 == 0) ∧
      (∀ g, g ≠ .r8 → g ≠ .r9 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, xmm := t'.xmm, cf := t'.cf, zf := t'.zf, sf := t'.sf, of := t'.of } := by
  let t₁ := (XOp.bin .paddw kReg sixteenReg).exec t
  let i16 : BitVec 64 := BitVec.signExtend 64 (16 : BitVec 32)
  let i1 : BitVec 64 := BitVec.signExtend 64 (1 : BitVec 32)
  let a8 := t₁.gpr .r8 + i16
  let t₂ := (arithFlags t₁ a8 (decide (2 ^ 64 ≤ (t₁.gpr .r8).toNat + i16.toNat))
    (addOverflow (t₁.gpr .r8) i16 a8)).setReg .r8 a8
  let a9 := t₂.gpr .r9 - i1
  let t₃ := (arithFlags t₂ a9 (decide ((t₂.gpr .r9).toNat < i1.toNat)) (subOverflow (t₂.gpr .r9) i1 a9)).setReg .r9 a9
  have g1 : t₁.gpr = t.gpr := rfl
  have h29 : t₂.gpr .r9 = t.gpr .r9 := by simp only [t₂, gpr_setReg_of_ne _ _ (show Reg.r9 ≠ Reg.r8 by decide), gpr_arithFlags, g1]
  refine ⟨t₃, ?_, rfl, ?_, ?_, ?_, fun g h8 h9 => ?_, ?_⟩
  · simp only [bin, runBlock_cons, runStep_some, exec, execAlu, readSrc, Option.bind_some, runBlock_nil]
    rfl
  · simp only [t₃, gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.r9 by decide), gpr_arithFlags, t₂, gpr_setReg_self, a8, g1]
    rfl
  · simp only [t₃, gpr_setReg_self, a9, h29]
    rfl
  · simp only [t₃, zf_setReg, zf_arithFlags, a9, h29]
    rfl
  · simp only [t₃, t₂, gpr_setReg_of_ne _ _ h9, gpr_setReg_of_ne _ _ h8, gpr_arithFlags, g1]
  · simp only [t₃, t₂, t₁, XOp.exec, State.setReg, State.setXmm, arithFlags, State.setFlags]

theorem row_run {sch : Reg} {S : Addr} {x : Byte} {j : Nat} {u₀ : State} (E : ScanEnv sch S x j u₀)
    {r : Nat} (hr : r < 16) {u : State} (I : RowInv sch S x j u₀ r u) :
    ∃ u', runBlock isa (row sch j) u = some u' ∧ RowInv sch S x j u₀ (r + 1) u' ∧
      u'.zf = some (BitVec.ofNat 64 (16 - (r + 1)) == 0) := by
  obtain ⟨u₁, r₁, hE, k₁, e₁⟩ := masks_run u x hr I.k (by rw [I.xmm _ (by decide), E.idx])
    (by rw [I.xmm _ (by decide), E.ones]) (by rw [I.xmm _ (by decide), E.low])
  have P0 : PlaneInv sch S x j u₀ r u u₁ (u₁.xmm mEven) (u₁.xmm mOdd) 0 := by
    refine ⟨e₁, rfl, rfl, fun _ h => absurd h (by omega_arith), fun b' _ h => ?_, fun d hd => ?_, ?_⟩
    · rw [k₁ _ (accReg_ne b' h).2.2.1 (accReg_ne b' h).2.2.2.1]; exact I.acc b' h
    · exact k₁ d (fun e => hd (e ▸ by decide)) (fun e => hd (e ▸ by decide))
    · rw [k₁ _ (by decide) (by decide)]; exact I.k
  obtain ⟨p1, rp1, P1⟩ := plane_step E hr I hE (b := 0) (by decide) P0
  obtain ⟨p2, rp2, P2⟩ := plane_step E hr I hE (b := 1) (by decide) P1
  obtain ⟨p3, rp3, P3⟩ := plane_step E hr I hE (b := 2) (by decide) P2
  obtain ⟨p4, rp4, P4⟩ := plane_step E hr I hE (b := 3) (by decide) P3
  have g4 : p4.gpr = u.gpr := by rw [P4.eq]
  have s4 : p4.xmm sixteenReg = wordsOf 16 := by rw [P4.keep _ (by decide), I.xmm _ (by decide), E.sixteen]
  obtain ⟨v, rv, xv, r8v, r9v, zv, gv, ev⟩ := rowTail_run p4
  refine ⟨v, ?_, ⟨by omega_arith, ?_, ?_, ?_, fun b hb => ?_, fun d hd => ?_, fun g h8 h9 => ?_, ?_⟩, ?_⟩
  · rw [row, List.append_assoc]
    refine cat_run r₁ (cat_run (a := (List.range 4).flatMap (plane sch j)) ?_ rv)
    show runBlock isa (plane sch j 0 ++ (plane sch j 1 ++ (plane sch j 2 ++ (plane sch j 3 ++ [])))) u₁ = _
    exact cat_run rp1 (cat_run rp2 (cat_run rp3 (cat_run rp4 runBlock_nil)))
  · rw [r8v, g4, I.r8]; apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [r9v, g4, I.r9]; apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [xv, xmm_setXmm_self, P4.k, s4, rowK_succ]
  · rw [xv, xmm_setXmm_of_ne _ _ (accReg_ne b hb).2.2.2.2.2.1, P4.done b hb]
  · rw [xv, xmm_setXmm_of_ne _ _ (show d ≠ kReg from fun e => hd (by rw [e]; decide)), P4.keep d hd, I.xmm d hd]
  · rw [gv g h8 h9, g4, I.gpr g h8 h9]
  · rw [ev, P4.eq, I.eq]
  · rw [zv, g4, I.r9]; congr 2; apply BitVec.eq_of_toNat_eq; simp; omega_arith


end VG.Proof.Blowfish.X86_64

end

end

/-! ### `Blowfish.X86_64.Reduce`, which only this module used -/

section

/-! # The OR of a plane accumulator's words -/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64

/-- What `reduce` leaves of `a`. -/
def reduceV (a : BitVec 128) : BitVec 128 :=
  let a1 := a ||| shufDwords a 0x4E
  let a2 := a1 ||| shufDwords a1 0xB1
  let a3 := a2 ||| XShiftOp.eval .psrld a2 16
  let a4 := a3 ||| XShiftOp.eval .psrld a3 8
  XShiftOp.eval .psrld (XShiftOp.eval .pslld a4 24) 24

theorem dword_or (a b : BitVec 128) (k : Nat) : dword (a ||| b) k = dword a k ||| dword b k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_or, decide_eq_true hi, Bool.true_and]

theorem psrld_dwords (a : BitVec 128) (c : BitVec 8) (hn : c.toNat < 32) :
    XShiftOp.eval .psrld a c =
      ofDwords (dword a 0 >>> c.toNat) (dword a 1 >>> c.toNat) (dword a 2 >>> c.toNat) (dword a 3 >>> c.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < c.toNat by omega_using [hn], ite_false]

theorem pslld_dwords (a : BitVec 128) (c : BitVec 8) (hn : c.toNat < 32) :
    XShiftOp.eval .pslld a c =
      ofDwords (dword a 0 <<< c.toNat) (dword a 1 <<< c.toNat) (dword a 2 <<< c.toNat) (dword a 3 <<< c.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < c.toNat by omega_using [hn], ite_false]

theorem reduceV_dword (a : BitVec 128) :
    dword (reduceV a) 0 =
      let D := (dword a 0 ||| dword a 2) ||| (dword a 1 ||| dword a 3)
      let E := D ||| D >>> 16
      ((E ||| E >>> 8) <<< 24) >>> 24 := by
  simp only [reduceV]
  rw [psrld_dwords _ _ (by decide), pslld_dwords _ _ (by decide), psrld_dwords _ _ (by decide)]
  simp only [dword_ofDwords_0, dword_or]
  rw [psrld_dwords _ _ (by decide)]
  simp only [dword_ofDwords_0, dword_or]
  rw [show shufDwords a 0x4E = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 1) from rfl,
    shufDwords_b1]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_or]
  rfl

theorem dword_words (v : BitVec 128) (k : Nat) : dword v k = word v (2 * k + 1) ++ word v (2 * k) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_append, getLsbD_word, decide_eq_true hi, Bool.true_and]
  split
  · simp only [decide_eq_true ‹i < 16›, Bool.true_and]; exact congrArg _ (by omega_using [])
  · simp only [decide_eq_true (show i - 16 < 16 by omega_using [hi]), Bool.true_and]; exact congrArg _ (by omega_arith)

/-- A byte at any of a dword's four positions, folded to the dword's low byte. -/
theorem fold_byte (b : BitVec 8) {c : Nat} (hc : c = 0 ∨ c = 1) {D : BitVec 32}
    (hD : D = 0#16 ++ b.setWidth 16 <<< (8 * c) ∨ D = b.setWidth 16 <<< (8 * c) ++ 0#16) :
    (((D ||| D >>> 16) ||| (D ||| D >>> 16) >>> 8) <<< 24) >>> 24 = b.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h8 : i < 8
  · rcases hc with rfl | rfl <;> rcases hD with rfl | rfl <;>
      simp only [Nat.mul_zero, Nat.mul_one, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
        BitVec.getLsbD_append, BitVec.getLsbD_setWidth] <;>
      rcases (by omega_using [h8] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ _ (by omega_using [h8]), BitVec.getLsbD_setWidth,
      BitVec.getLsbD_of_ge b i (by omega_using [h8]), Bool.and_false]

theorem reduce_scan (p : Nat → Byte) {x : Nat} (hx : x < 256) :
    dword (reduceV (scanAcc p x 16)) 0 = (p x).setWidth 32 := by
  have hw : ∀ w < 8, word (scanAcc p x 16) w = if x % 16 / 2 = w then ((p x).setWidth 16 <<< (8 * (x % 2))) else 0 := by
    intro w hw; rw [scanAcc, word_ofWords _ hw]
    simp only [show x / 16 < 16 by omega_arith, true_and]
  rw [reduceV_dword, dword_words, dword_words, dword_words, dword_words]
  simp only [Nat.mul_zero, Nat.zero_add, show 2 * 2 = 4 by rfl, show 2 * 3 = 6 by rfl,
    show 2 * 2 + 1 = 5 by rfl, show 2 * 3 + 1 = 7 by rfl, show 2 * 1 + 1 = 3 by rfl, show 2 * 1 = 2 by rfl,
    hw _ (by decide : 0 < 8), hw _ (by decide : 1 < 8), hw _ (by decide : 2 < 8), hw _ (by decide : 3 < 8),
    hw _ (by decide : 4 < 8), hw _ (by decide : 5 < 8), hw _ (by decide : 6 < 8), hw _ (by decide : 7 < 8)]
  have h8 : x % 16 / 2 < 8 := by omega_arith
  have h2 : x % 2 = 0 ∨ x % 2 = 1 := by omega_using []
  generalize x % 16 / 2 = w at h8
  rcases (by omega_arith : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      show (0#16 ++ 0#16 : BitVec 32) = 0#32 from rfl, BitVec.or_zero, BitVec.zero_or] <;>
    first
    | exact fold_byte (p x) h2 (Or.inl (by with_reducible rfl))
    | exact fold_byte (p x) h2 (Or.inr (by with_reducible rfl))

end VG.Proof.Blowfish.X86_64

end

end

/-! ### `Blowfish.X86_64.Lookup`, which only this module used -/

section

/-! ### `Blowfish.X86_64.Combine`, which only this module used -/

section

/-! # An S-box entry from its byte planes; the index in every lane -/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish

/-- The entry's bytes, shifted into place and ORed. -/
theorem combine_entry (m : Mem) (S : Addr) {j : Nat} (hj : j < 4) (x : Byte) :
    (pl S j 0 m x.toNat).setWidth 32 ||| (pl S j 1 m x.toNat).setWidth 32 <<< 8 |||
        (pl S j 2 m x.toNat).setWidth 32 <<< 16 ||| (pl S j 3 m x.toNat).setWidth 32 <<< 24 =
      sEntry (scheduleAt m S) j x := by
  refine word_ext fun b hb => ?_
  rw [byte_of_le4 _ _ _ _ hb, sEntry_byte _ _ hj hb]
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `punpcklwd` of a value with itself, then `pshufd 0`: its low word in every word. -/
theorem bcast_low (v : BitVec 128) (b : Byte) (h : dword v 0 = b.setWidth 32) :
    shufDwords (XBinOp.eval .punpcklwd v v) 0 = bcast b := by
  refine ext_word fun i hi => ?_
  rw [word_eq_dword _ hi, show shufDwords (XBinOp.eval .punpcklwd v v) 0 =
      ofDwords (dword (XBinOp.eval .punpcklwd v v) 0) (dword (XBinOp.eval .punpcklwd v v) 0)
        (dword (XBinOp.eval .punpcklwd v v) 0) (dword (XBinOp.eval .punpcklwd v v) 0) from rfl]
  obtain d0 : dword (XBinOp.eval .punpcklwd v v) 0 = word v 0 ++ word v 0 := by
    rw [dword_words]
    simp only [XBinOp.eval, word_ofWords _ (show 2 * 0 + 1 < 8 by decide), word_ofWords _ (show 2 * 0 < 8 by decide)]
    rfl
  obtain w0 : word v 0 = b.setWidth 16 := by
    rw [word_eq_dword _ (by decide), show 0 / 2 = 0 from rfl, h]
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]; omega_using [hj]
  obtain hd : ∀ k < 4, dword (ofDwords (word v 0 ++ word v 0) (word v 0 ++ word v 0) (word v 0 ++ word v 0)
      (word v 0 ++ word v 0)) k = word v 0 ++ word v 0 := by
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp
  rw [d0, hd _ (by omega_using [hi]), bcast, word_ofWords _ hi, w0]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split <;> rename_i h <;> rcases (by omega_using [] : i % 2 = 0 ∨ i % 2 = 1) with e | e <;> simp [e] at h ⊢ <;>
    omega

end VG.Proof.Blowfish.X86_64

end

end


/-!
# An S-box lookup

`lookup_run`: `lookup sch j` leaves S-box `j` at byte `3 - j` of xL (S₁ at
its most significant byte) in the low doubleword of `accReg 0`, writing only
`r8`, `r9`, `r11`, the flags and the scan's vector registers.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish

theorem exec_movImm64 (s : State) (d : Reg) (v : BitVec 64) : exec (.movImm64 d v) s = some (s.setReg d v) := rfl

theorem loadConst_run (t : State) {dst : XReg} (hd : dst ≠ tmp) (v : BitVec 128) :
    ∃ t', runBlock isa (loadConst dst v) t = some t' ∧ t'.xmm dst = v ∧
      (∀ d, d ≠ dst → d ≠ tmp → t'.xmm d = t.xmm d) ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, xmm := t'.xmm } := by
  let t₁ := t.setReg .r11 (v.extractLsb' 0 64)
  let t₂ := (XOp.movq dst .r11).exec t₁
  let t₃ := t₂.setReg .r11 (v.extractLsb' 64 64)
  let t₄ := (XOp.movq tmp .r11).exec t₃
  let t₅ := (XOp.bin .punpcklqdq dst tmp).exec t₄
  refine ⟨t₅, ?_, ?_, fun d h1 h2 => ?_, fun g hg => ?_, ?_⟩
  · simp only [loadConst, bin, runBlock_cons, exec_movImm64, exec_xop, runStep_some, runBlock_nil]
    rfl
  · simp (disch := decide) only [t₅, t₄, t₃, t₂, t₁, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hd,
      xmm_setReg, gpr_setReg_self]
    exact movq_const v
  · simp only [t₅, t₄, t₃, t₂, t₁, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, xmm_setReg]
  · simp only [t₅, t₄, t₃, t₂, t₁, XOp.exec, gpr_setXmm, gpr_setReg_of_ne _ _ hg]
  · simp only [t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setXmm, State.setReg]

/-- Byte `k` of a word, by shifts. -/
theorem shifts_byte (L : BitVec 32) {k : Nat} (hk : k < 4) :
    (L <<< (24 - 8 * k)) >>> 24 = (L.extractLsb' (8 * k) 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  by_cases h : i < 8
  · simp [h, show 24 + i < 32 by omega_using [h], show ¬ 24 + i < 24 - 8 * k by omega_using []]
    rw [decide_eq_true hi, Bool.true_and]
    exact congrArg _ (by omega_using [hk])
  · simp [h, show ¬ 24 + i < 32 by omega_using [h]]

theorem exec_mov32_imm (s : State) (d : Reg) (v : BitVec 32) :
    exec (.mov32 d (.imm v)) s = some (s.setReg32 d v) := rfl

theorem pslld_dword0 (v : BitVec 128) (c : BitVec 8) (hc : c.toNat < 32) :
    dword (XShiftOp.eval .pslld v c) 0 = dword v 0 <<< c.toNat := by
  rw [pslld_dwords _ _ hc, dword_ofDwords_0]

theorem psrld_dword0 (v : BitVec 128) (c : BitVec 8) (hc : c.toNat < 32) :
    dword (XShiftOp.eval .psrld v c) 0 = dword v 0 >>> c.toNat := by
  rw [psrld_dwords _ _ hc, dword_ofDwords_0]

theorem state_eta (t : State) :
    t = { t with gpr := t.gpr, xmm := t.xmm, cf := t.cf, zf := t.zf, sf := t.sf, of := t.of } := rfl

theorem reduce_run (t : State) {b : Nat} (hb : b < 4) :
    ∃ t', runBlock isa (reduce b) t = some t' ∧ t'.xmm (accReg b) = reduceV (t.xmm (accReg b)) ∧
      (∀ d, d ≠ tmp → d ≠ accReg b → t'.xmm d = t.xmm d) ∧ t' = { t with xmm := t'.xmm } := by
  obtain ne := (accReg_ne b hb).1
  let ops : List XOp := [.pshufd tmp (accReg b) 0x4E, .bin .por (accReg b) tmp, .pshufd tmp (accReg b) 0xB1,
    .bin .por (accReg b) tmp, .bin .movdqa tmp (accReg b), .shift .psrld tmp (BitVec.ofNat 8 16),
    .bin .por (accReg b) tmp, .bin .movdqa tmp (accReg b), .shift .psrld tmp (BitVec.ofNat 8 8),
    .bin .por (accReg b) tmp, .shift .pslld (accReg b) (BitVec.ofNat 8 24), .shift .psrld (accReg b) (BitVec.ofNat 8 24)]
  refine ⟨ops.foldl (fun t op => op.exec t) t, by rw [show reduce b = ops.map .xop from rfl]; exact runXops ops t,
    ?_, fun d h1 h2 => ?_, ?_⟩
  · simp only [ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ ne, xmm_setXmm_of_ne _ _ ne.symm,
      eval_movdqa]
    rfl
  · simp only [ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2]
  · simp only [ops, List.foldl, XOp.exec, State.setXmm]

/-- What a lookup needs. -/
structure LookEnv (sch : Reg) (S : Addr) (s : State) : Prop where
  hsch : s.gpr sch = S
  ne8 : sch ≠ Reg.r8
  ne9 : sch ≠ Reg.r9
  ne11 : sch ≠ Reg.r11
  rd : Readable s S
  ones : s.xmm onesReg = wordsOf 1
  sixteen : s.xmm sixteenReg = wordsOf 16
  low : s.xmm lowReg = wordsOf 0xFF

/-- The vector registers a lookup writes. -/
def lookXRegs : List XReg := [idxReg, kReg, tmp, tmp2, mEven, mOdd, .xmm8, .xmm9, .xmm10, .xmm11]

/-- Only the lookup's registers and the flags change. -/
structure LookOnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ lookXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → s'.gpr g = s.gpr g
  eq : s' = { s with gpr := s'.gpr, xmm := s'.xmm, cf := s'.cf, zf := s'.zf, sf := s'.sf, of := s'.of }

theorem index_eq (k : Nat) : index k = ([.bin .movdqa idxReg xL, .shift .pslld idxReg (BitVec.ofNat 8 (24 - 8 * k)),
    .shift .psrld idxReg (BitVec.ofNat 8 24), .bin .punpcklwd idxReg idxReg, .pshufd idxReg idxReg 0] : List XOp).map .xop := rfl

theorem lookup_run {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) {j : Nat} (hj : j < 4) :
    WP isa (lookup sch j) s (fun s' => dword (s'.xmm (accReg 0)) 0 =
      sEntry (scheduleAt s.mem S) j ((dword (s.xmm xL) 0).extractLsb' (8 * (3 - j)) 8) ∧ LookOnly s s') := by
  let x : Byte := (dword (s.xmm xL) 0).extractLsb' (8 * (3 - j)) 8
  rw [lookup]
  apply WP.seq
  -- the index, the row's numbers, the accumulators and the counters
  let iops : List XOp := [.bin .movdqa idxReg xL, .shift .pslld idxReg (BitVec.ofNat 8 (24 - 8 * (3 - j))),
    .shift .psrld idxReg (BitVec.ofNat 8 24), .bin .punpcklwd idxReg idxReg, .pshufd idxReg idxReg 0]
  let t₁ := iops.foldl (fun t op => op.exec t) s
  obtain hidx : t₁.xmm idxReg = bcast x := by
    simp (disch := decide) only [t₁, iops, List.foldl, XOp.exec, xmm_setXmm_self, eval_movdqa]
    refine bcast_low _ _ ?_
    rw [psrld_dword0 _ _ (by decide), pslld_dword0 _ _ (by simp; omega_using [])]
    simp only [BitVec.toNat_ofNat, show (24 - 8 * (3 - j)) % 2 ^ 8 = 24 - 8 * (3 - j) by omega_using [],
      show 24 % 2 ^ 8 = 24 from rfl]
    exact shifts_byte _ (by omega_using [])
  obtain ⟨t₂, r₂, k₂, x₂, g₂, e₂⟩ := loadConst_run t₁ (dst := kReg) (by decide) evenStart
  let pops : List XOp := (List.range 4).map fun b => .bin .pxor (accReg b) (accReg b)
  let t₃ := pops.foldl (fun t op => op.exec t) t₂
  let t₄ := (t₃.setReg32 .r8 0).setReg32 .r9 16
  obtain run₄ : runBlock isa (index (3 - j) ++ loadConst kReg evenStart ++
      (List.range 4).map (fun b => bin .pxor (accReg b) (accReg b)) ++
      [.mov32 .r8 (.imm 0), .mov32 .r9 (.imm 16)]) s = some t₄ := by
    refine cat_run (cat_run (cat_run (by rw [index_eq]; exact runXops iops s) r₂) (runXops pops t₂)) ?_
    rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil]
  -- what the init leaves
  obtain g₁ : t₁.gpr = s.gpr := by simp only [t₁, iops, List.foldl, XOp.exec, gpr_setXmm]
  obtain x₁ : ∀ d, d ≠ idxReg → t₁.xmm d = s.xmm d := fun d h => by
    simp only [t₁, iops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h]
  have pops_eq : pops = [.bin .pxor .xmm8 .xmm8, .bin .pxor .xmm9 .xmm9, .bin .pxor .xmm10 .xmm10,
      .bin .pxor .xmm11 .xmm11] := rfl
  obtain x₄ : ∀ d, d ∉ lookXRegs → t₄.xmm d = s.xmm d := fun d hd => by
    obtain h1 : d ≠ idxReg := fun e => hd (by rw [e]; decide)
    obtain h2 : d ≠ kReg := fun e => hd (by rw [e]; decide)
    obtain h3 : d ≠ tmp := fun e => hd (by rw [e]; decide)
    obtain h8 : d ≠ .xmm8 := fun e => hd (by rw [e]; decide)
    obtain h9 : d ≠ .xmm9 := fun e => hd (by rw [e]; decide)
    obtain h10 : d ≠ .xmm10 := fun e => hd (by rw [e]; decide)
    obtain h11 : d ≠ .xmm11 := fun e => hd (by rw [e]; decide)
    simp only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, xmm_setReg, xmm_setXmm_of_ne _ _ h8,
      xmm_setXmm_of_ne _ _ h9, xmm_setXmm_of_ne _ _ h10, xmm_setXmm_of_ne _ _ h11]
    rw [x₂ _ h2 h3, x₁ _ h1]
  obtain a₄ : ∀ b < 4, t₄.xmm (accReg b) = 0 := fun b hb => by
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, xmm_setReg,
        xmm_setXmm_of_ne, xmm_setXmm_self, accReg, List.getD_cons_zero, List.getD_cons_succ, reduceXBinOpEval,
        BitVec.xor_self] <;> rfl
  obtain xs₄ : ∀ d, d ≠ .xmm8 → d ≠ .xmm9 → d ≠ .xmm10 → d ≠ .xmm11 → t₄.xmm d = t₂.xmm d :=
    fun d h8 h9 h10 h11 => by
      simp only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, xmm_setReg, xmm_setXmm_of_ne _ _ h8,
        xmm_setXmm_of_ne _ _ h9, xmm_setXmm_of_ne _ _ h10, xmm_setXmm_of_ne _ _ h11]
  obtain i₄ : t₄.xmm idxReg = bcast x := by
    rw [xs₄ _ (by decide) (by decide) (by decide) (by decide), x₂ _ (by decide) (by decide), hidx]
  obtain k₄ : t₄.xmm kReg = rowK 0 := by
    rw [xs₄ _ (by decide) (by decide) (by decide) (by decide), k₂]
    refine ext_word fun w hw => ?_
    rw [evenStart, rowK, word_ofWords _ hw, word_ofWords _ hw, Nat.mul_zero, Nat.zero_add]
  obtain g₄ : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → t₄.gpr g = s.gpr g := fun g h8 h9 h11 => by
    simp only [t₄, State.setReg32, gpr_setReg_of_ne _ _ h9, gpr_setReg_of_ne _ _ h8, t₃, pops_eq, List.foldl,
      XOp.exec, gpr_setXmm]
    rw [g₂ _ h11, g₁]
  obtain r8₄ : t₄.gpr .r8 = BitVec.ofNat 64 (16 * 0) := by
    simp only [t₄, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.r9 by decide), gpr_setReg_self]; rfl
  obtain r9₄ : t₄.gpr .r9 = BitVec.ofNat 64 (16 - 0) := by
    simp only [t₄, State.setReg32, gpr_setReg_self]; rfl
  obtain e₄ : t₄ = { s with gpr := t₄.gpr, xmm := t₄.xmm } := by
    simp only [t₄, t₃, pops_eq, List.foldl, XOp.exec, State.setReg32, State.setReg, State.setXmm]
    rw [e₂]; simp only [t₁, iops, List.foldl, XOp.exec, State.setXmm]
  obtain hrd₄ : t₄.rd = s.rd := by rw [e₄]
  obtain hwr₄ : t₄.wr = s.wr := by rw [e₄]
  obtain hm₄ : t₄.mem = s.mem := by rw [e₄]
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  obtain SE : ScanEnv sch S x j t₄ := by
    refine ⟨hj, by rw [g₄ _ E.ne8 E.ne9 E.ne11, E.hsch], E.ne8, E.ne9, fun off h => ?_, i₄,
      by rw [x₄ _ (by decide), E.ones], by rw [x₄ _ (by decide), E.sixteen], by rw [x₄ _ (by decide), E.low]⟩
    rw [hrd₄, hwr₄]; exact E.rd off h
  obtain I0 : RowInv sch S x j t₄ 0 t₄ :=
    ⟨by omega_using [], r8₄, r9₄, k₄, fun b hb => by rw [a₄ b hb, scanAcc_zero], fun _ _ => rfl, fun _ _ _ => rfl,
      state_eta t₄⟩
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := RowInv sch S x j t₄ 16)
    (fun m u => ∃ r, r < 16 ∧ m = 16 - r ∧ RowInv sch S x j t₄ r u) ?_ 16 t₄ ⟨0, by omega_using [], rfl, I0⟩)
    fun v Iv => ?_
  · intro m u ⟨r, hr, hm, I⟩
    obtain ⟨u', ru, I', zu⟩ := row_run SE hr I
    refine WP.of_runBlock ⟨u', ru, ?_⟩
    obtain ev : isa.eval .ne u' = some (!(BitVec.ofNat 64 (16 - (r + 1)) == 0)) := by
      show u'.zf.map (!·) = _; rw [zu]; rfl
    by_cases h : r + 1 = 16
    · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
    · right
      obtain nz : BitVec.ofNat 64 (16 - (r + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_using [hr, h, this]
      exact ⟨by rw [ev, show (BitVec.ofNat 64 (16 - (r + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
        16 - (r + 1), by omega_using [hr, hm], r + 1,
        by omega_using [hr, h], rfl, I'⟩
  -- the entry from the planes' accumulators
  obtain ⟨w0, rw0, a0, k0, e0⟩ := reduce_run v (b := 0) (by decide)
  obtain ⟨w1, rw1, a1, k1, e1⟩ := reduce_run w0 (b := 1) (by decide)
  obtain ⟨w2, rw2, a2, k2, e2⟩ := reduce_run w1 (b := 2) (by decide)
  obtain ⟨w3, rw3, a3, k3, e3⟩ := reduce_run w2 (b := 3) (by decide)
  let cops : List XOp := [.shift .pslld (accReg 1) (BitVec.ofNat 8 8), .shift .pslld (accReg 2) (BitVec.ofNat 8 16),
    .shift .pslld (accReg 3) (BitVec.ofNat 8 24), .bin .por (accReg 0) (accReg 1), .bin .por (accReg 0) (accReg 2),
    .bin .por (accReg 0) (accReg 3)]
  let w := cops.foldl (fun t op => op.exec t) w3
  obtain red : ∀ b < 4, dword (reduceV (v.xmm (accReg b))) 0 = (pl S j b t₄.mem x.toNat).setWidth 32 :=
    fun b hb => by rw [Iv.acc b hb]; exact reduce_scan _ x.isLt
  refine WP.of_runBlock ⟨w, ?_, ?_, ?_⟩
  · refine cat_run (a := (List.range 4).flatMap reduce) ?_ (runXops cops w3)
    show runBlock isa (reduce 0 ++ (reduce 1 ++ (reduce 2 ++ (reduce 3 ++ [])))) v = _
    exact cat_run rw0 (cat_run rw1 (cat_run rw2 (cat_run rw3 runBlock_nil)))
  · have r3 : ∀ b < 4, w3.xmm (accReg b) = reduceV (v.xmm (accReg b)) := by
      intro b hb
      rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
      · rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), a0]
      · rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide), a1, k0 _ (by decide) (by decide)]
      · rw [k3 _ (by decide) (by decide), a2, k1 _ (by decide) (by decide), k0 _ (by decide) (by decide)]
      · rw [a3, k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), k0 _ (by decide) (by decide)]
    simp (disch := decide) only [w, cops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, reduceXBinOpEval]
    rw [dword_or, dword_or, dword_or, pslld_dword0 _ _ (by decide), pslld_dword0 _ _ (by decide),
      pslld_dword0 _ _ (by decide), r3 0 (by decide), r3 1 (by decide), r3 2 (by decide), r3 3 (by decide),
      red 0 (by decide), red 1 (by decide), red 2 (by decide), red 3 (by decide), hm₄]
    exact combine_entry _ _ hj x
  · have gw : w.gpr = v.gpr := by
      simp only [w, cops, List.foldl, XOp.exec, gpr_setXmm]; rw [e3, e2, e1, e0]
    refine ⟨fun d hd => ?_, fun g h8 h9 h11 => ?_, ?_⟩
    · have n0 : d ≠ accReg 0 := fun e => hd (by rw [e]; decide)
      obtain n1 : d ≠ accReg 1 := fun e => hd (by rw [e]; decide)
      obtain n2 : d ≠ accReg 2 := fun e => hd (by rw [e]; decide)
      obtain n3 : d ≠ accReg 3 := fun e => hd (by rw [e]; decide)
      obtain nt : d ≠ tmp := fun e => hd (by rw [e]; decide)
      obtain sub : ∀ e ∈ rowXRegs, e ∈ lookXRegs := by decide
      obtain hr : d ∉ rowXRegs := fun h => hd (sub d h)
      simp only [w, cops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ n0, xmm_setXmm_of_ne _ _ n1,
        xmm_setXmm_of_ne _ _ n2, xmm_setXmm_of_ne _ _ n3]
      rw [k3 _ nt n3, k2 _ nt n2, k1 _ nt n1, k0 _ nt n0, Iv.xmm _ hr, x₄ _ hd]
    · rw [gw, Iv.gpr g h8 h9, g₄ g h8 h9 h11]
    · have : w = { v with xmm := w.xmm } := by
        simp only [w, cops, List.foldl, XOp.exec, State.setXmm]; rw [e3, e2, e1, e0]
      rw [this, Iv.eq, e₄]

end VG.Proof.Blowfish.X86_64

end

end


/-! # F: four lookups, combined in the low doubleword of `fReg` -/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The vector registers F writes. -/
def fXRegs : List XReg := fReg :: lookXRegs

/-- Only F's registers and the flags change. -/
structure FOnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ fXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → s'.gpr g = s.gpr g
  eq : s' = { s with gpr := s'.gpr, xmm := s'.xmm, cf := s'.cf, zf := s'.zf, sf := s'.sf, of := s'.of }

/-- `a` is `c` with other registers and flags. -/
def Upd (c a : State) : Prop :=
  a = { c with gpr := a.gpr, xmm := a.xmm, cf := a.cf, zf := a.zf, sf := a.sf, of := a.of }

theorem Upd.trans {a b c : State} (h1 : Upd b a) (h2 : Upd c b) : Upd c a := by
  unfold Upd at *; rw [h1]; rw [h2]

theorem Upd.setXmm {a c : State} (h : Upd c a) (d : XReg) (v : BitVec 128) : Upd c (a.setXmm d v) := by
  unfold Upd at *; rw [h]; rfl

theorem FOnly.refl (s : State) : FOnly s s := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, state_eta s⟩

theorem FOnly.env {sch : Reg} {S : Addr} {s t : State} (E : LookEnv sch S s) (h : FOnly s t) : LookEnv sch S t := by
  obtain hrd : t.rd = s.rd := by rw [h.eq]
  obtain hwr : t.wr = s.wr := by rw [h.eq]
  refine ⟨by rw [h.gpr _ E.ne8 E.ne9 E.ne11, E.hsch], E.ne8, E.ne9, E.ne11, fun off ho => ?_,
    by rw [h.xmm _ (by decide), E.ones], by rw [h.xmm _ (by decide), E.sixteen], by rw [h.xmm _ (by decide), E.low]⟩
  rw [hrd, hwr]; exact E.rd off ho

theorem combineX_0 : combineX 0 = .bin .movdqa fReg (accReg 0) := rfl
theorem combineX_1 : combineX 1 = .bin .paddd fReg (accReg 0) := rfl
theorem combineX_2 : combineX 2 = .bin .pxor fReg (accReg 0) := rfl
theorem combineX_3 : combineX 3 = .bin .paddd fReg (accReg 0) := rfl

theorem dword_xor (a b : BitVec 128) : dword (a ^^^ b) 0 = dword a 0 ^^^ dword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, decide_eq_true hi, Bool.true_and]

/-- A lookup, then its combination, from a state that F's registers alone
separate from `s`. -/
theorem fstep {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) {j : Nat} (hj : j < 4) {t : State}
    (O : FOnly s t) (hf : 0 < j → dword (t.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) (j - 1)) :
    WP isa (.seq (lookup sch j) (.block [combine j])) t (fun t' =>
      dword (t'.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) j ∧ FOnly s t') := by
  obtain hm : t.mem = s.mem := by rw [O.eq]
  obtain hx : t.xmm xL = s.xmm xL := O.xmm _ (by decide)
  apply WP.seq
  refine WP.mono (lookup_run (O.env E) hj) fun u ⟨hu, L⟩ => ?_
  rw [hm, hx] at hu
  refine WP.of_runBlock ⟨(combineX j).exec u, runXops [combineX j] u, ?_, ?_⟩
  · have hf' : 0 < j → dword (u.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) (j - 1) :=
      fun h => by rw [L.xmm _ (by decide)]; exact hf h
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp only [combineX_0, XOp.exec, xmm_setXmm_self, eval_movdqa]; exact hu
    · simp only [combineX_1, XOp.exec, xmm_setXmm_self, XBinOp.eval, dword_ofDwords_0]
      rw [hf' (by decide), hu]; rfl
    · simp only [combineX_2, XOp.exec, xmm_setXmm_self, XBinOp.eval]
      rw [dword_xor, hf' (by decide), hu]; rfl
    · simp only [combineX_3, XOp.exec, xmm_setXmm_self, XBinOp.eval, dword_ofDwords_0]
      rw [hf' (by decide), hu]; rfl
  · have hx : ((combineX j).exec u) = u.setXmm fReg (((combineX j).exec u).xmm fReg) := by
      rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp only [combineX_0, combineX_1, combineX_2, combineX_3, XOp.exec, xmm_setXmm_self] <;> rfl
    refine ⟨fun d hd => ?_, fun g h8 h9 h11 => ?_, ?_⟩
    · have n : d ≠ fReg := fun e => hd (by rw [e]; decide)
      obtain hl : d ∉ lookXRegs := fun h => hd (List.mem_cons_of_mem _ h)
      rw [hx, xmm_setXmm_of_ne _ _ n, L.xmm _ hl, O.xmm _ hd]
    · rw [hx, gpr_setXmm, L.gpr _ h8 h9 h11, O.gpr _ h8 h9 h11]
    · rw [hx]; exact Upd.setXmm (Upd.trans L.eq O.eq) _ _

theorem f_run {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) :
    WP isa (f sch) s (fun s' =>
      dword (s'.xmm fReg) 0 = Spec.Blowfish.f (scheduleAt s.mem S) (dword (s.xmm xL) 0) ∧ FOnly s s') := by
  rw [Impl.Blowfish.X86_64.f]
  obtain st := fun (j : Nat) (hj : j < 4) (t : State) (O : FOnly s t) hf => WP.seq_iff.mp (fstep E hj O hf)
  apply WP.seq
  refine WP.mono (st 0 (by decide) s (FOnly.refl s) (fun h => absurd h (by decide))) fun t0 h0 => ?_
  apply WP.seq
  refine WP.mono h0 fun u0 ⟨v0, O0⟩ => ?_
  apply WP.seq
  refine WP.mono (st 1 (by decide) u0 O0 (fun _ => v0)) fun t1 h1 => ?_
  apply WP.seq
  refine WP.mono h1 fun u1 ⟨v1, O1⟩ => ?_
  apply WP.seq
  refine WP.mono (st 2 (by decide) u1 O1 (fun _ => v1)) fun t2 h2 => ?_
  apply WP.seq
  refine WP.mono h2 fun u2 ⟨v2, O2⟩ => ?_
  apply WP.seq
  refine WP.mono (st 3 (by decide) u2 O2 (fun _ => v2)) fun t3 h3 => ?_
  refine WP.mono h3 fun u3 ⟨v3, O3⟩ => ⟨by rw [v3, fAcc_three], O3⟩

end VG.Proof.Blowfish.X86_64

end

end

/-! ### `Blowfish.X86_64.Round`, which this module and modules that import it used -/

section

/-!
# The rounds

`round_run`: one round on the halves in the low doublewords of `xL` and
`xR`, the P-array entry at `rax`; `cipher_run`: the sixteen and the last
swap undone, `feistel` of the halves.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- What the rounds need: the lookups', and the P-array readable. -/
structure CipherEnv (sch : Reg) (S : Addr) (s : State) : Prop where
  look : LookEnv sch S s
  neA : sch ≠ Reg.rax
  ne10 : sch ≠ Reg.r10
  rdP : ∀ i < 18, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (4096 + 4 * i)) 4

/-- The vector registers the rounds write. -/
def cXRegs : List XReg := xL :: xR :: fXRegs

/-- After `i` rounds. -/
structure CInv (sch : Reg) (S : Addr) (up : Bool) (s₀ : State) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  rax : u.gpr .rax = BitVec.ofNat 64 (4 * ord up i)
  r10 : u.gpr .r10 = BitVec.ofNat 64 (16 - i)
  halves : (dword (u.xmm xL) 0, dword (u.xmm xR) 0) =
    iter (scheduleAt s₀.mem S) (ord up) i (dword (s₀.xmm xL) 0, dword (s₀.xmm xR) 0)
  xmm : ∀ d, d ∉ cXRegs → u.xmm d = s₀.xmm d
  gpr : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u.gpr g = s₀.gpr g
  upd : Upd s₀ u

theorem exec_mov32_mem {s : State} {d : Reg} {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 4) :
    exec (.mov32 d (.mem m)) s = some (s.setReg32 d (s.mem.readW (s.ea m) 32)) := by
  simp only [exec, readSrc32, State.load32, h, ite_true, Option.map_some]

theorem dword_movq (s : State) (r : Reg) (v : BitVec 32) (h : s.gpr r = v.setWidth 64) :
    dword ((0 : BitVec 64) ++ s.gpr r) 0 = v := by
  rw [h]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_dword, BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, Nat.mul_zero, Nat.zero_add,
    itT _ _ (show i < 64 by omega_using [hi]), BitVec.getLsbD_setWidth, decide_eq_true (show i < 64 by omega_using [hi]), Bool.true_and]

theorem runBlock_append_x {a b : List Instr} {s s₁ : State} (h : runBlock isa a s = some s₁) :
    runBlock isa (a ++ b) s = runBlock isa b s₁ := by
  rw [runBlock_append, h]; rfl

theorem ord_lt (up : Bool) {m : Nat} (hm : m < 18) : ord up m < 18 := by
  cases up <;> simp only [ord, Bool.false_eq_true, ite_false, ite_true] <;> omega_arith

theorem ea_p (t : State) (sch : Reg) (S : Addr) (n : Nat) (h1 : t.gpr sch = S)
    (h2 : t.gpr .rax = BitVec.ofNat 64 n) :
    t.ea { base := sch, index := some .rax, disp := Int.ofNat pOff } = S + BitVec.ofNat 64 (4096 + n) := by
  simp only [State.ea, h1, h2, BitVec.mul_one, Rc2.X86_64.offset_nat, pOff]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem add_imm_run (t : State) (d : Reg) (v : BitVec 32) :
    ∃ t', exec (.alu .add d (.imm v)) t = some t' ∧ t'.gpr d = t.gpr d + v.signExtend 64 ∧
      (∀ g, g ≠ d → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ Upd t t' := by
  refine ⟨_, rfl, ?_, fun g hg => ?_, rfl, rfl⟩
  · simp only [gpr_setReg_self]
  · simp only [gpr_setReg_of_ne _ _ hg, gpr_arithFlags]

theorem sub_imm_run (t : State) (d : Reg) (v : BitVec 32) :
    ∃ t', exec (.alu .sub d (.imm v)) t = some t' ∧ t'.gpr d = t.gpr d - v.signExtend 64 ∧
      t'.zf = some (t.gpr d - v.signExtend 64 == 0) ∧
      (∀ g, g ≠ d → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ Upd t t' := by
  refine ⟨_, rfl, ?_, rfl, fun g hg => ?_, rfl, rfl⟩
  · simp only [gpr_setReg_self]
  · simp only [gpr_setReg_of_ne _ _ hg, gpr_arithFlags]

theorem Upd.of_xmm {t t' : State} (h : t' = { t with xmm := t'.xmm }) : Upd t t' := by
  unfold Upd; rw [h]

/-- The end of a round. -/
theorem roundTail_run (t : State) (up : Bool) :
    ∃ t', runBlock isa [bin .pxor xR fReg, bin .movdqa tmp xL, bin .movdqa xL xR, bin .movdqa xR tmp,
        if up then .alu .add .rax (.imm 4) else .alu .sub .rax (.imm 4), .alu .sub .r10 (.imm 1)] t = some t' ∧
      t'.xmm xL = t.xmm xR ^^^ t.xmm fReg ∧ t'.xmm xR = t.xmm xL ∧
      (∀ d, d ≠ xL → d ≠ xR → d ≠ tmp → t'.xmm d = t.xmm d) ∧
      t'.gpr .rax = (if up then t.gpr .rax + 4 else t.gpr .rax - 4) ∧ t'.gpr .r10 = t.gpr .r10 - 1 ∧
      t'.zf = some (t.gpr .r10 - 1 == 0) ∧ (∀ g, g ≠ .rax → g ≠ .r10 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  let ops : List XOp := [.bin .pxor xR fReg, .bin .movdqa tmp xL, .bin .movdqa xL xR, .bin .movdqa xR tmp]
  let t₁ := ops.foldl (fun t op => op.exec t) t
  have r₁ : runBlock isa (ops.map .xop) t = some t₁ := runXops ops t
  have x₁ : t₁.xmm xL = t.xmm xR ^^^ t.xmm fReg ∧ t₁.xmm xR = t.xmm xL ∧
      ∀ d, d ≠ xL → d ≠ xR → d ≠ tmp → t₁.xmm d = t.xmm d := by
    refine ⟨?_, ?_, fun d h1 h2 h3 => ?_⟩
    · simp (disch := decide) only [t₁, ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, eval_movdqa]
      rfl
    · simp (disch := decide) only [t₁, ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, eval_movdqa]
    · simp only [t₁, ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2,
        xmm_setXmm_of_ne _ _ h3]
  have g₁ : t₁.gpr = t.gpr := by simp only [t₁, ops, List.foldl, XOp.exec, gpr_setXmm]
  have u₁ : Upd t t₁ := Upd.of_xmm (by simp only [t₁, ops, List.foldl, XOp.exec, State.setXmm])
  have hA : ∃ t₂, exec (if up then .alu .add .rax (.imm 4) else .alu .sub .rax (.imm 4)) t₁ = some t₂ ∧
      t₂.gpr .rax = (if up then t.gpr .rax + 4 else t.gpr .rax - 4) ∧ (∀ g, g ≠ .rax → t₂.gpr g = t₁.gpr g) ∧
      t₂.xmm = t₁.xmm ∧ Upd t₁ t₂ := by
    cases up
    · obtain ⟨t₂, e, h1, -, h2, h3, h4⟩ := sub_imm_run t₁ .rax 4
      exact ⟨t₂, e, by rw [h1, g₁]; rfl, h2, h3, h4⟩
    · obtain ⟨t₂, e, h1, h2, h3, h4⟩ := add_imm_run t₁ .rax 4
      exact ⟨t₂, e, by rw [h1, g₁]; rfl, h2, h3, h4⟩
  obtain ⟨t₂, e₂, a₂, g₂, x₂, u₂⟩ := hA
  obtain ⟨t₃, e₃, a₃, z₃, g₃, x₃, u₃⟩ := sub_imm_run t₂ .r10 1
  have h10 : t₂.gpr .r10 = t.gpr .r10 := by rw [g₂ _ (by decide), g₁]
  refine ⟨t₃, ?_, by rw [x₃, x₂]; exact x₁.1, by rw [x₃, x₂]; exact x₁.2.1,
    fun d h1 h2 h3 => by rw [x₃, x₂]; exact x₁.2.2 d h1 h2 h3, by rw [g₃ _ (by decide), a₂],
    by rw [a₃, h10]; rfl, by rw [z₃, h10]; rfl, fun g h1 h2 => by rw [g₃ _ h2, g₂ _ h1, g₁],
    Upd.trans u₃ (Upd.trans u₂ u₁)⟩
  show runBlock isa (ops.map .xop ++ [_, _]) t = _
  rw [runBlock_append_x r₁, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]

theorem ord_next (up : Bool) {m : Nat} (hm : m < 16) :
    (if up then BitVec.ofNat 64 (4 * ord up m) + 4 else BitVec.ofNat 64 (4 * ord up m) - 4) =
      BitVec.ofNat 64 (4 * ord up (m + 1)) := by
  cases up <;> simp only [ord, Bool.false_eq_true, ite_false, ite_true] <;>
    apply BitVec.eq_of_toNat_eq <;> simp <;> omega_arith

theorem round_step {sch : Reg} {S : Addr} {up : Bool} {s₀ : State} (E : CipherEnv sch S s₀) {i : Nat}
    (hi : i < 16) {u : State} (I : CInv sch S up s₀ i u) :
    WP isa (round sch up) u (fun u' => CInv sch S up s₀ (i + 1) u' ∧
      u'.zf = some (BitVec.ofNat 64 (16 - (i + 1)) == 0)) := by
  have hrd : u.rd = s₀.rd := by rw [I.upd]
  have hwr : u.wr = s₀.wr := by rw [I.upd]
  have hm : u.mem = s₀.mem := by rw [I.upd]
  have hsch : u.gpr sch = S := by
    rw [I.gpr _ E.neA (E.look.ne8) E.look.ne9 E.ne10 E.look.ne11]; exact E.look.hsch
  have ea := ea_p u sch S _ hsch I.rax
  have hR : InRegions (u.rd ++ u.wr) (u.ea { base := sch, index := some .rax, disp := Int.ofNat pOff }) 4 := by
    rw [ea, hrd, hwr]; exact E.rdP _ (ord_lt up (by omega_using [hi]))
  let P := u.mem.readW (u.ea { base := sch, index := some .rax, disp := Int.ofNat pOff }) 32
  have hP : P = pEntry (scheduleAt s₀.mem S) (ord up i) := by
    rw [pEntry_read _ _ (ord_lt up (by omega_using [hi]))]; simp only [P, ea, hm]
  let u₁ := u.setReg32 .r11 P
  let u₂ := (XOp.movq tmp .r11).exec u₁
  let u₃ := (XOp.bin .pxor xL tmp).exec u₂
  rw [round]
  apply WP.seq
  refine WP.of_runBlock ⟨u₃, ?_, ?_⟩
  · rw [loadP, List.cons_append, runBlock_cons, exec_mov32_mem hR, runStep_some]
    exact runXops [XOp.movq tmp .r11, XOp.bin .pxor xL tmp] u₁
  have x₃ : dword (u₃.xmm xL) 0 = dword (u.xmm xL) 0 ^^^ P := by
    simp (disch := decide) only [u₃, u₂, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, XBinOp.eval]
    rw [dword_xor, dword_movq _ _ P (by simp only [u₁, State.setReg32, gpr_setReg_self])]
    rfl
  have k₃ : ∀ d, d ≠ xL → d ≠ tmp → u₃.xmm d = u.xmm d := fun d h1 h2 => by
    simp only [u₃, u₂, u₁, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, State.setReg32, xmm_setReg]
  have g₃ : ∀ g, g ≠ .r11 → u₃.gpr g = u.gpr g := fun g h => by
    simp only [u₃, u₂, u₁, XOp.exec, gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ h]
  have up₃ : Upd u u₃ := by
    unfold Upd; simp only [u₃, u₂, u₁, XOp.exec, State.setXmm, State.setReg32, State.setReg]
  have LE : LookEnv sch S u₃ := by
    refine ⟨by rw [g₃ _ E.look.ne11, hsch], E.look.ne8, E.look.ne9, E.look.ne11, fun off h => ?_, ?_, ?_, ?_⟩
    · rw [show u₃.rd = s₀.rd by rw [up₃, hrd], show u₃.wr = s₀.wr by rw [up₃, hwr]]; exact E.look.rd off h
    · rw [k₃ _ (by decide) (by decide), I.xmm _ (by decide), E.look.ones]
    · rw [k₃ _ (by decide) (by decide), I.xmm _ (by decide), E.look.sixteen]
    · rw [k₃ _ (by decide) (by decide), I.xmm _ (by decide), E.look.low]
  apply WP.seq
  refine WP.mono (f_run LE) fun u₄ ⟨hf, O⟩ => ?_
  obtain ⟨u₅, r₅, xl₅, xr₅, k₅, rax₅, r10₅, z₅, g₅, up₅⟩ := roundTail_run u₄ up
  refine WP.of_runBlock ⟨u₅, r₅, ⟨by omega_using [hi], ?_, ?_, ?_, fun d hd => ?_, fun g h1 h2 h3 h4 h5 => ?_, ?_⟩, ?_⟩
  · rw [rax₅, O.gpr _ (by decide) (by decide) (by decide), g₃ _ (by decide), I.rax, ord_next up hi]
  · rw [r10₅, O.gpr _ (by decide) (by decide) (by decide), g₃ _ (by decide), I.r10]
    apply BitVec.eq_of_toNat_eq; simp; omega_using [hi]
  · rw [iter_succ, ← I.halves, xl₅, xr₅, dword_xor, hf, O.xmm xR (by decide), O.xmm xL (by decide),
      k₃ xR (by decide) (by decide), show u₃.mem = s₀.mem by rw [up₃, hm], x₃, hP]
    simp only [roundStep]
    rw [BitVec.xor_comm]
  · have h1 : d ≠ xL := fun e => hd (by rw [e]; decide)
    have h2 : d ≠ xR := fun e => hd (by rw [e]; decide)
    have h3 : d ≠ tmp := fun e => hd (by rw [e]; decide)
    have hf' : d ∉ fXRegs := fun h => hd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    rw [k₅ _ h1 h2 h3, O.xmm _ hf', k₃ _ h1 h3, I.xmm _ hd]
  · rw [g₅ _ h1 h4, O.gpr _ h2 h3 h5, g₃ _ h5, I.gpr _ h1 h2 h3 h4 h5]
  · exact Upd.trans up₅ (Upd.trans O.eq (Upd.trans up₃ I.upd))
  · rw [z₅, O.gpr _ (by decide) (by decide) (by decide), g₃ _ (by decide), I.r10,
      show BitVec.ofNat 64 (16 - i) - 1 = BitVec.ofNat 64 (16 - (i + 1)) from by
        apply BitVec.eq_of_toNat_eq; simp; omega_using [hi]]


/-- Only the rounds' registers and the flags change. -/
structure COnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ cXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g
  upd : Upd s s'

/-- The P-array entry `i` into `tmp`, XORed into `d`. -/
theorem xorP_run {sch : Reg} {S : Addr} {s₀ : State} (E : CipherEnv sch S s₀) {t : State} (O : COnly s₀ t)
    {i : Nat} (hi : i < 18) {d : XReg} (hd : d ≠ tmp) :
    ∃ t', runBlock isa [.mov32 .r11 (.mem (mem sch (pOff + 4 * i))), .xop (.movq tmp .r11), bin .pxor d tmp] t =
        some t' ∧
      dword (t'.xmm d) 0 = dword (t.xmm d) 0 ^^^ pEntry (scheduleAt s₀.mem S) i ∧
      (∀ e, e ≠ d → e ≠ tmp → t'.xmm e = t.xmm e) ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  have hsch : t.gpr sch = S := by
    rw [O.gpr _ E.neA E.look.ne8 E.look.ne9 E.ne10 E.look.ne11]; exact E.look.hsch
  have ea : t.ea (mem sch (pOff + 4 * i)) = S + BitVec.ofNat 64 (4096 + 4 * i) := by
    simp only [State.ea, mem, hsch, Rc2.X86_64.offset_nat, pOff]
  have hR : InRegions (t.rd ++ t.wr) (t.ea (mem sch (pOff + 4 * i))) 4 := by
    rw [ea, show t.rd = s₀.rd by rw [O.upd], show t.wr = s₀.wr by rw [O.upd]]; exact E.rdP i hi
  let P := t.mem.readW (t.ea (mem sch (pOff + 4 * i))) 32
  let t₁ := t.setReg32 .r11 P
  let t₂ := (XOp.movq tmp .r11).exec t₁
  let t₃ := (XOp.bin .pxor d tmp).exec t₂
  refine ⟨t₃, ?_, ?_, fun e h1 h2 => ?_, fun g h => ?_, ?_⟩
  · rw [runBlock_cons, exec_mov32_mem hR, runStep_some]
    exact runXops [XOp.movq tmp .r11, XOp.bin .pxor d tmp] t₁
  · simp only [t₃, t₂, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hd, XBinOp.eval]
    rw [dword_xor, dword_movq _ _ P (by simp only [t₁, State.setReg32, gpr_setReg_self]), pEntry_read _ _ hi]
    simp only [P, ea, show t.mem = s₀.mem by rw [O.upd]]
    rfl
  · simp only [t₃, t₂, t₁, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, State.setReg32, xmm_setReg]
  · simp only [t₃, t₂, t₁, XOp.exec, gpr_setXmm, State.setReg32, gpr_setReg_of_ne _ _ h]
  · unfold Upd; simp only [t₃, t₂, t₁, XOp.exec, State.setXmm, State.setReg32, State.setReg]

theorem cipher_run {sch : Reg} {S : Addr} {s : State} (E : CipherEnv sch S s) (up : Bool) :
    WP isa (cipher sch up) s (fun s' =>
      dword (s'.xmm xR) 0 = (feistel (scheduleAt s.mem S) (ord up) (dword (s.xmm xL) 0) (dword (s.xmm xR) 0)).1 ∧
      dword (s'.xmm xL) 0 = (feistel (scheduleAt s.mem S) (ord up) (dword (s.xmm xL) 0) (dword (s.xmm xR) 0)).2 ∧
      COnly s s') := by
  rw [cipher]
  apply WP.seq
  let u₀ := (s.setReg32 .rax (if up then 0 else 68)).setReg32 .r10 16
  have I0 : CInv sch S up s 0 u₀ := by
    refine ⟨by omega_using [], ?_, ?_, rfl, fun d _ => rfl, fun g h1 _ _ h4 _ => ?_, ?_⟩
    · simp only [u₀, State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rax ≠ Reg.r10 by decide), gpr_setReg_self]
      cases up <;> rfl
    · simp only [u₀, State.setReg32, gpr_setReg_self]; rfl
    · simp only [u₀, State.setReg32, gpr_setReg_of_ne _ _ h4, gpr_setReg_of_ne _ _ h1]
    · unfold Upd; simp only [u₀, State.setReg32, State.setReg]
  refine WP.of_runBlock ⟨u₀, ?_, ?_⟩
  · rw [runBlock_cons, exec_mov32_imm, runStep_some, runBlock_cons, exec_mov32_imm, runStep_some, runBlock_nil]
  apply WP.seq
  refine WP.mono (WP.loop (M := isa) (Q := CInv sch S up s 16)
    (fun m u => ∃ i, i < 16 ∧ m = 16 - i ∧ CInv sch S up s i u) ?_ 16 u₀ ⟨0, by omega_using [], rfl, I0⟩)
    fun v Iv => ?_
  · intro m u ⟨i, hi, hm, I⟩
    refine WP.mono (round_step E hi I) fun u' ⟨I', zu⟩ => ?_
    have ev : isa.eval .ne u' = some (!(BitVec.ofNat 64 (16 - (i + 1)) == 0)) := by
      show u'.zf.map (!·) = _; rw [zu]; rfl
    by_cases h : i + 1 = 16
    · left; exact ⟨by rw [ev, h]; rfl, h ▸ I'⟩
    · right
      have nz : BitVec.ofNat 64 (16 - (i + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_using [hi, h, this]
      exact ⟨by rw [ev, show (BitVec.ofNat 64 (16 - (i + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
        16 - (i + 1), by omega_using [hi, hm], i + 1, by omega_using [hi, h], rfl, I'⟩
  have Ov : COnly s v := ⟨Iv.xmm, Iv.gpr, Iv.upd⟩
  obtain ⟨w₁, r₁, x₁, k₁, g₁, u₁⟩ := xorP_run E Ov (i := ord up 16) (ord_lt up (by decide)) (d := xL) (by decide)
  have O₁ : COnly s w₁ := ⟨fun d hd => by
      rw [k₁ _ (fun e => hd (by rw [e]; decide)) (fun e => hd (by rw [e]; decide)), Iv.xmm d hd],
    fun g h1 h2 h3 h4 h5 => by rw [g₁ _ h5, Iv.gpr _ h1 h2 h3 h4 h5], Upd.trans u₁ Iv.upd⟩
  obtain ⟨w₂, r₂, x₂, k₂, g₂, u₂⟩ := xorP_run E O₁ (i := ord up 17) (ord_lt up (by decide)) (d := xR) (by decide)
  refine WP.of_runBlock ⟨w₂, ?_, ?_, ?_, ?_⟩
  · have e1 : pOff + 4 * (if up then 16 else 1) = pOff + 4 * ord up 16 := by cases up <;> rfl
    have e2 : pOff + 4 * (if up then 17 else 0) = pOff + 4 * ord up 17 := by cases up <;> rfl
    rw [e1, e2]
    exact cat_run r₁ r₂
  · rw [x₂, k₁ _ (by decide) (by decide), feistel_eq, ← Iv.halves]
  · rw [k₂ _ (by decide) (by decide), x₁, feistel_eq, ← Iv.halves]
  · exact ⟨fun d hd => by
      rw [k₂ _ (fun e => hd (by rw [e]; decide)) (fun e => hd (by rw [e]; decide)), O₁.xmm d hd],
    fun g h1 h2 h3 h4 h5 => by rw [g₂ _ h5, O₁.gpr _ h1 h2 h3 h4 h5], Upd.trans u₂ O₁.upd⟩


end VG.Proof.Blowfish.X86_64

end

end

/-!
# A block in and out of the halves

`loadBlock_run`: the big-endian words of the block at `rsi` into the halves;
`storeBlock_run`: the output block, xL (in `xR`) and xR (in `xL`), back to
`rsi`, through the working space at `rcx`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem bswap32_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (bswap32 x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, getLsbD_bswap32_block _ hb hi]
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> simp

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem bswap_readW (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    bswap32 (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [bswap32_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega_using [ho]),
    show 8 * (3 - b) = 8 * (3 - b) from rfl, ← Mem.readW_byte m _ (by omega_using []), Offset.add_add]

theorem ea_mem (t : State) (r : Reg) (o : Nat) : t.ea (mem r o) = t.gpr r + BitVec.ofNat 64 o := by
  simp only [State.ea, mem, Rc2.X86_64.offset_nat]

theorem exec_bswap32 (s : State) (d : Reg) :
    exec (.bswap32 d) s = some (s.setReg32 d (bswap32 ((s.gpr d).setWidth 32))) := rfl

theorem loadBlock_run (t : State) (q : Addr) (hq : t.gpr .rsi = q)
    (hR : ∀ o ≤ 4, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 o) 4) :
    ∃ t', runBlock isa loadBlock t = some t' ∧
      dword (t'.xmm xL) 0 = decodeWord (blockAt t.mem q) 0 ∧ dword (t'.xmm xR) 0 = decodeWord (blockAt t.mem q) 4 ∧
      (∀ d, d ≠ xL → d ≠ xR → t'.xmm d = t.xmm d) ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  have r0 : InRegions (t.rd ++ t.wr) (t.ea (mem .rsi 0)) 4 := by rw [ea_mem, hq]; exact hR 0 (by omega_using [])
  let w0 := t.mem.readW (t.ea (mem .rsi 0)) 32
  let t₁ := t.setReg32 .r11 w0
  let t₂ := t₁.setReg32 .r11 (bswap32 ((t₁.gpr .r11).setWidth 32))
  let t₃ := (XOp.movq xL .r11).exec t₂
  have r4 : InRegions (t₃.rd ++ t₃.wr) (t₃.ea (mem .rsi 4)) 4 := by
    rw [ea_mem]; simp only [t₃, t₂, t₁, XOp.exec, gpr_setXmm, State.setReg32, rd_setXmm, wr_setXmm, rd_setReg, wr_setReg,
      gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.r11 by decide), hq]; exact hR 4 (by omega_using [])
  let w4 := t₃.mem.readW (t₃.ea (mem .rsi 4)) 32
  let t₄ := t₃.setReg32 .r11 w4
  let t₅ := t₄.setReg32 .r11 (bswap32 ((t₄.gpr .r11).setWidth 32))
  let t₆ := (XOp.movq xR .r11).exec t₅
  refine ⟨t₆, ?_, ?_, ?_, fun d h1 h2 => ?_, fun g h => ?_, ?_⟩
  · rw [loadBlock, runBlock_cons, exec_mov32_mem r0, runStep_some, runBlock_cons, exec_bswap32, runStep_some,
      runBlock_cons, exec_xop, runStep_some, runBlock_cons, exec_mov32_mem r4, runStep_some, runBlock_cons,
      exec_bswap32, runStep_some, runBlock_cons, exec_xop, runStep_some, runBlock_nil]
  · simp only [t₆, XOp.exec, xmm_setXmm_of_ne _ _ (show xL ≠ xR by decide), t₅, t₄, State.setReg32, xmm_setReg,
      t₃, xmm_setXmm_self]
    rw [dword_movq _ _ (bswap32 w0) (by simp only [t₂, t₁, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]),
      ← bswap_readW _ _ (by omega_using [])]
    simp only [w0, ea_mem, hq]
  · simp only [t₆, XOp.exec, xmm_setXmm_self]
    rw [dword_movq _ _ (bswap32 w4) (by simp only [t₅, t₄, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]),
      ← bswap_readW _ _ (by omega_using [])]
    simp only [w4, ea_mem, t₃, t₂, t₁, XOp.exec, gpr_setXmm, State.setReg32, mem_setXmm, mem_setReg,
      gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.r11 by decide), hq]
  · simp only [t₆, t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setReg32, xmm_setXmm_of_ne _ _ h2, xmm_setReg,
      xmm_setXmm_of_ne _ _ h1]
  · simp only [t₆, t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setReg32, gpr_setXmm, gpr_setReg_of_ne _ _ h]
  · unfold Upd; simp only [t₆, t₅, t₄, t₃, t₂, t₁, XOp.exec, State.setReg32, State.setXmm, State.setReg]

theorem exec_movdquStore {s : State} {m : MemOp} {r : XReg} (h : InRegions s.wr (s.ea m) 16) :
    exec (.movdquStore m r) s = some { s with mem := s.mem.writeW (s.ea m) (s.xmm r) } := by
  simp only [exec, State.store128, h, ite_true]

theorem exec_store32 {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 4) :
    exec (.store32 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 32) } := by
  simp only [exec, State.store32, h, ite_true]

theorem writeW32_byte (m : Mem) (a : Addr) (v : BitVec 32) {b : Nat} (hb : b < 4) :
    m.writeW a v (a + BitVec.ofNat 64 b) = v.extractLsb' (8 * b) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a hb, Mem.readW_writeW_self32]

theorem readW_writeW128_0 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 32 = dword v 0 := by
  have := readW_writeW128 m a v (j := 0) (by decide)
  rwa [Nat.mul_zero, BitVec.add_zero] at this

theorem writeW_sep {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) (h : ¬ (x - a).toNat < w / 8) :
    m.writeW a v x = m x := Mem.write_apply h

theorem inRegions_off {rs : List Region} {a : Addr} {N o n : Nat} (h : InRegions rs a N) (hon : o + n ≤ N) :
    InRegions rs (a + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a + BitVec.ofNat 64 o - r.base = (a - r.base) + BitVec.ofNat 64 o := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 o),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((a - r.base).toNat + o % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le o (2 ^ 64)
  omega_using [hon, hc]

theorem inRegions_append_right {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega_using [h₁]) (by simp only [Region.Contains]; omega_using [h₂])

/-- What a block store needs: the block and the working space writable, apart. -/
structure StoreEnv (q B : Addr) (t : State) : Prop where
  rsi : t.gpr .rsi = q
  rcx : t.gpr .rcx = B
  wq : InRegions t.wr q 8
  wB : InRegions t.wr B 16
  sep : Mem.Sep q 8 B 16
  sep' : Mem.Sep B 16 q 8

theorem storeBlock_run {q B : Addr} {t : State} (E : StoreEnv q B t) :
    ∃ t', runBlock isa storeBlock t = some t' ∧
      (∀ i < 8, t'.mem (q + BitVec.ofNat 64 i) =
        (encodeBlock (dword (t.xmm xR) 0) (dword (t.xmm xL) 0)).getD i 0) ∧
      Frame [⟨q, 8⟩, ⟨B, 16⟩] t.mem t'.mem ∧ (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, mem := t'.mem } := by
  let A := dword (t.xmm xR) 0
  let Bw := dword (t.xmm xL) 0
  let t₁ : State := { t with mem := t.mem.writeW (t.ea (mem .rcx 0)) (t.xmm xR) }
  let t₂ := t₁.setReg32 .r11 (t₁.mem.readW (t₁.ea (mem .rcx 0)) 32)
  let t₃ := t₂.setReg32 .r11 (bswap32 ((t₂.gpr .r11).setWidth 32))
  let t₄ : State := { t₃ with mem := t₃.mem.writeW (t₃.ea (mem .rsi 0)) ((t₃.gpr .r11).setWidth 32) }
  let t₅ : State := { t₄ with mem := t₄.mem.writeW (t₄.ea (mem .rcx 0)) (t₄.xmm xL) }
  let t₆ := t₅.setReg32 .r11 (t₅.mem.readW (t₅.ea (mem .rcx 0)) 32)
  let t₇ := t₆.setReg32 .r11 (bswap32 ((t₆.gpr .r11).setWidth 32))
  let t₈ : State := { t₇ with mem := t₇.mem.writeW (t₇.ea (mem .rsi 4)) ((t₇.gpr .r11).setWidth 32) }
  have g : ∀ u : State, u.gpr .rsi = q → u.gpr .rcx = B → (u.setReg32 .r11 0).gpr .rsi = q := fun u h _ => by
    simp only [State.setReg32, gpr_setReg_of_ne _ _ (show Reg.rsi ≠ Reg.r11 by decide), h]
  have gr : ∀ k : Nat, k < 8 → ∀ r, r ≠ Reg.r11 →
      ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD k t).gpr r = t.gpr r := by
    intro k hk r hr
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, State.setReg32,
      gpr_setReg_of_ne _ _ hr]
  have eB : ∀ k < 8, ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD k t).ea (mem .rcx 0) = B + BitVec.ofNat 64 0 :=
    fun k hk => by rw [ea_mem, gr k hk _ (by decide), E.rcx]
  have eq0 : ∀ k < 8, ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD k t).ea (mem .rsi 0) = q + BitVec.ofNat 64 0 :=
    fun k hk => by rw [ea_mem, gr k hk _ (by decide), E.rsi]
  have eq4 : ([t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈].getD 6 t).ea (mem .rsi 4) = q + BitVec.ofNat 64 4 := by
    rw [ea_mem, gr 6 (by decide) _ (by decide), E.rsi]
  have et : t.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := by rw [ea_mem, E.rcx]
  have wr : ∀ u : State, u.wr = t.wr → InRegions u.wr (B + BitVec.ofNat 64 0) 16 := fun u h => by
    rw [h]; exact inRegions_off E.wB (by omega_using [])
  have rB : ∀ u : State, u.wr = t.wr → InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 0) 4 := fun u h => by
    rw [h]; exact inRegions_append_right (inRegions_off E.wB (by omega_using []))
  have wq : ∀ u : State, u.wr = t.wr → ∀ o, o ≤ 4 → InRegions u.wr (q + BitVec.ofNat 64 o) 4 := fun u h o ho => by
    rw [h]; exact inRegions_off E.wq (by omega_using [ho])
  have run : runBlock isa storeBlock t = some t₈ := by
    rw [storeBlock, runBlock_cons, exec_movdquStore (by rw [et]; exact wr t rfl), runStep_some,
      runBlock_cons, exec_mov32_mem (by have h := rB t₁ rfl; rw [← (eB 0 (by decide) : t₁.ea _ = _)] at h; exact h), runStep_some,
      runBlock_cons, exec_bswap32, runStep_some,
      runBlock_cons, exec_store32 (by have h := wq t₃ rfl 0 (by omega_using []); rw [← (eq0 2 (by decide) : t₃.ea _ = _)] at h; exact h),
      runStep_some,
      runBlock_cons, exec_movdquStore (by have h := wr t₄ rfl; rw [← (eB 3 (by decide) : t₄.ea _ = _)] at h; exact h), runStep_some,
      runBlock_cons, exec_mov32_mem (by have h := rB t₅ rfl; rw [← (eB 4 (by decide) : t₅.ea _ = _)] at h; exact h), runStep_some,
      runBlock_cons, exec_bswap32, runStep_some,
      runBlock_cons, exec_store32 (by have h := wq t₇ rfl 4 (by omega_using []); rw [← (eq4 : t₇.ea _ = _)] at h; exact h), runStep_some,
      runBlock_nil]
  have x₄ : t₄.xmm = t.xmm := rfl
  have ea1 : t₁.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := eB 0 (by decide)
  have ea3 : t₃.ea (mem .rsi 0) = q + BitVec.ofNat 64 0 := eq0 2 (by decide)
  have ea4 : t₄.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := eB 3 (by decide)
  have ea5 : t₅.ea (mem .rcx 0) = B + BitVec.ofNat 64 0 := eB 4 (by decide)
  have ea7 : t₇.ea (mem .rsi 4) = q + BitVec.ofNat 64 4 := eq4
  have w3 : (t₃.gpr .r11).setWidth 32 = bswap32 A := by
    simp only [t₃, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]
    rw [show (t₂.gpr .r11).setWidth 32 = t₁.mem.readW (t₁.ea (mem .rcx 0)) 32 by
      simp only [t₂, State.setReg32, gpr_setReg_self, setWidth_setWidth_32], ea1,
      show t₁.mem = t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR) by simp only [t₁, et],
      readW_writeW128_0]
  have w7 : (t₇.gpr .r11).setWidth 32 = bswap32 Bw := by
    simp only [t₇, State.setReg32, gpr_setReg_self, setWidth_setWidth_32]
    rw [show (t₆.gpr .r11).setWidth 32 = t₅.mem.readW (t₅.ea (mem .rcx 0)) 32 by
      simp only [t₆, State.setReg32, gpr_setReg_self, setWidth_setWidth_32], ea5,
      show t₅.mem = t₄.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xL) by simp only [t₅, ea4, x₄],
      readW_writeW128_0]
  have m8 : t₈.mem = (((t.mem.writeW (B + BitVec.ofNat 64 0) (t.xmm xR)).writeW (q + BitVec.ofNat 64 0)
      (bswap32 A)).writeW (B + BitVec.ofNat 64 0) (t.xmm xL)).writeW (q + BitVec.ofNat 64 4) (bswap32 Bw) := by
    show t₇.mem.writeW (t₇.ea (mem .rsi 4)) ((t₇.gpr .r11).setWidth 32) = _
    rw [ea7, w7]
    show (t₄.mem.writeW (t₄.ea (mem .rcx 0)) (t₄.xmm xL)).writeW _ _ = _
    rw [ea4, x₄]
    show ((t₃.mem.writeW (t₃.ea (mem .rsi 0)) ((t₃.gpr .r11).setWidth 32)).writeW _ _).writeW _ _ = _
    rw [ea3, w3]
    show (((t.mem.writeW (t.ea (mem .rcx 0)) (t.xmm xR)).writeW _ _).writeW _ _).writeW _ _ = _
    rw [et]
  refine ⟨t₈, run, fun i hi => ?_, ?_, fun g h => gr 7 (by decide) g h, ?_⟩
  · have hi64 : i < 2 ^ 64 := by omega_using [hi]
    rw [m8, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4)]
      rw [writeW_sep _ (Offset.sep q (d := i) (n := 1) (e := 4) (k := 4) (.inl (by omega_using [h4])) (by omega_using [hi]) (by omega_using []) _
        (by rw [BitVec.sub_self]; decide)), writeW_sep _ (by
          rw [BitVec.add_zero]; exact E.sep _ (by rw [Mem.sub_ofNat_toNat q hi64]; omega_using [hi])),
        show q + BitVec.ofNat 64 i = q + BitVec.ofNat 64 0 + BitVec.ofNat 64 i by rw [BitVec.add_zero],
        writeW32_byte _ _ _ h4, bswap32_byte _ h4]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4),
        show q + BitVec.ofNat 64 i = q + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) by
          rw [Offset.add_add]; congr 2; omega_using [h4],
        writeW32_byte _ _ _ (by omega_using [hi]), bswap32_byte _ (by omega_using [hi])]
      congr 2; omega_using [h4]
  · have mq : (⟨q, 8⟩ : Region) ∈ [⟨q, 8⟩, ⟨B, 16⟩] := List.mem_cons_self
    have mB : (⟨B, 16⟩ : Region) ∈ [⟨q, 8⟩, ⟨B, 16⟩] := List.mem_cons_of_mem _ List.mem_cons_self
    rw [m8]
    exact ((((Frame.refl _ _).writeW mB _ (Offset.contains_base B (by decide) (by decide))).writeW mq _
      (Offset.contains_base q (by decide) (by decide))).writeW mB _
      (Offset.contains_base B (by decide) (by decide))).writeW mq _ (Offset.contains_base q (by decide) (by decide))
  · simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, State.setReg32, State.setReg]



end VG.Proof.Blowfish.X86_64

end

end

/-!
# The ECB functions

`ecb_correct`: every block becomes its encryption or decryption, one at a
time, through the working space.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block at `p`. -/
abbrev wAt (p : Addr) (b : Nat) : Addr := p + BitVec.ofNat 64 (8 * b)

theorem constants_run (t : State) :
    ∃ t', runBlock isa constants t = some t' ∧ t'.xmm onesReg = wordsOf 1 ∧ t'.xmm sixteenReg = wordsOf 16 ∧
      t'.xmm lowReg = wordsOf 0xFF ∧
      (∀ d, d ≠ onesReg → d ≠ sixteenReg → d ≠ lowReg → d ≠ tmp → t'.xmm d = t.xmm d) ∧
      (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  obtain ⟨t₁, r₁, v₁, k₁, g₁, e₁⟩ := loadConst_run t (dst := onesReg) (by decide) (wordsOf 1)
  obtain ⟨t₂, r₂, v₂, k₂, g₂, e₂⟩ := loadConst_run t₁ (dst := sixteenReg) (by decide) (wordsOf 16)
  obtain ⟨t₃, r₃, v₃, k₃, g₃, e₃⟩ := loadConst_run t₂ (dst := lowReg) (by decide) (wordsOf 0xFF)
  refine ⟨t₃, cat_run (cat_run r₁ r₂) r₃, by rw [k₃ _ (by decide) (by decide), k₂ _ (by decide) (by decide), v₁],
    by rw [k₃ _ (by decide) (by decide), v₂], v₃, fun d h1 h2 h3 h4 => by rw [k₃ _ h3 h4, k₂ _ h2 h4, k₁ _ h1 h4],
    fun g h => by rw [g₃ _ h, g₂ _ h, g₁ _ h], ?_⟩
  obtain u : ∀ {a c : State}, a = { c with gpr := a.gpr, xmm := a.xmm } → Upd c a := fun h => by
    unfold Upd; rw [h]
  exact Upd.trans (u e₃) (Upd.trans (u e₂) (u e₁))

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 4168⟩]
  wr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 256⟩]
  keyData : (⟨s.gpr .rdi, 4168⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  keyBuf : (⟨s.gpr .rdi, 4168⟩ : Region).Disjoint ⟨s.gpr .rcx, 256⟩
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 256⟩
  retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 256⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

/-- The loop's fixed facts: the state after the constants. -/
structure LoopEnv (S D B : Addr) (n : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [⟨S, 4168⟩]
  wr : s₀.wr = [⟨D, 8 * n⟩, ⟨B, 256⟩]
  keyData : (⟨S, 4168⟩ : Region).Disjoint ⟨D, 8 * n⟩
  keyBuf : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 256⟩
  dataBuf : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 256⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  rdi : s₀.gpr .rdi = S
  rcx : s₀.gpr .rcx = B
  ones : s₀.xmm onesReg = wordsOf 1
  sixteen : s₀.xmm sixteenReg = wordsOf 16
  low : s₀.xmm lowReg = wordsOf 0xFF

/-- After `k` blocks. -/
structure EInv (S D B : Addr) (n : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ n
  rsi : u.gpr .rsi = wAt D k
  rdx : u.gpr .rdx = BitVec.ofNat 64 (n - k)
  rdi : u.gpr .rdi = S
  rcx : u.gpr .rcx = B
  gpr : ∀ g, g ≠ .rsi → g ≠ .rdx → g ≠ .r11 → g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → u.gpr g = s₀.gpr g
  xmm : ∀ d, d ∉ cXRegs → u.xmm d = s₀.xmm d
  done : ∀ b < k, blockAt u.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < n → blockAt u.mem (wAt D b) = blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * n⟩, ⟨B, 256⟩] s₀.mem u.mem
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr

theorem ecb_step {S D B : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D B n s₀) {k : Nat}
    (hk : k < n) {u : State} (I : EInv S D B n up s₀ k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher .rdi up)
      (.block (storeBlock ++ ([.alu .add .rsi (.imm 8), .alu .sub .rdx (.imm 1)] : List Instr))))) u
      (fun u' => EInv S D B n up s₀ (k + 1) u' ∧ u'.zf = some (BitVec.ofNat 64 (n - (k + 1)) == 0)) := by
  have fit := L.fit
  obtain hrdw : u.rd ++ u.wr = [⟨S, 4168⟩, ⟨D, 8 * n⟩, ⟨B, 256⟩] := by rw [I.rd, I.wr, L.rd, L.wr]; rfl
  obtain dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.wr, L.wr]; exact List.mem_cons_self
  obtain bR : (⟨B, 256⟩ : Region) ∈ u.wr := by rw [I.wr, L.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain sR : (⟨S, 4168⟩ : Region) ∈ u.rd ++ u.wr := by rw [hrdw]; exact List.mem_cons_self
  -- the block in
  obtain ⟨u₁, r₁, l₁, h₁, k₁, g₁, up₁⟩ := loadBlock_run u (wAt D k) I.rsi fun o ho =>
    ⟨_, List.mem_append_right _ dR, by rw [Offset.add_add]; exact Offset.contains_base D (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.of_runBlock ⟨u₁, r₁, ?_⟩
  obtain m₁ : u₁.mem = u.mem := by rw [up₁]
  obtain hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.keyData
      · exact L.keyBuf
  obtain CE : CipherEnv .rdi S u₁ := by
    obtain rdw₁ : u₁.rd ++ u₁.wr = u.rd ++ u.wr := by rw [up₁]
    refine ⟨⟨by rw [g₁ _ (by decide), I.rdi], by decide, by decide, by decide, fun off h => ?_,
      by rw [k₁ _ (by decide) (by decide), I.xmm _ (by decide), L.ones],
      by rw [k₁ _ (by decide) (by decide), I.xmm _ (by decide), L.sixteen],
      by rw [k₁ _ (by decide) (by decide), I.xmm _ (by decide), L.low]⟩, by decide, by decide, fun i hi => ?_⟩
    · rw [rdw₁]; exact ⟨_, sR, Offset.contains_base S (by omega_arith) (by omega_arith)⟩
    · rw [rdw₁]; exact ⟨_, sR, Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c₁, c₂, O⟩ => ?_
  obtain up₂ : Upd u u₂ := Upd.trans O.upd up₁
  obtain wr₂ : u₂.wr = u.wr := by rw [up₂]
  obtain m₂ : u₂.mem = u.mem := by rw [up₂]
  obtain gu : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u₂.gpr g = u.gpr g :=
    fun g h1 h2 h3 h4 h5 => by rw [O.gpr _ h1 h2 h3 h4 h5, g₁ _ h5]
  obtain subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_arith)
  obtain subB : Region.Sub ⟨B, 16⟩ ⟨B, 256⟩ := Region.sub_prefix (by omega_arith)
  obtain dKB : (⟨wAt D k, 8⟩ : Region).Disjoint ⟨B, 16⟩ := (L.dataBuf.sub_left subK).sub_right subB
  obtain SE : StoreEnv (wAt D k) B u₂ := by
    refine ⟨by rw [gu _ (by decide) (by decide) (by decide) (by decide) (by decide), I.rsi],
      by rw [gu _ (by decide) (by decide) (by decide) (by decide) (by decide), I.rcx],
      ⟨_, by rw [wr₂]; exact dR, Offset.contains_base D (by omega_arith) (by omega_arith)⟩,
      ⟨_, by rw [wr₂]; exact bR, by simp [Region.Contains]⟩, sep_of_disjoint dKB, sep_of_disjoint dKB.symm⟩
  obtain ⟨u₃, r₃, b₃, f₃, g₃, e₃⟩ := storeBlock_run SE
  obtain ⟨u₄, r₄, a₄, k₄, x₄, up₄⟩ := add_imm_run u₃ .rsi 8
  obtain ⟨u₅, r₅, a₅, z₅, k₅, x₅, up₅⟩ := sub_imm_run u₄ .rdx 1
  refine WP.of_runBlock ⟨u₅, ?_, ?_, ?_⟩
  · refine cat_run r₃ ?_
    rw [runBlock_cons, r₄, runStep_some, runBlock_cons, r₅, runStep_some, runBlock_nil]
  obtain m₅ : u₅.mem = u₃.mem := by rw [up₅, up₄]
  obtain g₅ : ∀ g, g ≠ .rsi → g ≠ .rdx → u₅.gpr g = u₃.gpr g := fun g h1 h2 => by rw [k₅ _ h2, k₄ _ h1]
  obtain hgk : ∀ g, g ≠ .rsi → g ≠ .rdx → g ≠ .r11 → g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → u₅.gpr g = u.gpr g :=
    fun g h1 h2 h3 h4 h5 h6 h7 => by rw [g₅ _ h1 h2, g₃ _ h3, gu _ h4 h5 h6 h7 h3]
  obtain other : ∀ b, b < n → b ≠ k → blockAt u₅.mem (wAt D b) = blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₅, blockAt_frame f₃ fun r hr => ?_, m₂]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (L.dataBuf.sub_left (Offset.sub_base D (by omega_arith))).sub_right subB
  refine ⟨by omega_arith, ?_, ?_, ?_, ?_,
    fun g h1 h2 h3 h4 h5 h6 h7 => by rw [hgk _ h1 h2 h3 h4 h5 h6 h7, I.gpr _ h1 h2 h3 h4 h5 h6 h7], fun d hd => ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [k₅ _ (by decide), a₄, g₃ _ (by decide), gu _ (by decide) (by decide) (by decide) (by decide) (by decide),
      I.rsi, wAt, wAt, show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    congr 2
  · rw [a₅, k₄ _ (by decide), g₃ _ (by decide),
      gu _ (by decide) (by decide) (by decide) (by decide) (by decide), I.rdx]
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [hgk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.rdi]
  · rw [hgk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.rcx]
  · rw [x₅, x₄, show u₃.xmm = u₂.xmm by rw [e₃], O.xmm _ hd, k₁ _ (fun e => hd (by rw [e]; decide))
      (fun e => hd (by rw [e]; decide)), I.xmm _ hd]
  · by_cases hbk : b = k
    · subst hbk
      refine blockAt_eq _ _ _ fun i hi => ?_
      rw [m₅, b₃ i hi, c₁, c₂, l₁, h₁, show u₁.mem = u.mem from m₁, hK,
        I.rest b (by omega_arith) hk, blockOut_eq]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · rw [m₅]
    refine I.frame.trans ?_
    rw [← m₂]
    refine Frame.sub f₃ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subB⟩
  · rw [show u₅.rd = u₂.rd by rw [up₅, up₄, e₃], up₂, I.rd]
  · rw [show u₅.wr = u₂.wr by rw [up₅, up₄, e₃], up₂, I.wr]
  · rw [z₅, k₄ _ (by decide), g₃ _ (by decide), gu _ (by decide) (by decide) (by decide) (by decide) (by decide),
      I.rdx, show BitVec.ofNat 64 (n - k) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (n - (k + 1)) from by
        apply BitVec.eq_of_toNat_eq; simp; omega_arith]

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .rdx).toNat, blockAt s'.mem (wAt (s.gpr .rsi) b) =
    blockOut (scheduleAt s.mem (s.gpr .rdi)) up (blockAt s.mem (wAt (s.gpr .rsi) b))
  gpr : ∀ g, g ≠ .rsi → g ≠ .rdx → g ≠ .r11 → g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → s'.gpr g = s.gpr g
  frame : Frame [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 256⟩] s.mem s'.mem

theorem exec_test (t : State) (d : Reg) :
    exec (.alu .test d (.reg d)) t = some (arithFlags t (t.gpr d &&& t.gpr d) false false) := rfl

theorem ecb_correct (up : Bool) {s : State} (h : EcbPre s) : WP isa (ecb up) s (EcbPost up s) := by
  have fit := h.fit
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  let B := s.gpr .rcx
  rw [Impl.Blowfish.X86_64.ecb]
  apply WP.seq
  obtain ⟨s₀, r₀, o₀, x₀, l₀, k₀, g₀, up₀⟩ := constants_run s
  refine WP.of_runBlock ⟨s₀, r₀, ?_⟩
  obtain m₀ : s₀.mem = s.mem := by rw [up₀]
  obtain L : LoopEnv S D B n s₀ := by
    refine ⟨by rw [up₀]; exact h.rd, by rw [up₀]; exact h.wr, h.keyData, h.keyBuf, h.dataBuf, fit,
      g₀ _ (by decide), g₀ _ (by decide), o₀, x₀, l₀⟩
  apply WP.seq
  let s₁ := arithFlags s₀ (s₀.gpr .rdx &&& s₀.gpr .rdx) false false
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_test, runStep_some, runBlock_nil], ?_⟩
  obtain g₁ : s₁.gpr = s₀.gpr := by simp only [s₁, gpr_arithFlags]
  obtain I0 : EInv S D B n up s₀ 0 s₁ := by
    refine ⟨by omega_arith, ?_, ?_, ?_, ?_, fun g _ _ _ _ _ _ _ => by rw [g₁], fun d _ => rfl,
      fun b hb => by omega_arith, fun b _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
    · rw [g₁, g₀ _ (by decide)]; simp [wAt, D]
    · rw [g₁, g₀ _ (by decide)]; simp [n]
    · rw [g₁, g₀ _ (by decide)]
    · rw [g₁, g₀ _ (by decide)]
  obtain fin : ∀ u, EInv S D B n up s₀ n u → EcbPost up s u := fun u I => by
    refine ⟨fun b hb => ?_, fun g h1 h2 h3 h4 h5 h6 h7 => ?_, ?_⟩
    · rw [I.done b hb, m₀]
    · rw [I.gpr _ h1 h2 h3 h4 h5 h6 h7, g₀ _ h3]
    · rw [← m₀]; exact I.frame
  obtain zf₁ : s₁.zf = some (s.gpr .rdx == 0) := by
    simp only [s₁, zf_arithFlags, g₀ _ (show Reg.rdx ≠ .r11 by decide), BitVec.and_self]
  apply WP.ite (s.gpr .rdx == 0) zf₁
  · intro hz
    obtain hn : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    apply WP.block_nil
    exact fin s₁ (hn ▸ I0)
  · intro hz
    obtain hn : 0 < n := by
      have : s.gpr .rdx ≠ 0 := by simpa using hz
      have : (s.gpr .rdx).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega_arith
    refine WP.mono (WP.loop (M := isa) (Q := EInv S D B n up s₀ n)
      (fun m u => ∃ k, k < n ∧ m = n - k ∧ EInv S D B n up s₀ k u) ?_ n s₁ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step L hk I) fun u' ⟨I', zu⟩ => ?_
    obtain ev : isa.eval .ne u' = some (!(BitVec.ofNat 64 (n - (k + 1)) == 0)) := by
      show u'.zf.map (!·) = _; rw [zu]; rfl
    by_cases e : k + 1 = n
    · left
      refine ⟨by rw [ev, e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      obtain nz : BitVec.ofNat 64 (n - (k + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
      exact ⟨by rw [ev, show (BitVec.ofNat 64 (n - (k + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
        n - (k + 1), by omega_arith, k + 1, by omega_arith, rfl, I'⟩

end VG.Proof.Blowfish.X86_64
