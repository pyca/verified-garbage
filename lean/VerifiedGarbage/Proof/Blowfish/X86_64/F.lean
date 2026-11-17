module

import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Blowfish.X86_64.Scan
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Rc2.X86_64.Lookup
import VerifiedGarbage.Proof.Framework.AddrArith

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
