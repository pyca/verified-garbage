module

public import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Gcm.AArch64.Lit
public import VerifiedGarbage.Proof.Gcm.Holes
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
meta import VerifiedGarbage.Proof.Gcm.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

-- separate module: the proof of one function, with the algebra of `Proof/Gcm/Holes.lean`, apart from the contracts and lemmas of `Ghash.lean`, which the proofs of seven others import

/-!
# GHASH on AArch64 meets its contract

Untrusted: everything here is checked by Lean. What the blocks of
`Impl/Gcm/AArch64.lean` compute, as the functions of `Proof/Gcm/Holes.lean`:
a 32-bit product (`holes_ok`), a 64-bit one (`pm_ok`) and a block's
(`mulCode_ok`, which is SP 800-38D's by `Holes.mulK_eq`). Then the blocks
(`body_ok`) and the function: the registers saved, the key and the masks
(`setup_ok`), the blocks and the registers restored (`ghash_correct`), and
that it is constant time (`ghash_ct`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Gcm.AArch64 VG.Proof.Gcm
open VG.Proof.Gcm.Holes (holes pm)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-- Runs a block of the instructions the code uses. -/
macro "hrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| plain_simp_names (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.AArch64.addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    mov, List.cons_append, List.nil_append, reduceCtorEq, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    and_true, true_and, BitVec.add_zero, $ts,*]) <;> try rfl)

/-- `s'` differs from `s` only in the registers `rs`. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) : Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-! ## A 32-bit product -/

/-- The masks are in their registers. -/
def Masks (s : State) : Prop := ∀ i < 4, s.gpr (K i) = Holes.K i

/-- The registers `holesCode` writes. -/
def holesRegs : List Reg := [.x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, B, T]

theorem holes_ok (s : State) (hK : Masks s) :
    WP isa (.block holesCode) s fun t =>
      t.gpr (Z 0) = holes (s.gpr T) (fun j => s.gpr HB &&& Holes.K j) ∧ Keep holesRegs s t := by
  obtain ⟨k0, k1, k2, k3⟩ : s.gpr .x13 = Holes.K 0 ∧ s.gpr .x14 = Holes.K 1 ∧ s.gpr .x15 = Holes.K 2 ∧
    s.gpr .x16 = Holes.K 3 := ⟨hK 0 (by decide), hK 1 (by decide), hK 2 (by decide), hK 3 (by decide)⟩
  rw [show holesCode = ([
      .logic .and .x .x17 .x12 .x13, .logic .and .x .x19 .x12 .x14, .logic .and .x .x20 .x12 .x15,
      .logic .and .x .x21 .x12 .x16,
      .logic .and .x .x11 .x26 .x13,
      .mul .x .x22 .x17 .x11, .mul .x .x23 .x19 .x11, .mul .x .x24 .x20 .x11, .mul .x .x25 .x21 .x11,
      .logic .and .x .x11 .x26 .x14,
      .mul .x .x12 .x17 .x11, .logic .eor .x .x23 .x23 .x12,
      .mul .x .x12 .x19 .x11, .logic .eor .x .x24 .x24 .x12,
      .mul .x .x12 .x20 .x11, .logic .eor .x .x25 .x25 .x12,
      .mul .x .x12 .x21 .x11, .logic .eor .x .x22 .x22 .x12,
      .logic .and .x .x11 .x26 .x15,
      .mul .x .x12 .x17 .x11, .logic .eor .x .x24 .x24 .x12,
      .mul .x .x12 .x19 .x11, .logic .eor .x .x25 .x25 .x12,
      .mul .x .x12 .x20 .x11, .logic .eor .x .x22 .x22 .x12,
      .mul .x .x12 .x21 .x11, .logic .eor .x .x23 .x23 .x12,
      .logic .and .x .x11 .x26 .x16,
      .mul .x .x12 .x17 .x11, .logic .eor .x .x25 .x25 .x12,
      .mul .x .x12 .x19 .x11, .logic .eor .x .x22 .x22 .x12,
      .mul .x .x12 .x20 .x11, .logic .eor .x .x23 .x23 .x12,
      .mul .x .x12 .x21 .x11, .logic .eor .x .x24 .x24 .x12,
      .logic .and .x .x22 .x22 .x13, .logic .and .x .x23 .x23 .x14, .logic .and .x .x24 .x24 .x15,
      .logic .and .x .x25 .x25 .x16,
      .logic .orr .x .x22 .x22 .x23, .logic .orr .x .x22 .x22 .x24,
      .logic .orr .x .x22 .x22 .x25] : List Instr) from rfl]
  apply WP.of_runBlock
  refine ⟨_, by hrun [], ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [Z, T, HB, holes, Holes.zc, gpr_write, ↓reduceIte, k0, k1, k2, k3,
      Nat.reduceAdd, Nat.reduceMod, BitVec.setWidth_eq]
  · simp only [holesRegs, B, T, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp only [gpr_write, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false]

theorem Keep.masks {rs : List Reg} {s t : State} (h : Keep rs s t) (hm : Masks s)
    (hr : ∀ i < 4, K i ∉ rs) : Masks t :=
  fun i hi => by rw [h.gpr (hr i hi)]; exact hm i hi

theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (h : r ∉ l') (hs : l ⊆ l') : r ∉ l :=
  fun hm => h (hs hm)

/-! ## A 64-bit product -/

/-- The registers `pmCode` writes, besides its results. -/
def pmTmp : List Reg := HB :: holesRegs

/-- The masks' registers. -/
def maskRegs : List Reg := [.x13, .x14, .x15, .x16]

theorem K_mem (i : Nat) : K i ∈ maskRegs := by
  unfold K maskRegs; split <;> simp

/-- The registers of a product: its factors are not among those it writes,
and its results neither among them, nor the masks, nor its factors. -/
structure PmRegs (X Y OL OH : Reg) : Prop where
  x : X ∉ pmTmp
  y : Y ∉ pmTmp
  l : OL ∉ pmTmp ++ maskRegs
  h : OH ∉ pmTmp ++ maskRegs
  xl : X ≠ OL
  xh : X ≠ OH
  yl : Y ≠ OL
  yh : Y ≠ OH
  lh : OL ≠ OH

def pmG1 (X Y : Reg) : List Instr := lo32 T X ++ lo32 HB Y
def pmG2 (X Y OL : Reg) : List Instr := [mov OL (Z 0), .lsr .x T X 32, .lsr .x HB Y 32]
def pmG3 (X Y OH : Reg) : List Instr :=
  ([mov OH (Z 0)] : List Instr) ++ lo32 T X ++ ([.lsr .x B X 32, .logic .eor .x T T B] : List Instr) ++
  lo32 HB Y ++ ([.lsr .x B Y 32, .logic .eor .x HB HB B] : List Instr)
def pmG4 (OL OH : Reg) : List Instr :=
  [.logic .eor .x (Z 0) (Z 0) OL, .logic .eor .x (Z 0) (Z 0) OH,
   .lsl .x T (Z 0) 32, .logic .eor .x OL OL T, .lsr .x T (Z 0) 32, .logic .eor .x OH OH T]

theorem pmCode_eq (X Y OL OH : Reg) : pmCode X Y OL OH = pmG1 X Y ++ (holesCode ++ (pmG2 X Y OL ++
    (holesCode ++ (pmG3 X Y OH ++ (holesCode ++ pmG4 OL OH))))) := by
  simp only [pmCode, pmG1, pmG2, pmG3, pmG4, List.append_assoc, List.cons_append, List.nil_append]

theorem g1_ok (s : State) {X Y : Reg} (hy : Y ≠ .x12) :
    WP isa (.block (pmG1 X Y)) s fun t => t.gpr T = Holes.lo32 (s.gpr X) ∧
      t.gpr HB = Holes.lo32 (s.gpr Y) ∧ Keep [T, HB] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [pmG1, lo32, T, HB, hy], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [T, gpr_write, reduceCtorEq, ↓reduceIte, Holes.lo32, BitVec.setWidth_eq]
  · simp only [HB, gpr_write, ↓reduceIte, Holes.lo32, BitVec.setWidth_eq]
  · simp only [T, HB, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]

theorem g2_ok (s : State) {X Y OL : Reg} (hxl : X ≠ OL) (hyl : Y ≠ OL) (hy : Y ≠ .x12)
    (hl : OL ≠ .x12) (hl' : OL ≠ .x26) :
    WP isa (.block (pmG2 X Y OL)) s fun t => t.gpr OL = s.gpr (Z 0) ∧
      t.gpr T = Holes.hi32 (s.gpr X) ∧ t.gpr HB = Holes.hi32 (s.gpr Y) ∧ Keep [OL, T, HB] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [pmG2, T, HB, Z, hxl, hyl, hy], ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [Z, gpr_write, hl, hl', ↓reduceIte, BitVec.setWidth_eq]
  · simp only [T, gpr_write, reduceCtorEq, ↓reduceIte, Holes.hi32, BitVec.setWidth_eq]
  · simp only [HB, gpr_write, ↓reduceIte, Holes.hi32, BitVec.setWidth_eq]
  · simp only [T, HB, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem g3_ok (s : State) {X Y OH : Reg} (hxh : X ≠ OH) (hx : X ≠ .x12) (hyh : Y ≠ OH)
    (hy : Y ≠ .x12) (hy' : Y ≠ .x11) (hy'' : Y ≠ .x26) (hh : OH ≠ .x12) (hh' : OH ≠ .x11)
    (hh'' : OH ≠ .x26) :
    WP isa (.block (pmG3 X Y OH)) s fun t => t.gpr OH = s.gpr (Z 0) ∧
      t.gpr T = Holes.lo32 (s.gpr X) ^^^ Holes.hi32 (s.gpr X) ∧
      t.gpr HB = Holes.lo32 (s.gpr Y) ^^^ Holes.hi32 (s.gpr Y) ∧ Keep [OH, T, B, HB] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [pmG3, lo32, T, HB, B, Z, hxh, hx, hyh, hy, hy', hy''], ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [Z, gpr_write, hh, hh', hh'', ↓reduceIte, BitVec.setWidth_eq]
  · simp only [T, gpr_write, reduceCtorEq, ↓reduceIte, Holes.lo32, Holes.hi32, BitVec.setWidth_eq]
  · simp only [HB, gpr_write, ↓reduceIte, Holes.lo32, Holes.hi32, BitVec.setWidth_eq]
  · simp only [T, HB, B, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem g4_ok (s : State) {OL OH : Reg} (hlh : OL ≠ OH) (hl : OL ≠ .x12) (hl' : OL ≠ .x22)
    (hh : OH ≠ .x12) (hh' : OH ≠ .x22) :
    WP isa (.block (pmG4 OL OH)) s fun t =>
      t.gpr OL = s.gpr OL ^^^ ((s.gpr (Z 0) ^^^ s.gpr OL) ^^^ s.gpr OH) <<< 32 ∧
      t.gpr OH = s.gpr OH ^^^ ((s.gpr (Z 0) ^^^ s.gpr OL) ^^^ s.gpr OH) >>> 32 ∧
      Keep [OL, OH, Z 0, T] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [pmG4, T, Z, hlh, (Ne.symm hlh), hl, hl', hh, hh', (Ne.symm hl), (Ne.symm hl'),
    (Ne.symm hh), (Ne.symm hh')], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [Z, gpr_write, hlh, hl, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [Z, gpr_write, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [T, Z, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem Keep.step {W rs : List Reg} {s u v : State} (h : Keep W s u) (k : Keep rs u v) (hs : rs ⊆ W) :
    Keep W s v :=
  (h.trans k).mono fun _ hr => (List.mem_append.mp hr).elim id fun hr => hs hr

theorem pm_ok (s : State) {X Y OL OH : Reg} (hr : PmRegs X Y OL OH) (hK : Masks s) :
    WP isa (.block (pmCode X Y OL OH)) s fun t =>
      t.gpr OL = (pm (s.gpr X) (s.gpr Y)).1 ∧ t.gpr OH = (pm (s.gpr X) (s.gpr Y)).2 ∧
      Keep (OL :: OH :: pmTmp) s t := by
  have hx := hr.x; have hy := hr.y; have hl := hr.l; have hh := hr.h
  simp only [pmTmp, holesRegs, maskRegs, HB, B, T, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hx hy hl hh
  -- what the code writes
  have sW : pmTmp ⊆ OL :: OH :: pmTmp := fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have sA : [T, HB] ⊆ OL :: OH :: pmTmp := fun _ h => sW ((by decide : [T, HB] ⊆ pmTmp) h)
  have sB : holesRegs ⊆ OL :: OH :: pmTmp := fun _ h => sW ((by decide : holesRegs ⊆ pmTmp) h)
  have sC : [OL, T, HB] ⊆ OL :: OH :: pmTmp := List.cons_subset.mpr ⟨List.mem_cons_self, sA⟩
  have sD : [OH, T, B, HB] ⊆ OL :: OH :: pmTmp := List.cons_subset.mpr
    ⟨List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => sW ((by decide : [T, B, HB] ⊆ pmTmp) h)⟩
  have sE : [OL, OH, Z 0, T] ⊆ OL :: OH :: pmTmp := List.cons_subset.mpr ⟨List.mem_cons_self,
    List.cons_subset.mpr ⟨List.mem_cons_of_mem _ List.mem_cons_self,
      fun _ h => sW ((by decide : [Z 0, T] ⊆ pmTmp) h)⟩⟩
  -- and what it does not
  have hXW : X ∉ OL :: OH :: pmTmp :=
    List.not_mem_cons_of_ne_of_not_mem hr.xl (List.not_mem_cons_of_ne_of_not_mem hr.xh hr.x)
  have hYW : Y ∉ OL :: OH :: pmTmp :=
    List.not_mem_cons_of_ne_of_not_mem hr.yl (List.not_mem_cons_of_ne_of_not_mem hr.yh hr.y)
  have hKW : ∀ i < 4, K i ∉ OL :: OH :: pmTmp := fun i _ =>
    List.not_mem_cons_of_ne_of_not_mem (fun e => hr.l (e ▸ List.mem_append_right _ (K_mem i)))
      (List.not_mem_cons_of_ne_of_not_mem (fun e => hr.h (e ▸ List.mem_append_right _ (K_mem i)))
        ((by decide : ∀ r ∈ maskRegs, r ∉ pmTmp) _ (K_mem i)))
  have lA : OL ∉ holesRegs := not_mem_of_sub hr.l (by decide)
  have lB : OL ∉ [OH, T, B, HB] :=
    List.not_mem_cons_of_ne_of_not_mem hr.lh (not_mem_of_sub hr.l (by decide))
  have hA : OH ∉ holesRegs := not_mem_of_sub hr.h (by decide)
  rw [pmCode_eq]
  refine WP.block_append_iff.mpr (WP.mono (g1_ok s hy.2.2.2.2.2.2.2.2.2.2) fun u1 ⟨a1, b1, k1⟩ => ?_)
  have w1 : Keep (OL :: OH :: pmTmp) s u1 := k1.mono sA
  refine WP.block_append_iff.mpr (WP.mono (holes_ok u1 (w1.masks hK hKW)) fun u2 ⟨z2, k2⟩ => ?_)
  have w2 := w1.step k2 sB
  have l2 : u2.gpr (Z 0) = Holes.pmL (s.gpr X) (s.gpr Y) := by rw [z2, a1, b1]; rfl
  refine WP.block_append_iff.mpr (WP.mono (g2_ok u2 hr.xl hr.yl hy.2.2.2.2.2.2.2.2.2.2
    hl.2.2.2.2.2.2.2.2.2.2.1 hl.1) fun u3 ⟨l3, a3, b3, k3⟩ => ?_)
  have w3 := w2.step k3 sC
  refine WP.block_append_iff.mpr (WP.mono (holes_ok u3 (w3.masks hK hKW)) fun u4 ⟨z4, k4⟩ => ?_)
  have w4 := w3.step k4 sB
  have h4 : u4.gpr (Z 0) = Holes.pmH (s.gpr X) (s.gpr Y) := by
    rw [z4, a3, b3, w2.gpr hXW, w2.gpr hYW]; rfl
  refine WP.block_append_iff.mpr (WP.mono (g3_ok u4 hr.xh hx.2.2.2.2.2.2.2.2.2.2 hr.yh
    hy.2.2.2.2.2.2.2.2.2.2 hy.2.2.2.2.2.2.2.2.2.1 hy.1 hh.2.2.2.2.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2.2.2.1
    hh.1) fun u5 ⟨h5, a5, b5, k5⟩ => ?_)
  have w5 := w4.step k5 sD
  refine WP.block_append_iff.mpr (WP.mono (holes_ok u5 (w5.masks hK hKW)) fun u6 ⟨z6, k6⟩ => ?_)
  have w6 := w5.step k6 sB
  refine WP.mono (g4_ok u6 hr.lh hl.2.2.2.2.2.2.2.2.2.2.1 hl.2.2.2.2.2.1 hh.2.2.2.2.2.2.2.2.2.2.1
    hh.2.2.2.2.2.1) fun t ⟨e1, e2, k7⟩ => ?_
  have l6 : u6.gpr OL = Holes.pmL (s.gpr X) (s.gpr Y) := by
    rw [k6.gpr lA, k5.gpr lB, k4.gpr lA, l3, l2]
  have h6 : u6.gpr OH = Holes.pmH (s.gpr X) (s.gpr Y) := by rw [k6.gpr hA, h5, h4]
  have m6 : u6.gpr (Z 0) = holes (Holes.lo32 (s.gpr X) ^^^ Holes.hi32 (s.gpr X))
      (fun j => (Holes.lo32 (s.gpr Y) ^^^ Holes.hi32 (s.gpr Y)) &&& Holes.K j) := by
    rw [z6, a5, b5, w4.gpr hXW, w4.gpr hYW]
  refine ⟨?_, ?_, w6.step k7 sE⟩
  · rw [e1, l6, h6, m6]; rfl
  · rw [e2, l6, h6, m6]; rfl

/-! ## A block's product -/

/-- The halves of `H'` added, or apart again. -/
def xk : List Instr := [.logic .eor .x KW0 KW0 KW1]

theorem mulCode_eq : mulCode = pmCode Y0 KW0 L1 L2 ++ (pmCode Y1 KW1 H1 H2 ++ (xk ++
    (pmCode YX KW0 Y0 Y1 ++ (xk ++ tail)))) := by
  simp only [mulCode, xk, List.append_assoc]

theorem xk_ok (s : State) :
    WP isa (.block xk) s fun t => t.gpr KW0 = s.gpr KW0 ^^^ s.gpr KW1 ∧ Keep [KW0] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [xk, KW0, KW1], ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [KW0, KW1, gpr_write, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [KW0, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_write, hr, ite_false]

theorem tail_ok (s : State) :
    WP isa (.block (xk ++ tail)) s fun t =>
      t.gpr ZH ++ t.gpr ZL = Holes.reduce (s.gpr L2) (s.gpr L1 ^^^ (s.gpr Y1 ^^^ s.gpr L2 ^^^ s.gpr H2))
        ((s.gpr Y0 ^^^ s.gpr L1 ^^^ s.gpr H1) ^^^ s.gpr H2) (s.gpr H1) ∧
      t.gpr KW0 = s.gpr KW0 ^^^ s.gpr KW1 ∧ Keep [KW0, YX, B, T, ZH] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [xk, tail, KW0, KW1, YX, Y0, Y1, L1, L2, H1, H2, B, T, ZH, ZL], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [ZH, ZL, L1, L2, H1, H2, Y0, Y1, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq,
      Holes.reduce, Holes.foldLo, Holes.foldHi]
  · simp only [KW0, KW1, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [KW0, YX, B, T, ZH, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The registers `mulCode` writes. -/
def mulRegs : List Reg := [.x5, .x6, .x7, .x8, .x9, .x27, .x28, .x0] ++ pmTmp

theorem xor_xor_self (a b : BitVec 64) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem mulCode_ok (s : State) (hK : Masks s) (hyx : s.gpr YX = s.gpr Y0 ^^^ s.gpr Y1) :
    WP isa (.block mulCode) s fun t =>
      t.gpr ZH ++ t.gpr ZL = Holes.mulK (s.gpr Y0) (s.gpr Y1) (s.gpr KW0) (s.gpr KW1) ∧
      t.gpr KW0 = s.gpr KW0 ∧ Keep mulRegs s t := by
  have r1 : PmRegs Y0 KW0 L1 L2 := by constructor <;> decide
  have r2 : PmRegs Y1 KW1 H1 H2 := by constructor <;> decide
  have r3 : PmRegs YX KW0 Y0 Y1 := by constructor <;> decide
  have hm : ∀ i < 4, K i ∉ mulRegs := fun i _ => (by decide : ∀ r ∈ maskRegs, r ∉ mulRegs) _ (K_mem i)
  rw [mulCode_eq]
  refine WP.block_append_iff.mpr (WP.mono (pm_ok s r1 hK) fun u1 ⟨a1, b1, k1⟩ => ?_)
  have w1 : Keep mulRegs s u1 := k1.mono (by decide)
  refine WP.block_append_iff.mpr (WP.mono (pm_ok u1 r2 (w1.masks hK hm)) fun u2 ⟨a2, b2, k2⟩ => ?_)
  have w2 := w1.step k2 (by decide)
  refine WP.block_append_iff.mpr (WP.mono (xk_ok u2) fun u3 ⟨a3, k3⟩ => ?_)
  have w3 := w2.step k3 (by decide)
  refine WP.block_append_iff.mpr (WP.mono (pm_ok u3 r3 (w3.masks hK hm)) fun u4 ⟨a4, b4, k4⟩ => ?_)
  have w4 := w3.step k4 (by decide)
  refine WP.mono (tail_ok u4) fun t ⟨e, f, k5⟩ => ?_
  -- the halves of `H'`
  have q1 : u2.gpr KW1 = s.gpr KW1 := w2.gpr (by decide)
  have q0 : u2.gpr KW0 = s.gpr KW0 := by rw [k2.gpr (by decide), k1.gpr (by decide)]
  have q3 : u3.gpr KW0 = s.gpr KW0 ^^^ s.gpr KW1 := by rw [a3, q0, q1]
  have q4 : u4.gpr KW0 = s.gpr KW0 ^^^ s.gpr KW1 := by rw [k4.gpr (by decide), q3]
  have q4' : u4.gpr KW1 = s.gpr KW1 := w4.gpr (by decide)
  -- the three products
  have l1 : u4.gpr L1 = (pm (s.gpr Y0) (s.gpr KW0)).1 := by
    rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), a1]
  have l2 : u4.gpr L2 = (pm (s.gpr Y0) (s.gpr KW0)).2 := by
    rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), b1]
  have h1 : u4.gpr H1 = (pm (s.gpr Y1) (s.gpr KW1)).1 := by
    rw [k4.gpr (by decide), k3.gpr (by decide), a2, k1.gpr (by decide), k1.gpr (by decide)]
  have h2 : u4.gpr H2 = (pm (s.gpr Y1) (s.gpr KW1)).2 := by
    rw [k4.gpr (by decide), k3.gpr (by decide), b2, k1.gpr (by decide), k1.gpr (by decide)]
  have yx3 : u3.gpr YX = s.gpr Y0 ^^^ s.gpr Y1 := by
    rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hyx]
  refine ⟨?_, by rw [f, q4, q4', xor_xor_self], w4.step k5 (by decide)⟩
  rw [e, l1, l2, h1, h2, a4, b4, yx3, q3]
  rfl

/-! ## One block -/

theorem blockAt_rev' (m : Mem) (p : Addr) :
    rev64 (m.readW p 64) ++ rev64 (m.readW (p + BitVec.ofNat 64 8) 64) = blockAt m p := by
  have := blockAt_rev m p
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this

theorem load_ok (s : State)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8)
    (hd : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 d) 8) :
    WP isa (.block load) s fun t =>
      t.gpr Y0 ++ t.gpr Y1 = blockAt s.mem (s.gpr .x1) ^^^ blockAt s.mem (s.gpr .x2) ∧
      t.gpr YX = t.gpr Y0 ^^^ t.gpr Y1 ∧ Keep [Y0, Y1, YX, T] s t := by
  have y0 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8 := by
    have := hy 0 (by decide); rwa [show s.gpr .x1 + BitVec.ofNat 64 0 = s.gpr .x1 from BitVec.add_zero _] at this
  have d0 : InRegions (s.rd ++ s.wr) (s.gpr .x2) 8 := by
    have := hd 0 (by decide); rwa [show s.gpr .x2 + BitVec.ofNat 64 0 = s.gpr .x2 from BitVec.add_zero _] at this
  have y8 := hy 8 (by decide); have d8 := hd 8 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by hrun [load, Y0, Y1, YX, T, y0, y8, d0, d8], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [Y0, Y1, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
    rw [← blockAt_rev', ← blockAt_rev', BitVec.xor_append, read_8, read_8, read_8, read_8]
  · simp only [Y0, Y1, YX, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [Y0, Y1, YX, T, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem store_ok (s : State)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = storeMem s.mem (s.gpr .x1) (s.gpr ZH) (s.gpr ZL) ∧
      s'.gpr .x2 = s.gpr .x2 + 16 ∧ s'.gpr .x3 = s.gpr .x3 - 1 ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ ZH → r ≠ ZL → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have y0 : InRegions s.wr (s.gpr .x1) 8 := by
    have := hy 0 (by decide); rwa [show s.gpr .x1 + BitVec.ofNat 64 0 = s.gpr .x1 from BitVec.add_zero _] at this
  have y8 := hy 8 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by hrun [store, ZH, ZL, y0, y8], ?_⟩
  refine ⟨?_, ?_, ?_, fun r h2 h3 h7 h8 => ?_, rfl, rfl⟩
  · simp only [storeMem, ZH, ZL, mem_write, write_8, BitVec.add_zero]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]; rfl
  · simp only [gpr_write, ↓reduceIte, BitVec.setWidth_eq]; rfl
  · simp only [ZH, ZL] at h7 h8
    simp only [gpr_write, h2, h3, h7, h8, ite_false]

theorem storeMem_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hr : (⟨p, 16⟩ : Region) ∈ rs) (zh zl : BitVec 64) : Frame rs m (storeMem m' p zh zl) :=
  (h.writeW hr _ (contains_offset (by decide) (by decide))).writeW hr _
    (contains_offset (by decide) (by decide))

/-- A block apart from what was written. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : blockAt m' p = blockAt m p :=
  blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

/-! ## The key and the masks -/

/-- The registers `setup` writes. -/
def setupRegs : List Reg := [KW0, KW1, T, B, .x13, .x14, .x15, .x16]

theorem setup_ok (s : State)
    (hh : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8) :
    WP isa (.block setup) s fun t =>
      t.gpr KW0 = Holes.key0 (rev64 (s.mem.readW (s.gpr .x0) 64))
        (rev64 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 8) 64)) ∧
      t.gpr KW1 = Holes.key1 (rev64 (s.mem.readW (s.gpr .x0) 64))
        (rev64 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 8) 64)) ∧
      Masks t ∧ Keep setupRegs s t := by
  have h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 8 := by
    have := hh 0 (by decide); rwa [show s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 from BitVec.add_zero _] at this
  have h8 := hh 8 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by hrun [setup, KW0, KW1, T, B, K, h0, h8], ?_⟩
  refine ⟨?_, ?_, fun i hi => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [KW0, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq, Holes.key0, read_8]
    rw [show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide,
      show BitVec.setWidth 64 (0xc200 : BitVec 16) <<< 48 = Impl.Gcm.Clmul.poly by decide]
  · simp only [KW1, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq, Holes.key1, read_8]
    rw [show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide,
      show BitVec.setWidth 64 (1 : BitVec 16) <<< 0 = 1#64 by decide]
  · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    all_goals simp only [K, Holes.K, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
    all_goals decide
  · simp only [setupRegs, KW0, KW1, T, B, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-! ## The loop invariant -/

section
variable (s₀ : State)

/-- The halves of `H`. -/
abbrev hw0 : BitVec 64 := rev64 (s₀.mem.readW (hA s₀) 64)
abbrev hw1 : BitVec 64 := rev64 (s₀.mem.readW (hA s₀ + BitVec.ofNat 64 8) 64)

end

theorem Pre.in_scr {s₀ : State} (h : Pre s₀) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega_using [hd])⟩

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x1 : s.gpr .x1 = yp s₀
  x4 : s.gpr .x4 = scr s₀
  x30 : s.gpr .x30 = s₀.gpr .x30
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  masks : Masks s
  k0 : s.gpr KW0 = Holes.key0 (hw0 s₀) (hw1 s₀)
  k1 : s.gpr KW1 = Holes.key1 (hw0 s₀) (hw1 s₀)
  frame : Frame [yR s₀, scrR s₀] s₀.mem s.mem
  slots : Spill.Saved (scr s₀) s₀.gpr saved s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x2 : s.gpr .x2 = blkAddr s₀ i
  x3 : s.gpr .x3 = BitVec.ofNat 64 (nb s₀ - i)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa (.block body) s fun s' =>
      (eval (.nonzero .x .x3) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x3) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  rw [body, List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (load_ok s
    (fun d hd => by rw [hL.rd, hL.wr, hL.x1]; exact hp.in_y hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.x2]; exact hp.in_blk hi hd)) fun u1 ⟨a1, b1, k1⟩ => ?_)
  have m1 : Masks u1 := k1.masks hL.masks fun j _ =>
    (by decide : ∀ r ∈ maskRegs, r ∉ [Y0, Y1, YX, T]) _ (K_mem j)
  refine WP.block_append_iff.mpr (WP.mono (mulCode_ok u1 m1 b1) fun u2 ⟨z2, q2, k2⟩ => ?_)
  have hx1₂ : u2.gpr .x1 = yp s₀ := by rw [k2.gpr (by decide), k1.gpr (by decide), hL.x1]
  have hm₂ : u2.mem = s.mem := k2.2.1.trans k1.2.1
  refine WP.mono (store_ok u2 fun d hd => by rw [k2.2.2.2, k1.2.2.2, hL.wr, hx1₂]; exact hp.out_y hd)
    fun s₃ ⟨hm₃, hx2₃, hx3₃, hk₃, hrd₃, hwr₃⟩ => ?_
  -- the registers that are neither loaded, nor multiplied, nor stored
  have keep : ∀ r, r ∉ [Y0, Y1, YX, T] → r ∉ mulRegs → r ≠ .x2 → r ≠ .x3 → s₃.gpr r = s.gpr r :=
    fun r hr hr' h2 h3 => by
      rw [hk₃ r h2 h3 (fun e => hr' (e ▸ by decide)) (fun e => hr' (e ▸ by decide)), k2.gpr hr',
        k1.gpr hr]
  have hx3 : u2.gpr .x3 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [k2.gpr (by decide), k1.gpr (by decide), hL.x3, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  have hblk : blockAt s.mem (blkAddr s₀ i) = blockAt s₀.mem (blkAddr s₀ i) :=
    blockAt_frame hL.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.y_d.symm.sub_left (hp.blk_sub hi)
      · exact hp.d_scr.sub_left (hp.blk_sub hi)
  have hy : blockAt s₃.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    rw [hm₃, hx1₂, blockAt_storeMem, z2, ghashFrom_blocksAt_succ, ← hL.y, k1.gpr (r := KW0) (by decide),
      k1.gpr (r := KW1) (by decide), hL.k0, hL.k1, Holes.mulK_eq, a1, hL.x1, hL.x2, hblk, blockAt_rev']
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.x1],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.x4],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.x30],
      by rw [hrd₃, k2.2.2.1, k1.2.2.1, hL.rd], by rw [hwr₃, k2.2.2.2, k1.2.2.2, hL.wr],
      fun j hj => ?_, ?_, by rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.k1],
      ?_, ?_, hy⟩
    · have := (by decide : ∀ r ∈ maskRegs, r ∉ [Y0, Y1, YX, T] ∧ r ∉ mulRegs ∧ r ≠ .x2 ∧ r ≠ .x3) _
        (K_mem j)
      rw [keep _ this.1 this.2.1 this.2.2.1 this.2.2.2]; exact hL.masks j hj
    · rw [hk₃ _ (by decide) (by decide) (by decide) (by decide), q2, k1.gpr (by decide), hL.k0]
    · rw [hm₃, hx1₂, hm₂]; exact storeMem_frame hL.frame List.mem_cons_self _ _
    · refine hL.slots.frame_in (lo := 0) (n := 256) (by decide)
        (rs := [yR s₀]) ?_ fun r hr => ?_
      · rw [hm₃, hx1₂, hm₂]; exact storeMem_frame (Frame.refl _ _) List.mem_cons_self _ _
      · rw [List.mem_singleton] at hr; subst hr
        rw [show scr s₀ + BitVec.ofNat 64 0 = scr s₀ from BitVec.add_zero _]
        exact hp.y_scr.symm
  have hev : eval (.nonzero .x .x3) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx3₃, hx3]
  by_cases hlast : i + 1 = nb s₀
  · left
    rw [hlast, Nat.sub_self] at hev
    exact ⟨hev.trans (by decide), hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    refine ⟨?_, by omega_using [hi, hlast], { hcommon with x2 := ?_, x3 := ?_ }⟩
    · have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])] at h'
        exact hne h'
      exact hev.trans (by simpa using h0)
    · rw [hx2₃, k2.gpr (by decide), k1.gpr (by decide), hL.x2, blkAddr, blkAddr,
        show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, Nat.mul_succ]
    · rw [hx3₃, hx3]

/-! ## The whole function -/

theorem ghash_wp {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hev : eval (.zero .x .x3) s₀ = some (s₀.gpr .x3 == 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.ite (s₀.gpr .x3 == 0) hev (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    refine WP.block_nil (M := isa) ⟨fun _ _ => rfl, ?_⟩
    show blockAt s₀.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    rw [h0]; rfl
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    -- the registers saved, the key and the masks
    have fS : Frame [scrR s₀] s₀.mem (Spill.saveMem s₀.mem (scr s₀) s₀.gpr saved) :=
      Spill.saveMem_frame_base (by decide) (by decide) _ _ _
    have hscr : ∀ r ∈ [scrR s₀], (hR s₀).Disjoint r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.h_scr
    refine WP.seq ?_
    rw [show save = Spill.saveCode .x4 saved from rfl]
    refine Spill.save_ok (by decide) (fun p hp' => hp.in_scr
      (by have := (by decide : ∀ p ∈ saved, p.2 + 8 ≤ 80) p hp'; omega_using [this])) ?_
    refine WP.mono (setup_ok _ fun d hd => hp.in_h hd) fun s₁ ⟨e0, e1, mk, k⟩ => ?_
    have hL₀ : LInv s₀ 0 s₁ := by
      refine ⟨⟨k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), k.2.2.1, k.2.2.2, mk, ?_, ?_,
        ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [e0]
        exact congrArg₂ Holes.key0
          (congrArg rev64 (fS.readW (r := hR s₀) (by simp [Region.Contains]) hscr (by decide)))
          (congrArg rev64 (fS.readW (r := hR s₀) (contains_offset (by decide) (by decide)) hscr
            (by decide)))
      · rw [e1]
        exact congrArg₂ Holes.key1
          (congrArg rev64 (fS.readW (r := hR s₀) (by simp [Region.Contains]) hscr (by decide)))
          (congrArg rev64 (fS.readW (r := hR s₀) (contains_offset (by decide) (by decide)) hscr
            (by decide)))
      · rw [k.2.1]; exact fS.mono (by simp)
      · rw [k.2.1]; exact Spill.saveMem_saved (by decide) _ _ _
      · rw [k.2.1]
        exact blockAt_frame fS fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact hp.y_scr
      · rw [k.gpr (by decide)]; simp [blkAddr]
      · rw [k.gpr (by decide)]; simp [nb]
    -- the blocks
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa (.block body) s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩)
      fun s₂ hc => ?_)
    -- the registers restored
    rw [show restore = Spill.restoreCode .x4 saved from rfl]
    refine WP.mono (Spill.restore_wp hc.x4 (by decide) (by decide) (fun p hp' => ?_) hc.slots)
      fun s' hR => ⟨fun r hr => ?_, ?_⟩
    · rw [hc.rd, hc.wr]
      exact ⟨scrR s₀, by simp [hp.wr], contains_offset
        (by have := (by decide : ∀ p ∈ saved, p.2 + 8 ≤ 80) p hp'; omega_using [this])
        (by have := (by decide : ∀ p ∈ saved, p.2 + 8 ≤ 80) p hp'; omega_using [this])⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact hR.gpr_of (.inl (by decide))
        | exact hR.gpr_of (.inr hc.x30)
    · show blockAt s'.mem (yp s₀) = _
      rw [hR.mem]; exact hc.y

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := ghash_wp (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub
    Impl.Gcm.AArch64.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Gcm.AArch64
