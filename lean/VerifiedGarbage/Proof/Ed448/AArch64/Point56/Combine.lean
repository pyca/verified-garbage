module

public import VerifiedGarbage.Proof.X448.AArch64.Base.Step
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Curve448.AArch64
public import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Impl.Ed448.AArch64.Point56
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.X448.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.AsFn
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.AsFn
meta import VerifiedGarbage.Proof.X448.AArch64.Base.Step
meta import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
meta import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
meta import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
meta import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
public import VerifiedGarbage.Proof.Ed448.Group.Projective
meta import VerifiedGarbage.Proof.Ed448.Group.Projective
public import VerifiedGarbage.Proof.X448.AArch64.Base.Comb
meta import VerifiedGarbage.Proof.X448.AArch64.Base.Comb
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
meta import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Iter
meta import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
meta import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
meta import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
meta import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Value
meta import VerifiedGarbage.Proof.Curve448.AArch64.Stage
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.AArch64.BitWrite
meta import VerifiedGarbage.Proof.X448.AArch64.Bits
meta import VerifiedGarbage.Proof.X448.AArch64.Carry
meta import VerifiedGarbage.Proof.X448.AArch64.Copy
meta import VerifiedGarbage.Proof.X448.AArch64.Setup
meta import VerifiedGarbage.Proof.X448.AArch64.Finish
meta import VerifiedGarbage.Proof.X448.AArch64.Initial
meta import VerifiedGarbage.Proof.X448.AArch64.Iter
meta import VerifiedGarbage.Proof.X448.AArch64.Step
meta import VerifiedGarbage.Proof.X448.AArch64.Weak.Iter
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
meta import VerifiedGarbage.Proof.X448.Wide.Fold
meta import VerifiedGarbage.Proof.X448.Wide.Pack
meta import VerifiedGarbage.Proof.X448.Wide.Pass
meta import VerifiedGarbage.Proof.X448.Wide.Term
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Impl.X448.AArch64.Base
meta import VerifiedGarbage.Proof.X448.Limbs
meta import VerifiedGarbage.Proof.X448.AArch64.Swap
meta import VerifiedGarbage.Impl.X448.AArch64
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.X448.AArch64.Mem
meta import Batteries.Logic
meta import VerifiedGarbage.Impl.X448.AArch64.Symmetric
meta import VerifiedGarbage.Proof.X448.Wide.CacheRegs
meta import VerifiedGarbage.Proof.X448.Wide.Product
meta import VerifiedGarbage.Proof.X448.Wide.Word
meta import VerifiedGarbage.Proof.X448.Wide.Column
meta import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.X448
meta import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.X448.AArch64.Base.Const

/-! ### `Ed448.AArch64.CombBase`, which the modules that import this one used -/

section

/-! ### `X448.AArch64.Base.Setup`, which this module and modules that import it used -/

section

/-!
# X448 of the base point on AArch64: the setup

Untrusted: everything here is checked by Lean. The setup points `x3` at the
working space, sets `x12`, saves the callee-saved registers and the output
pointer, zeroes every slot, expands the clamped scalar's bits, and starts both
accumulators at `[G] B` (`baseG`): `StepInv` for step 0.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 store_ok)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

open VG.Proof.X448.AArch64 (Saved)

/-- `x3 := x2` (the working space) and `x12 := 2²⁸ - 1`. -/
theorem regs_ok (s : State) :
    WP isa (.block ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x3 = s.gpr .x2 ∧ t.gpr .x12 = 0x0fffffff ∧ Keeps [.x3, .x12] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, by decide, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem word_store {m : Mem} {base : Addr} {d e : Nat} (hd : d + 8 ≤ 8192) (he : e + 8 ≤ 8192)
    (hdm : d % 8 = 0) (hem : e % 8 = 0) (v : BitVec 64) (hne : e ≠ d) :
    word (m.writeW (off base d) v) base e = word m base e := by
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ hd he hdm hem, ite_eq_right hne]

theorem word_store_self {m : Mem} {base : Addr} {d : Nat} (hd : d + 8 ≤ 8192) (hdm : d % 8 = 0)
    (v : BitVec 64) : word (m.writeW (off base d) v) base d = v := by
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ hd hd hdm hdm, ite_eq_left rfl]

theorem mov20_ok (s : State) :
    WP isa (.block [.addImm .x .x20 .x0 0]) s fun t =>
      t.gpr .x20 = s.gpr .x0 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The registers, the stores of `x19` and `x20`, the output pointer to `x20`, and the save of
`x21`–`x28`. -/
theorem prefix_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) ++ VG.Impl.X448.AArch64.Fast.save)) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      Keeps [.x3, .x12, .x20] s t ∧ Outside base 0 8192 s.mem t.mem := by
  rw [show ([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
      st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr) =
      [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ [.addImm .x .x20 .x0 0])) from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (regs_ok s) fun a ⟨a3, a12, ka, ma⟩ => ?_
  obtain ha : Scr a base := ⟨a3.trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  obtain hsb := ha.of_keeps kb (by decide)
  obtain b0 : word b.mem base 0 = s.gpr .x19 := by
    rw [mb, word_store_self (by decide) (by decide), ka.1 _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  obtain hsc := hsb.of_keeps kc (by decide)
  obtain c0 : word c.mem base 0 = s.gpr .x19 := by
    rw [mc, word_store (by decide) (by decide) (by decide) (by decide) _ (by decide), b0]
  obtain c8 : word c.mem base 8 = s.gpr .x20 := by
    rw [mc, word_store_self (by decide) (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (mov20_ok c) fun d ⟨d20, md, kd⟩ => ?_
  obtain hsd := hsc.of_keeps kd (by decide)
  refine WP.mono (save_ok hsd) fun t ⟨tx, tOut, tg, tr, tw⟩ => ?_
  obtain kad : Keeps [.x3, .x12, .x20] s d :=
    (((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans (kd.mono (by simp))
  obtain kt : Keeps [.x3, .x12, .x20] s t := ⟨fun r hr => (congrFun tg r).trans (kad.1 r hr), tr.trans kad.2.1,
    tw.trans kad.2.2⟩
  obtain od : Outside base 0 8192 s.mem d.mem := by
    obtain o1 : Outside base 0 8192 s.mem b.mem := by
      rw [mb, ← ma]; exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)).mono (by omega_arith) (by omega_arith)
    obtain o2 : Outside base 0 8192 b.mem c.mem := by
      rw [mc]; exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)).mono (by omega_arith) (by omega_arith)
    rw [md]; exact o1.trans o2
  refine ⟨hsd.of_keeps (rs := []) ⟨fun r _ => congrFun tg r, tr, tw⟩ (by decide), ⟨?_, ?_⟩, ?_, ?_, kt,
    od.trans (tOut.mono (by omega_arith) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega_arith))⟩
  · rw [tOut.word (Or.inl (by decide)) (by decide), md]; exact c0
  · rw [tOut.word (Or.inl (by decide)) (by decide), md]; exact c8
  · rw [congrFun tg .x20, d20, kc.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)]
  · intro k hk
    rw [tx k hk]
    have : VG.Impl.X448.AArch64.Fast.saved k ∉ [Reg.x3, .x12, .x20] := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega_arith)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact kad.1 _ this

/-- The setup's first block: `prefix`, then `v8`–`v15` saved and every slot zeroed. -/
theorem block1_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block VG.Impl.X448.AArch64.Base.entry) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .x20 = s.gpr .x0 ∧ SavedX base s.gpr t.mem ∧
      SavedV base s.v t.mem ∧ Keeps [.x3, .x12, .x4, .x20] s t ∧
      (∀ i < 352, limbs t.mem base (slot 0) i = 0) ∧ Outside base 0 8192 s.mem t.mem := by
  simp only [VG.Impl.X448.AArch64.Base.entry, List.append_assoc]
  rw [← List.append_assoc (([.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
        st .x19 0, st .x20 8, .addImm .x .x20 .x0 0] : List Instr)), WP.block_append_iff]
  refine WP.mono (WP.preservedV (prefix_ok hb hw hn) (by lit_decide)) fun a ⟨⟨ha, sa, oa, xa, ka, outa⟩, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vsave_ok ha) fun b ⟨vb, ob, gb, rb, wb⟩ => ?_
  obtain hsb : Scr b base := ha.of_keeps (rs := []) ⟨fun r _ => congrFun gb r, rb, wb⟩ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroX4_ok b) fun c ⟨c4, mc, kc⟩ => ?_
  obtain hsc : Scr c base := hsb.of_keeps kc (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.fill_ok hsc (o := slot 0) (n := 352) (by decide) (by decide) c4)
    fun t ⟨tz, tOut, kt⟩ => ?_
  obtain hst : Scr t base := hsc.of_keeps kt (by decide)
  obtain m : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 2880 ≤ d → d + 8 ≤ 8192 →
      d + 8 ≤ VG.Impl.X448.AArch64.Fast.VSAVE ∨ VG.Impl.X448.AArch64.Fast.VSAVE + 128 ≤ d →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by simp only [slot]; omega_arith) h2, mc, ob.word h3 h2]
  obtain hxs : ∀ k < 8, word t.mem base (Impl.X448.AArch64.Fast.SAVE + 8 * k) = s.gpr (Impl.X448.AArch64.Fast.saved k) :=
    fun k hk => by
      rw [m (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega_arith) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega_arith)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, Impl.X448.AArch64.Fast.VSAVE]; omega_arith)]
      exact xa k hk
  obtain vt : SavedV base a.v t.mem := by
    obtain vc : SavedV base a.v c.mem := by rw [mc]; exact vb
    exact vc.outside tOut (by simp only [slot, Impl.X448.AArch64.Fast.VSAVE]; omega_arith)
  refine ⟨hst, ⟨by rw [m (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [m (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kc.1 _ (by decide), congrFun gb .x20]; exact oa,
    hxs, fun k hk => ?_, ?_, tz, ?_⟩
  · rw [vt k hk]
    obtain hr : VG.Impl.Curve448.AArch64.Neon.V (8 + k) ∈ preservedV := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega_arith)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact va _ hr
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [kt.1 _ (by simp), kc.1 _ (by simpa using hr.2.2.1), congrFun gb r,
        ka.1 _ (by simp [hr.1, hr.2.1, hr.2.2.2])]
    · rw [kt.2.1, kc.2.1, rb, ka.2.1]
    · rw [kt.2.2, kc.2.2, wb, ka.2.2]
  · refine (outa.trans (ob.mono (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega_arith)
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega_arith))).trans ?_
    rw [← mc]; exact tOut.mono (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)

/-- The constant slots: both accumulators at the affine point `g`, and the counter at 0. -/
theorem consts_ok {s : State} {base : Addr} (hs : Scr s base) (g : Spec.X448.Fe × Spec.X448.Fe) :
    WP isa (.block (accs g)) s fun t =>
      (∀ w < 8, word t.mem base (AX + 8 * w) = limb g.1 w ∧
        word t.mem base (AY + 8 * w) = limb g.2 w ∧ word t.mem base (AZ + 8 * w) = limb 1 w ∧
        word t.mem base (BX + 8 * w) = limb g.1 w ∧
        word t.mem base (BY + 8 * w) = limb g.2 w ∧ word t.mem base (BZ + 8 * w) = limb 1 w) ∧
      Outside base 64 768 s.mem t.mem ∧ Keeps [.x4, .x19] s t ∧ t.gpr .x19 = 0 := by
  simp only [accs, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok hs (o := AX) (by decide) (by decide) _) fun t1 ⟨v1, o1, k1⟩ => ?_
  obtain h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h1 (o := AY) (by decide) (by decide) _) fun t2 ⟨v2, o2, k2⟩ => ?_
  obtain h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h2 (o := AZ) (by decide) (by decide) _) fun t3 ⟨v3, o3, k3⟩ => ?_
  obtain h3 := h2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h3 (o := BX) (by decide) (by decide) _) fun t4 ⟨v4, o4, k4⟩ => ?_
  obtain h4 := h3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h4 (o := BY) (by decide) (by decide) _) fun t5 ⟨v5, o5, k5⟩ => ?_
  obtain h5 := h4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h5 (o := BZ) (by decide) (by decide) _) fun t6 ⟨v6, o6, k6⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok t6 0 (by decide))
    fun t ⟨c, g, m, rd, wr⟩ => ⟨fun w hw => ?_, ?_, ?_, by rw [c]; rfl⟩
  · have hw8 : w < 8 := hw
    simp only [AX, AY, AZ, BX, BY, BZ, slot] at v1 v2 v3 v4 v5 v6 o1 o2 o3 o4 o5 o6 ⊢
    rw [m]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o6.word (by omega_arith) (by omega_arith), o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
        o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]; exact v1 w hw8
    · rw [o6.word (by omega_arith) (by omega_arith), o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
        o3.word (by omega_arith) (by omega_arith)]; exact v2 w hw8
    · rw [o6.word (by omega_arith) (by omega_arith), o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith)]
      exact v3 w hw8
    · rw [o6.word (by omega_arith) (by omega_arith), o5.word (by omega_arith) (by omega_arith)]; exact v4 w hw8
    · rw [o6.word (by omega_arith) (by omega_arith)]; exact v5 w hw8
    · exact v6 w hw8
  · simp only [AX, AY, AZ, BX, BY, BZ, slot] at o1 o2 o3 o4 o5 o6
    rw [m]
    exact (((((o1.mono (by omega_arith) (by omega_arith)).trans (o2.mono (by omega_arith) (by omega_arith))).trans
      (o3.mono (by omega_arith) (by omega_arith))).trans (o4.mono (by omega_arith) (by omega_arith))).trans
      (o5.mono (by omega_arith) (by omega_arith))).trans (o6.mono (by omega_arith) (by omega_arith))
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r hr.2, k6.1 r (by simp [hr.1]), k5.1 r (by simp [hr.1]), k4.1 r (by simp [hr.1]),
        k3.1 r (by simp [hr.1]), k2.1 r (by simp [hr.1]), k1.1 r (by simp [hr.1])]
    · rw [rd, k6.2.1, k5.2.1, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    · rw [wr, k6.2.2, k5.2.2, k4.2.2, k3.2.2, k2.2.2, k1.2.2]

open VG.Proof.Ed448 (Rep baseAff)
open VG.Proof.X448.AArch64 (bitRegs ofs)

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

/-- What the setup leaves, from the function's entry state `sE`. -/
structure Ready (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  pre : CombPre 56 base k t
  saved : Saved base sE.gpr t.mem
  out : t.gpr .x20 = sE.gpr .x0
  savedX : SavedX base sE.gpr t.mem
  savedV : SavedV base sE.v t.mem
  lr : t.gpr .x30 = sE.gpr .x30
  rd : t.rd = sE.rd
  wr : t.wr = sE.wr
  mem : Outside base 0 8192 sE.mem t.mem

theorem setup_ok {s : State} {base kp : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (hk : s.gpr .x1 = kp)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.AArch64.ofs base (kp + BitVec.ofNat 64 q))
    (htb : TblAt s base (s.syms combSym)) :
    WP isa VG.Impl.X448.AArch64.Base.setup s
      (Ready s base (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem kp 56))) := by
  unfold VG.Impl.X448.AArch64.Base.setup
  refine WP.seq (WP.mono_syms (block1_ok hb hw hn) fun a ⟨ha, sa, oa, xa, va, ka, za, outa⟩ sya => ?_)
  refine WP.mono_syms (bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun t ⟨gb, rdb, wrb, ob, bitsb⟩ syb => ?_
  obtain kb : Keeps bitRegs a t := ⟨gb, rdb, wrb⟩
  obtain hst : Scr t base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  obtain mt : Outside base 0 8192 s.mem t.mem := outa.trans (ob.mono (by omega_arith) (by simp only [BITS]; omega_arith))
  obtain htt : TblAt t base (t.syms combSym) := by
    rw [syb, sya]
    exact htb.of_far (by rw [kb.2.1, ka.2.1, kb.2.2, ka.2.2]) fun x hx => mt x (Or.inr hx)
  -- Every word outside the bits is as `block1` left it.
  obtain wt : ∀ {d : Nat}, d + 8 ≤ BITS ∨ BITS + 448 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h2 h3 => ob.word h2 h3
  -- The slots `block1` zeroed.
  obtain zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    obtain hz := za (16 * i.val + w) (by omega_arith)
    obtain e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega_arith
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  obtain zt : ∀ i : Index, ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    rw [wt (by simp only [slot, BITS]; omega_arith) (by simp only [slot]; omega_arith)]
    exact zs i w hw
  refine ⟨⟨hst, fun i w hw => ?_, fun w hw => ?_, fun q hq => ?_, htt⟩,
    ⟨by rw [wt (by decide) (by decide)]; exact sa.1,
      by rw [wt (by decide) (by decide)]; exact sa.2⟩,
    by rw [kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [wt (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega_arith)
        (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega_arith)]
      exact xa k hk,
    va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega_arith),
    by rw [kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kb.2.1, ka.2.1], by rw [kb.2.2, ka.2.2], mt⟩
  · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
    rw [zt i w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 w hw]; rfl
  · exact bitsb q hq

end VG.Proof.X448.AArch64.Base

end

end

/-!
# Ed448's fixed-base comb on AArch64, as a function

Untrusted: everything here is checked by Lean. One module, so that few others import the AdvSIMD
products' algebra (`ci/check_lean_speed.py`).

* `combBaseFn_ok`: `vg_ed448_r56_comb_base` (`combBaseFn`) saves `x21`–`x28` in the upper halves
  of `v8`–`v15`, those at `CSAVE` (`stqs_ok`), and `x19` and the return address at `XSAVE`; sets
  both accumulators at `[G] B` for `n` (`init_ok`), which takes `StepInv` to step 0; runs the `n`
  steps (`loop_ok`), with `n` in `x30`; and loads the registers back (`ldqs_ok`). The steps store
  only to the slots up to 18 and the products' bytes but `CSAVE` (`loopStores`,
  `WP.storeFrame`), so the saved registers survive them.
* `call_ok`: a call of it (`CombBase.call n`), from what the comb needs (`CombPre`) and `Frame`,
  keeps `Frame` and leaves the comb's sums, as the inlined comb does. The call runs on the working
  space and the tables (`WP.callV`, with the function's own proof as its contract, `combK`), and
  the return address is kept in a lane of `v8`, whose low half the function restores.
-/

@[expose] public section

/-! # The function -/

namespace VG.Proof.Ed448.AArch64.CombBase

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.CombBase
open VG.Impl.X448.AArch64 (slot ACC BITS st ld)
open VG.Impl.X448.AArch64.Base (combSym AX AY AZ BX BY BZ limb)
open VG.Impl.Curve448.AArch64.Neon (V ldq stq)
open VG.Proof.Curve448.AArch64.Neon (exec_ldq exec_stq off_add st_outside read16_write setMem setMem_mem
  V_ne)
open VG.Proof.X448.AArch64 (Scr Keeps off limbs word Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt StepInv Bits TblAt)
open VG.Proof.X448 (combG oddSumZ evenSumZ)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## The saves -/

theorem stqs_ok {s : State} {base : Addr} (hs : Scr s base) {O : Nat} (hO : O % 16 = 0) (hO' : O + 128 ≤ 8192) :
    WP isa (.block ((List.range 8).map fun k => stq (8 + k) (O + 16 * k))) s fun t =>
      (∀ k < 8, t.mem.read (off base (O + 16 * k)) 16 = s.v (V (8 + k))) ∧
      Outside base O 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  have e : ((List.range 8).map fun k => stq (8 + k) (O + 16 * k)) =
      (List.range 8).flatMap fun k => [stq (8 + k) (O + 16 * k)] := rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (O + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base O 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv
    (fun n t hn ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tvv, tr, tw, tsp⟩
  obtain ts : Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := O + 16 * n) (by omega_arith) (by omega_arith),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)),
      tg, tvv, tr, tw, tsp⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [((st_outside t.mem base (t.v (V (8 + n))) (d := O + 16 * n) (by omega_arith))).read16 (by omega_arith)
      (by omega_arith)]
    exact tv k (by omega_arith)

theorem ldqs_ok {s : State} {base : Addr} (hs : Scr s base) {O : Nat} (hO : O % 16 = 0) (hO' : O + 128 ≤ 8192) :
    WP isa (.block ((List.range 8).map fun k => ldq (8 + k) (O + 16 * k))) s fun t =>
      (∀ k < 8, t.v (V (8 + k)) = s.mem.read (off base (O + 16 * k)) 16) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e : ((List.range 8).map fun k => ldq (8 + k) (O + 16 * k)) =
      (List.range 8).flatMap fun k => [ldq (8 + k) (O + 16 * k)] := rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.v (V (8 + k)) = s.mem.read (off base (O + 16 * k)) 16) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, rfl⟩
  obtain ts : Scr t base := VG.Proof.Curve448.AArch64.Neon.scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := O + 16 * n) (by omega_arith) (by omega_arith),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw], by rw [RegUpd.sp_setV, tsp]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]
    exact tv k (by omega_arith)


/-- The lanes the function keeps `x21`–`x28` in. -/
abbrev cks : List (Reg × VReg × Nat) :=
  [(.x21, .v8, 1), (.x22, .v9, 1), (.x23, .v10, 1), (.x24, .v11, 1), (.x25, .v12, 1), (.x26, .v13, 1),
    (.x27, .v14, 1), (.x28, .v15, 1)]

theorem save_eq : save = ((([.addImm .x .x3 .x0 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] :
    List Instr) ++ insOf cks) ++ (List.range 8).map (fun k => stq (8 + k) (CSAVE + 16 * k))) ++
    (([st .x19 XSAVE] : List Instr) ++ (([st .x30 (XSAVE + 8)] : List Instr) ++
      ([.addImm .x .x30 .x1 0] : List Instr))) := rfl

theorem restore_eq : restore ++ ([ld .x19 XSAVE, ld .x30 (XSAVE + 8)] : List Instr) =
    ((List.range 8).map (fun k => ldq (8 + k) (CSAVE + 16 * k)) ++ umovOf cks) ++
      (([ld .x19 XSAVE] : List Instr) ++ ([ld .x30 (XSAVE + 8)] : List Instr)) := rfl

theorem preservedV_V : ∀ r ∈ preservedV, ∃ k < 8, r = V (8 + k) := by decide

/-- `x30 := x1`. -/
theorem mov30_ok (s : State) :
    WP isa (.block [.addImm .x .x30 .x1 0]) s fun t =>
      t.gpr .x30 = s.gpr .x1 ∧ t.mem = s.mem ∧ Keeps [.x30] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    BitVec.add_zero, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩

/-- `x9 = n - 56`: nonzero exactly for 57. -/
theorem sub56_ok (s : State) {n : Nat} (hn : n = 56 ∨ n = 57) (h : s.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x9 .x30 56]) s fun t =>
      (t.gpr .x9 != 0) = decide (n = 57) ∧ t.mem = s.mem ∧ Keeps [.x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (56 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, h,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩
  rcases hn with rfl | rfl <;> decide

theorem WP.ite_of {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop} {b : Bool}
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, _, Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, _, Exec.iteT hc e, q⟩

/-- `[G] B` for `n` tables. -/
def gOf (n : Nat) : Spec.X448.Fe × Spec.X448.Fe := if n = 57 then Impl.X448.baseG57 else Impl.X448.baseG

theorem gOf_ok {n : Nat} (hn : n = 56 ∨ n = 57) :
    Rep (VG.Proof.X448.basePt (gOf n)) (((combG n : ℤ) + 0) • baseAff) := by
  rcases hn with rfl | rfl
  · rw [show gOf 56 = Impl.X448.baseG from rfl, VG.Proof.X448.combG_56, add_zero, natCast_zsmul]
    exact VG.Proof.X448.baseG_ok
  · rw [show gOf 57 = Impl.X448.baseG57 from rfl, VG.Proof.X448.combG_57, add_zero, natCast_zsmul]
    exact VG.Proof.X448.baseG57_ok

/-- Both accumulators at `[G] B` for `n = x30`, and the counter at 0. -/
theorem init_ok {s : State} {base : Addr} {n : Nat} (hs : Scr s base) (hn : n = 56 ∨ n = 57)
    (h30 : s.gpr .x30 = BitVec.ofNat 64 n) :
    WP isa init s fun t =>
      (∀ w < 8, word t.mem base (AX + 8 * w) = limb (gOf n).1 w ∧
        word t.mem base (AY + 8 * w) = limb (gOf n).2 w ∧ word t.mem base (AZ + 8 * w) = limb 1 w ∧
        word t.mem base (BX + 8 * w) = limb (gOf n).1 w ∧
        word t.mem base (BY + 8 * w) = limb (gOf n).2 w ∧ word t.mem base (BZ + 8 * w) = limb 1 w) ∧
      Outside base 64 768 s.mem t.mem ∧ Keeps [.x9, .x4, .x19] s t ∧ t.gpr .x19 = 0 := by
  unfold init
  refine WP.seq (WP.mono (sub56_ok s hn h30) fun t1 ⟨z1, m1, k1⟩ => ?_)
  obtain hs1 := hs.of_keeps k1 (by decide)
  refine WP.ite_of (b := decide (n = 57)) (by simp only [eval, State.read, BitVec.setWidth_eq, z1]) ?_ ?_
  · intro hb
    obtain e : gOf n = Impl.X448.baseG57 := by simp only [decide_eq_true_eq] at hb; simp [gOf, hb]
    refine WP.mono (VG.Proof.X448.AArch64.Base.consts_ok hs1 _) fun t ⟨tv, tOut, kt, tc⟩ =>
      ⟨by rw [e]; exact tv, by rw [← m1]; exact tOut, (k1.then kt).mono (by decide), tc⟩
  · intro hb
    obtain e : gOf n = Impl.X448.baseG := by
      simp only [decide_eq_false_iff_not] at hb; simp [gOf, hb]
    refine WP.mono (VG.Proof.X448.AArch64.Base.consts_ok hs1 _) fun t ⟨tv, tOut, kt, tc⟩ =>
      ⟨by rw [e]; exact tv, by rw [← m1]; exact tOut, (k1.then kt).mono (by decide), tc⟩

/-! ## The steps' stores -/

/-- Where the accumulators' setting and the steps store: the slots up to 18, and the products'
bytes but `CSAVE`. -/
def loopOk (d : Nat) : Bool :=
  (64 ≤ d && d + 8 ≤ 2496) || (3584 ≤ d && d + 8 ≤ 3968) || (4096 ≤ d && d + 8 ≤ 4736)

theorem loopStores :
    ∀ i ∈ instrs (.seq init (.loop Impl.X448.AArch64.Base.stepR (.nonzero .x .x9)) : Prog isa),
      storesAt loopOk i = true := by
  rw [← List.all_eq_true, ← Code.allInstrs_eq]; lit_decide

/-- The bytes the function saves registers at are in no store of the steps. -/
theorem save_unstored (base : Addr) {i : Nat}
    (hi : CSAVE ≤ i ∧ i < CSAVE + 128 ∨ XSAVE ≤ i ∧ i < XSAVE + 16) :
    Unstored loopOk base (off base i) := by
  intro d hd hlt
  simp only [loopOk, CSAVE, XSAVE, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd hi
  rw [off, Offset.add_sub_add_left] at hlt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hlt
  omega_arith

theorem cks_V : ∀ k < 8, (cks.getD k (.x21, .v8, 1)).2.1 = V (8 + k) ∧
    (cks.getD k (.x21, .v8, 1)).1 = Impl.X448.AArch64.Fast.saved k ∧
    (cks.getD k (.x21, .v8, 1)).2.2 = 1 ∧ (cks.getD k (.x21, .v8, 1)) ∈ cks := by
  decide

/-! ## The function -/

/-- What the function needs: `ws` (`base`) in `x0`, `n` in `x1`, the working space writable, every
slot's limbs below `Ib`, slot 19 zero, the bits of `k` at `BITS`, and the tables. -/
structure CombIn (n : Nat) (base : Addr) (k : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = base
  x1 : s.gpr .x1 = BitVec.ofNat 64 n
  hn : n = 56 ∨ n = 57
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  bits : Bits n base k s.mem
  tbl : TblAt s base (s.syms combSym)

/-- What the saves leave. -/
structure Saved (n : Nat) (base : Addr) (s t : State) : Prop where
  scr : Scr t base
  x30 : t.gpr .x30 = BitVec.ofNat 64 n
  regs : ∀ r, r ≠ .x3 → r ≠ .x12 → r ≠ .x30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside2 base XSAVE 16 CSAVE 128 s.mem t.mem
  x19s : word t.mem base XSAVE = s.gpr .x19
  x30s : word t.mem base (XSAVE + 8) = s.gpr .x30
  lane1 : ∀ k < 8, (t.mem.read (off base (CSAVE + 16 * k)) 16).extractLsb' 64 64 =
    s.gpr (Impl.X448.AArch64.Fast.saved k)
  lane0 : ∀ k < 8, (t.mem.read (off base (CSAVE + 16 * k)) 16).extractLsb' 0 64 =
    (s.v (V (8 + k))).extractLsb' 0 64

theorem save_ok {n k : Nat} {base : Addr} {s : State} (h : CombIn n base k s) :
    WP isa (.block save) s (Saved n base s) := by
  have hnw := h.nowrap
  rw [save_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Point56.regs_ok s) fun s₀ ⟨g3, g12, gk, gm, gr, gw, gsp, gv⟩ => ?_
  refine WP.mono (insOf_ok cks s₀ (by decide) (by decide)) fun s₁ ⟨hg, hm, hr, hw, hsp, hls, hlo⟩ => ?_
  obtain hs₁ : Scr s₁ base := ⟨by rw [hg, g3, h.x0], by rw [hg, g12], by rw [hw, gw]; exact h.wr, hnw⟩
  refine WP.mono (stqs_ok hs₁ (O := CSAVE) (by decide) (by decide)) fun s₂ ⟨sv₂, o₂, g₂, v₂, r₂, w₂, sp₂⟩ => ?_
  obtain hs₂ : Scr s₂ base := VG.Proof.Curve448.AArch64.Neon.scr_of hs₁ g₂ w₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.store_ok hs₂ (d := XSAVE) (by decide) (by decide) .x19)
    fun s₃ ⟨m₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.store_ok hs₃ (d := XSAVE + 8) (by decide) (by decide) .x30)
    fun s₄ ⟨m₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (mov30_ok s₄) fun s₅ ⟨g20, m₅, k₅⟩ => ?_
  obtain gs : ∀ r, r ≠ .x3 → r ≠ .x12 → s₂.gpr r = s.gpr r := fun r h3 h12 => by rw [g₂, hg, gk r h3 h12]
  obtain g34 : ∀ r, s₄.gpr r = s₂.gpr r := fun r => by rw [k₄.1 r (by simp), k₃.1 r (by simp)]
  obtain w4 : ∀ x, (ofs base x < XSAVE ∨ XSAVE + 16 ≤ ofs base x) → s₄.mem x = s₂.mem x := fun x hx => by
    rw [m₄, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide) x (by simp only [XSAVE] at hx ⊢; omega_arith), m₃,
      VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide) x (by simp only [XSAVE] at hx ⊢; omega_arith)]
  obtain csv : ∀ k < 8, s₅.mem.read (off base (CSAVE + 16 * k)) 16 = s₁.v (V (8 + k)) := fun k hk => by
    rw [← sv₂ k hk, m₅]
    exact Mem.read_congr fun i hi => by
      rw [off_add]
      exact w4 _ (by
        rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [CSAVE]; omega_arith)]; simp only [CSAVE, XSAVE]; omega_arith)
  obtain x19w : word s₄.mem base XSAVE = s₂.gpr .x19 := by
    rw [m₄, VG.Proof.X448.AArch64.Base.word_store (d := XSAVE + 8) (e := XSAVE) (by decide) (by decide)
      (by decide) (by decide) _ (by decide), m₃, VG.Proof.X448.AArch64.Base.word_store_self (by decide) (by decide)]
  obtain x20w : word s₄.mem base (XSAVE + 8) = s₂.gpr .x30 := by
    rw [m₄, VG.Proof.X448.AArch64.Base.word_store_self (by decide) (by decide), k₃.1 _ (by simp)]
  refine ⟨hs₄.of_keeps k₅ (by decide), ?_, fun r h3 h12 h20 => ?_, ?_, ?_, fun x h1 h2 => ?_,
    by rw [m₅, x19w, gs _ (by decide) (by decide)], by rw [m₅, x20w, gs _ (by decide) (by decide)],
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [g20, g34, gs _ (by decide) (by decide), h.x1]
  · rw [k₅.1 r (by simpa using h20), g34, gs r h3 h12]
  · rw [k₅.2.1, k₄.2.1, k₃.2.1, r₂, hr, gr]
  · rw [k₅.2.2, k₄.2.2, k₃.2.2, w₂, hw, gw]
  · rw [m₅, w4 x h1, o₂ x h2, hm, gm]
  · obtain ⟨hv, hs', hl, hm'⟩ := cks_V k hk
    obtain n3 := (show ∀ k < 8, Impl.X448.AArch64.Fast.saved k ≠ .x3 ∧ Impl.X448.AArch64.Fast.saved k ≠ .x12 by
      decide) k hk
    rw [csv k hk, ← gk _ n3.1 n3.2, ← hs', ← hls _ hm']
    simp only [laneOf, hv, hl]
  · rw [csv k hk]
    obtain h0 := hlo (V (8 + k)) 0 (by decide) (by revert k; decide)
    simp only [laneOf, Nat.mul_zero] at h0
    rw [h0, gv]

/-- What the function leaves, from `s`: every register outside `x1` and `fclob` restored, and
`x21`–`x28`, but `x3` (`ws`) and `x12` (the mask), the low halves of `v8`–`v15`, and the comb's
sums, `[G + Σ_j d_{2j+1} 256^j] B` in slots 0–2 and `[G + Σ_j d_{2j} 256^j] B` in slots 3–5. -/
structure CombOut (n : Nat) (base : Addr) (k : Nat) (s u : State) : Prop where
  regs : ∀ r, (r ∉ .x1 :: fclob ∨ r ∈ cks.map Prod.fst) → r ≠ .x3 → r ≠ .x12 → u.gpr r = s.gpr r
  x3 : u.gpr .x3 = base
  mask : u.gpr .x12 = 0x0fffffff
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  env : BEnv u.mem base
  zero : ∀ w < 8, limbs u.mem base (slot (19 : Index).val) w = 0
  mem : Outside2 base 64 2816 ACC 1152 s.mem u.mem
  odd : Rep (pt (EV u.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k n) • baseAff)
  even : Rep (pt (EV u.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k n) • baseAff)

/-- **The comb, as a function**. -/
theorem combBaseFn_ok {n k : Nat} {base : Addr} {s : State} (h : CombIn n base k s) :
    WP isa combBaseFn s (CombOut n base k s) := by
  obtain hn57 : n ≤ 57 := by rcases h.hn with rfl | rfl <;> decide
  have hnw := h.nowrap
  unfold combBaseFn
  refine WP.seq (WP.mono_syms (save_ok h) fun s₅ hS sy5 => ?_)
  have hs₅ := hS.scr
  -- The memory after the saves.
  obtain wS : ∀ {d : Nat}, d + 8 ≤ XSAVE → word s₅.mem base d = word s.mem base d := fun hd =>
    hS.mem.word (Or.inl hd) (Or.inl (by simp only [XSAVE, CSAVE] at hd ⊢; omega_arith))
      (by simp only [XSAVE] at hd; omega_arith)
  obtain bS : BEnv s₅.mem base := fun i j hj => by
    have := i.isLt
    show (word s₅.mem base (slot i.val + 8 * j)).toNat < Ib
    rw [wS (by simp only [slot, XSAVE]; omega_arith)]; exact h.env i j hj
  obtain zS : ∀ w < 8, limbs s₅.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    show (word s₅.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [wS (by simp only [slot, XSAVE]; omega_arith)]; exact h.zero w hw
  obtain bitsS : Bits n base k s₅.mem := fun q hq => by
    obtain e := VG.Proof.X448.AArch64.Base.ofs_off0 base (d := BITS + q) (by simp only [BITS]; omega_arith)
    rw [hS.mem _ (by rw [e]; simp only [BITS, XSAVE]; omega_arith) (by rw [e]; simp only [BITS, CSAVE]; omega_arith)]
    exact h.bits q hq
  obtain tblS : TblAt s₅ base (s₅.syms combSym) := by
    rw [sy5]
    exact h.tbl.of_far (by rw [hS.rd, hS.wr]) fun x hx =>
      hS.mem x (.inr (by simp only [XSAVE]; omega_arith)) (.inr (by simp only [CSAVE]; omega_arith))
  -- The accumulators' setting and the steps, which keep the saved registers.
  refine WP.assoc ?_
  refine WP.seq (WP.mono (WP.storeFrame (Q := StepInv n s₅ base k n) loopStores (WP.seq (WP.mono_syms (init_ok hs₅ h.hn hS.x30)
    fun t ⟨tv, tOut, kt, tc⟩ syt => ?_))) fun tL ⟨hL, x3L, fL⟩ => ?_)
  · have hst : Scr t base := hs₅.of_keeps kt (by decide)
    obtain ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
        EV t.mem base i = v := fun i v hv => VG.Proof.X448.AArch64.Base.F_of_words hv
    obtain pA : pt (EV t.mem base) 0 1 2 = VG.Proof.X448.basePt (gOf n) := by
      simp only [pt, VG.Proof.X448.basePt]
      rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
    obtain pB : pt (EV t.mem base) 3 4 5 = VG.Proof.X448.basePt (gOf n) := by
      simp only [pt, VG.Proof.X448.basePt]
      rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
        ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
    obtain wt : ∀ (i : Index), 6 ≤ i.val → ∀ w < 8, word t.mem base (slot i.val + 8 * w) =
        word s₅.mem base (slot i.val + 8 * w) := fun i hi w hw => by
      have := i.isLt
      exact tOut.word (Or.inr (by simp only [slot]; omega_arith)) (by simp only [slot]; omega_arith)
    obtain inv : StepInv n s₅ base k 0 t := by
      refine ⟨Nat.zero_le _, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
        by rw [pA]; exact gOf_ok h.hn, by rw [pB]; exact gOf_ok h.hn, kt.1 _ (by decide), kt.1 _ (by decide),
        kt.2.1, kt.2.2, fun x h1 _ => tOut x (by omega_arith),
        tblS.of_far (by rw [kt.2.1, kt.2.2]) fun x hx => tOut x (.inr (by omega_arith)),
        fun r hr => kt.1 r (VG.Proof.X448.AArch64.Base.notin_keep (by decide) hr)⟩
      · by_cases hi : i.val < 6
        · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
            rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega_arith
          rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
          · exact VG.Proof.X448.AArch64.Base.bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
        · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
          rw [wt i (by omega_arith) w hw]; exact bS i w hw
      · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
        rw [wt 19 (by decide) w hw]; exact zS w hw
      · have e := VG.Proof.X448.AArch64.Base.ofs_off0 base (d := BITS + q) (by simp only [BITS]; omega_arith)
        rw [tOut _ (by rw [e]; simp only [BITS]; omega_arith)]
        exact bitsS q hq
    have := VG.Proof.X448.AArch64.Base.loop_ok hn57 hS.x30 n t (by rcases h.hn with rfl | rfl <;> decide)
      le_rfl (by rw [Nat.sub_self]; exact inv) (by rw [syt])
    exact this
  -- The registers loaded back.
  rw [hs₅.x3] at fL
  have hsL := hL.scr
  rw [restore_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldqs_ok hsL (O := CSAVE) (by decide) (by decide)) fun s₆ ⟨v₆, m₆, g₆, r₆, w₆, sp₆⟩ => ?_
  obtain hs₆ : Scr s₆ base := VG.Proof.Curve448.AArch64.Neon.scr_of hsL g₆ w₆
  refine WP.mono (WP.preservedV (umovOf_ok cks s₆ (by decide) (by decide)) (by lit_decide))
    fun s₇ ⟨⟨m₇, r₇, w₇, sp₇, l₇, o₇⟩, vv₇⟩ => ?_
  obtain hs₇ : Scr s₇ base := ⟨by rw [o₇ _ (by decide)]; exact hs₆.x3, by rw [o₇ _ (by decide)]; exact hs₆.mask,
    by rw [w₇]; exact hs₆.wr, hnw⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (VG.Proof.Curve448.AArch64.Fast.ld_ok hs₇ .x19 (d := XSAVE) (by decide)
    (by decide)) (by lit_decide)) fun s₈ ⟨⟨x8, m₈, k₈⟩, vv₈⟩ => ?_
  obtain hs₈ := hs₇.of_keeps k₈ (by decide)
  refine WP.mono (WP.preservedV (VG.Proof.Curve448.AArch64.Fast.ld_ok hs₈ .x30 (d := XSAVE + 8) (by decide)
    (by decide)) (by lit_decide)) fun u ⟨⟨xu, mu, ku⟩, vvu⟩ => ?_
  -- The saved bytes, as the saves left them.
  obtain mL : ∀ i, CSAVE ≤ i ∧ i < CSAVE + 128 ∨ XSAVE ≤ i ∧ i < XSAVE + 16 →
      tL.mem (off base i) = s₅.mem (off base i) := fun i hi => fL _ (save_unstored base hi)
  obtain rdL : ∀ k < 8, tL.mem.read (off base (CSAVE + 16 * k)) 16 = s₅.mem.read (off base (CSAVE + 16 * k)) 16 :=
    fun k hk => Mem.read_congr fun i hi => by
      rw [off_add]; exact mL _ (.inl (by simp only [CSAVE]; omega_arith))
  obtain wL : ∀ d, XSAVE ≤ d → d + 8 ≤ XSAVE + 16 → word tL.mem base d = word s₅.mem base d :=
    fun d h1 h2 => Mem.readW_congr fun i hi => by
      rw [off_add]; exact mL _ (.inr (by simp only [XSAVE] at h1 h2 ⊢; omega_arith))
  obtain mu' : u.mem = tL.mem := by rw [mu, m₈, m₇, m₆]
  obtain v6 : ∀ k < 8, s₆.v (V (8 + k)) = s₅.mem.read (off base (CSAVE + 16 * k)) 16 := fun k hk => by
    rw [v₆ k hk, rdL k hk]
  obtain gu : ∀ r, r ≠ .x19 → r ≠ .x30 → u.gpr r = s₇.gpr r := fun r h19 h20 => by
    rw [ku.1 r (by simpa using h20), k₈.1 r (by simpa using h19)]
  refine ⟨fun r hr h3 h12 => ?_, by rw [gu _ (by decide) (by decide), o₇ _ (by decide), g₆]; exact hsL.x3,
    by rw [gu _ (by decide) (by decide), o₇ _ (by decide), g₆]; exact hsL.mask,
    by rw [ku.2.1, k₈.2.1, r₇, r₆, hL.rd, hS.rd], by rw [ku.2.2, k₈.2.2, w₇, w₆, hL.wr, hS.wr],
    fun r hr => ?_, by rw [mu']; exact hL.env, by rw [mu']; exact hL.zero, fun x h1 h2 => ?_,
    by rw [mu']; exact hL.odd, by rw [mu']; exact hL.even⟩
  · by_cases e19 : r = .x19
    · subst e19
      rw [ku.1 _ (by decide), x8, m₇, m₆, wL _ le_rfl (by decide), hS.x19s]
    by_cases e20 : r = .x30
    · subst e20
      rw [xu, m₈, m₇, m₆, wL _ (by decide) le_rfl, hS.x30s]
    by_cases hk : r ∈ cks.map Prod.fst
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      obtain ⟨k, hk8, hkx⟩ : ∃ k < 8, cks.getD k (.x21, .v8, 1) = x := by
        revert x; decide
      obtain ⟨hv, hs', hl, -⟩ := cks_V k hk8
      rw [gu _ e19 e20, l₇ x hx, ← hkx, laneOf, hv, hl, v6 k hk8, hs']
      exact hS.lane1 k hk8
    · have hf : r ∉ .x1 :: fclob := hr.resolve_right hk
      rw [gu r e19 e20, o₇ r hk, g₆, hL.keep r (by simp only [List.mem_cons, not_or] at hf ⊢; exact ⟨hf.1, e19, hf.2⟩),
        hS.regs r h3 h12 e20]
  · obtain ⟨k, hk8, rfl⟩ := preservedV_V r hr
    rw [vvu _ hr, vv₈ _ hr, vv₇ _ hr, v6 k hk8]
    exact hS.lane0 k hk8
  · rw [mu', hL.mem x h1 h2]
    have hA : ACC = 3584 := rfl
    exact hS.mem x (by simp only [XSAVE]; omega_arith) (by simp only [CSAVE]; omega_arith)

end VG.Proof.Ed448.AArch64.CombBase

/-! # Calls -/

namespace VG.Proof.Ed448.AArch64.CombBase

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.CombBase
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (combSym)
open VG.Proof.X448.AArch64 (Scr Keeps limbs Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv fclob)
open VG.Proof.X448.AArch64.Base (pt Bits TblAt CombPre)
open VG.Proof.X448 (combG oddSumZ evenSumZ)
open VG.Proof.Ed448 (Rep baseAff)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "BFrame" => VG.Proof.X448.AArch64.Base.Frame

/-- The tables' bytes. -/
abbrev tblLen : Nat := 8 * (57 * 128)

/-- The function's proof, as the contract of a call on the working space at `base` and the tables
at `T`. -/
def combK (n : Nat) (base : Addr) (k : Nat) (T : Addr) : Contract isa where
  pre t := t.rd = [⟨T, tblLen⟩] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .x0 = base ∧
    t.gpr .x1 = BitVec.ofNat 64 n ∧ (n = 56 ∨ n = 57) ∧ base.toNat + 8192 ≤ 2 ^ 64 ∧ BEnv t.mem base ∧
    (∀ w < 8, limbs t.mem base (slot (19 : Index).val) w = 0) ∧ Bits n base k t.mem ∧
    TblAt t base T ∧ t.syms combSym = T
  post t u := CombOut n base k t u
  pub _ _ := True

theorem preserved_ok : ∀ r ∈ preserved, (r ∉ .x1 :: fclob ∨ r ∈ cks.map Prod.fst) ∧ r ≠ .x3 ∧ r ≠ .x12 := by
  decide

theorem combK_ok {n k : Nat} {base T : Addr} :
    ∀ s, (combK n base k T).pre s →
      ∃ t s', Exec isa combBaseFn s t s' ∧ abiPreserved s s' ∧ (combK n base k T).post s s' := by
  intro s ⟨_, hwr, h0, h1, hn, hnw, hb, hz, hbits, htbl, hsym⟩
  obtain hin : CombIn n base k s :=
    ⟨h0, h1, hn, by rw [hwr]; exact List.mem_singleton_self _, hnw, hb, hz, hbits, by rw [hsym]; exact htbl⟩
  obtain ⟨t, u, he, hout⟩ := combBaseFn_ok hin
  exact ⟨t, u, he, ⟨fun r hr => hout.regs r (preserved_ok r hr).1 (preserved_ok r hr).2.1 (preserved_ok r hr).2.2,
    Exec.sp he, hout.v⟩, hout⟩

theorem movz1_ok (s : State) {n : Nat} (hn : n = 56 ∨ n = 57) :
    WP isa (.block [.movz .x .x1 n 0]) s fun t => t.gpr .x1 = BitVec.ofNat 64 n ∧ t.mem = s.mem ∧
      Keeps [.x1] s t ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩
  rw [RegUpd.gpr_write_self]
  rcases hn with rfl | rfl <;> decide

/-- **A call of `vg_ed448_r56_comb_base`** for `n` tables: from `Frame` and what the comb needs,
`Frame` and the comb's sums. -/
theorem call_ok {n k : Nat} {s₀ s : State} {base : Addr} (hn : n = 56 ∨ n = 57) (hf : BFrame s₀ base s)
    (hp : CombPre n base k s) :
    WP isa (call n) s fun t => BFrame s₀ base t ∧
      Rep (pt (EV t.mem base) 0 1 2) (((combG n : ℤ) + oddSumZ k n) • baseAff) ∧
      Rep (pt (EV t.mem base) 3 4 5) (((combG n : ℤ) + evenSumZ k n) • baseAff) := by
  have hs := hf.scr
  have hnw := hs.nowrap
  unfold VG.Impl.Ed448.AArch64.CombBase.call
  rw [WP.seq_iff, show ([.vop (.ins .d2 .v8 0 .x30), .movz .x .x1 n 0] : List Instr) =
    insOf [(.x30, .v8, 0)] ++ ([.movz .x .x1 n 0] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono_syms (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide))
    fun t₁ ⟨g₁, m₁, r₁, w₁, sp₁, l₁, o₁⟩ sy₁ => ?_
  refine WP.mono_syms (movz1_ok t₁ hn) fun t₂ ⟨x1₂, m₂, k₂, v₂⟩ sy₂ => ?_
  unfold fnCall
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.of_runBlock ⟨t₂.write .x .x0 (t₂.gpr .x3 + BitVec.ofNat 64 0), ?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq]
  generalize ht₃ : t₂.write .x .x0 (t₂.gpr .x3 + BitVec.ofNat 64 0) = t₃
  obtain g₂ : ∀ r, r ≠ .x1 → t₂.gpr r = s.gpr r := fun r h => by rw [k₂.1 r (by simpa using h), g₁]
  obtain g0 : t₃.gpr .x0 = base := by
    rw [← ht₃, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, g₂ _ (by decide), hs.x3]
  obtain gk : ∀ r, r ≠ .x0 → t₃.gpr r = t₂.gpr r := fun r hr => by rw [← ht₃, RegUpd.gpr_write_of_ne _ _ _ hr]
  obtain m₃ : t₃.mem = s.mem := by rw [← ht₃]; exact m₂.trans m₁
  obtain r₃ : t₃.rd = s.rd := by rw [← ht₃]; exact k₂.2.1.trans r₁
  obtain w₃ : t₃.wr = s.wr := by rw [← ht₃]; exact k₂.2.2.trans w₁
  obtain v₃ : t₃.v = t₁.v := by rw [← ht₃, ← v₂]; rfl
  obtain sy₃ : t₃.syms = s.syms := by rw [← ht₃, ← sy₁, ← sy₂]; rfl
  obtain htb : TblAt t₃ base (s.syms combSym) :=
    hp.tbl.of_far (by rw [r₃, w₃]) fun x _ => by rw [m₃]
  obtain hcov : Covers ([⟨s.syms combSym, tblLen⟩] ++ [⟨base, 8192⟩]) (t₃.rd ++ t₃.wr) :=
    Covers.append_left (Covers.one htb.rd)
      (Covers.right (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, w₃]; exact hs.wr))
  obtain hcw : Covers [⟨base, 8192⟩] t₃.wr :=
    Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, w₃]; exact hs.wr
  refine WP.callV (k := combK n base k (s.syms combSym)) (rd := [⟨s.syms combSym, tblLen⟩])
    (wr := [⟨base, 8192⟩]) combK_ok ⟨rfl, rfl, ?_, ?_, hn, hnw, ?_, ?_, ?_, ?_, ?_⟩ hcov hcw ?_
  · rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0]
  · rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), gk _ (by decide), x1₂]
  · rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hp.env
  · rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hp.zero
  · rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hp.bits
  · exact ⟨⟨⟨s.syms combSym, tblLen⟩, List.mem_append_left _ (List.mem_singleton_self _), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, le_refl]⟩,
      htb.far, by rw [State.withRegions_mem, State.callEntry_mem]; exact htb.val⟩
  · show t₃.syms combSym = s.syms combSym
    rw [sy₃]
  intro t' hrd hwr hsp _ hpres _ hv hpost
  obtain hm : Outside2 base 64 2816 ACC 1152 s.mem t'.mem := by
    have := hpost.mem
    simp only [State.withRegions_mem, State.callEntry_mem, m₃] at this
    exact this
  refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t' (by decide) (by decide)) fun u ⟨um, ur, uw, usp, ul, uo⟩ => ?_
  obtain gu : ∀ r, r ≠ .x30 → u.gpr r = t'.gpr r := fun r h => uo r (by simpa using h)
  obtain l30 : u.gpr .x30 = s₀.gpr .x30 := by
    rw [ul _ List.mem_cons_self]
    show (t'.v .v8).extractLsb' (64 * 0) 64 = _
    rw [hv .v8 (by decide), v₃]
    exact (l₁ _ List.mem_cons_self).trans hf.lr
  obtain x3u : u.gpr .x3 = base := by rw [gu _ (by decide)]; exact hpost.x3
  refine ⟨⟨⟨x3u, by rw [gu _ (by decide)]; exact hpost.mask, by rw [uw, hwr, w₃]; exact hs.wr, hnw⟩,
    by rw [um]; exact hpost.env, by rw [um]; exact hpost.zero, l30, ?_, by rw [ur, hrd, r₃, hf.rd],
    by rw [uw, hwr, w₃, hf.wr], ?_⟩, by rw [um]; exact hpost.odd, by rw [um]; exact hpost.even⟩
  · rw [gu _ (by decide), hpres .x20 (by decide) (by decide), gk _ (by decide), g₂ _ (by decide)]
    exact hf.out
  · rw [um]
    exact hf.mem.trans hm

end VG.Proof.Ed448.AArch64.CombBase

end

end

/-!
# Ed448's comb on AArch64: `16 A + B` by calls

Untrusted: everything here is checked by Lean. `combineCall` (the comb's
`A := 16 A + B` by calls of `vg_ed448_r56_point_add`) leaves what X448's
`Base.combine` does (as `combine_ok`): `B` kept in slots 0–2,
`A` moved to slots 3–5 and added to a copy of itself in slots 6–8 four times
(`addCall_ok`, whose addition is `addPt` with 0 in slot 19), `B` added, and the
sum moved to slots 0–2; the return address kept in a lane of `v8` across the
calls (`WP.preservedV`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64 VG.Impl.Ed448.AArch64.Point56
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genPt genPt_eq temps zero_env StepInv)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Proof.X448 (addPt addPt_rep)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-- What `combineMid` keeps: `Frame` but for the return address. -/
structure MFrame (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  out : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem MFrame.keeps {s₀ s t : State} {base : Addr} {rs : List Reg} (h : MFrame s₀ base s) (k : Keeps rs s t)
    (h312 : .x3 ∉ rs ∧ .x12 ∉ rs) (h20 : .x20 ∉ rs) (hm : t.mem = s.mem) : MFrame s₀ base t :=
  ⟨h.scr.of_keeps k h312, by rw [hm]; exact h.env, by rw [hm]; exact h.zero,
    by rw [k.1 _ h20]; exact h.out, by rw [k.2.1]; exact h.rd, by rw [k.2.2]; exact h.wr,
    by rw [hm]; exact h.mem⟩

theorem FV_of_limbs {m m' : Mem} {base : Addr} {o o' : Nat} (h : ∀ i < 8, limbs m' base o' i = limbs m base o i) :
    FV m' base o' = FV m base o := congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

/-- Three slots copied from three others: the copies' limbs, and every other slot's kept. -/
theorem copy3_ok {s₀ s : State} {base : Addr} (h : MFrame s₀ base s) (o a : Nat) (ho : o + 3 ≤ 10) (ha : a + 3 ≤ 10)
    (hsep : o + 3 ≤ a ∨ a + 3 ≤ o) :
    WP isa (.block (copy3 o a)) s fun t => MFrame s₀ base t ∧
      pt (EV t.mem base) ⟨o, by omega_arith⟩ ⟨o + 1, by omega_arith⟩ ⟨o + 2, by omega_arith⟩ =
        pt (EV s.mem base) ⟨a, by omega_arith⟩ ⟨a + 1, by omega_arith⟩ ⟨a + 2, by omega_arith⟩ ∧
      (∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
        limbs s.mem base (slot i.val) j) ∧
      Keeps VG.Proof.X448.AArch64.clob s t := by
  have hs := h.scr
  rw [copy3, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (o := slot o) (a := slot a) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (Or.inr (by simp only [slot]; omega_arith))) fun t1 ⟨v1, o1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs1 (o := slot (o + 1)) (a := slot (a + 1))
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (Or.inr (by simp only [slot]; omega_arith))) fun t2 ⟨v2, o2, k2⟩ => ?_
  obtain hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs2 (o := slot (o + 2)) (a := slot (a + 2))
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (Or.inr (by simp only [slot]; omega_arith))) fun t ⟨v3, o3, k3⟩ => ?_
  obtain hc : ∀ c < 3, ∀ j < 8, limbs t.mem base (slot (o + c)) j = limbs s.mem base (slot (a + c)) j := by
    intro c hc j hj
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega_arith) with rfl | rfl | rfl
    · rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
        o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith), Nat.add_zero, v1 j hj,
        Nat.add_zero]
    · rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith), v2 j hj,
        o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
    · rw [v3 j hj, o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
        o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
  obtain hk : ∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
      limbs s.mem base (slot i.val) j := fun i hi j hj => by
    have := i.isLt
    rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
      o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
      o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
  obtain k : Keeps VG.Proof.X448.AArch64.clob s t := (k1.trans k2).trans k3
  obtain om : Outside base (slot o) 384 s.mem t.mem := by
    intro x hx
    rw [o3 x (by simp only [slot] at hx ⊢; omega_arith), o2 x (by simp only [slot] at hx ⊢; omega_arith),
      o1 x (by simp only [slot] at hx ⊢; omega_arith)]
  refine ⟨⟨hs.of_keeps k (by decide), fun i => ?_, fun w hw => ?_, by rw [k.1 _ (by decide)]; exact h.out,
    by rw [k.2.1]; exact h.rd, by rw [k.2.2]; exact h.wr, h.mem.trans fun x h1 _ => om x (by
      simp only [slot] at h1 ⊢; omega_arith)⟩, ?_, hk, k⟩
  · by_cases hi : i.val < o ∨ o + 3 ≤ i.val
    · exact fun j hj => by rw [hk i hi j hj]; exact h.env i j hj
    · have e : i.val = o + (i.val - o) := by omega_arith
      exact fun j hj => by
        show limbs t.mem base (slot i.val) j < Ib
        rw [e, hc _ (by omega_arith) j hj]; exact h.env ⟨a + (i.val - o), by omega_arith⟩ j hj
  · rw [hk 19 (by simp; omega_arith) w hw]; exact h.zero w hw
  · simp only [pt, VG.Proof.X448.AArch64.Weak.E]
    rw [FV_of_limbs (o := slot a) (o' := slot o) (fun j hj => by simpa using hc 0 (by decide) j hj),
      FV_of_limbs (hc 1 (by decide)), FV_of_limbs (hc 2 (by decide))]

/-- The point in slots 3–5 added to the point in slots 6–8, by a call. -/
theorem addC_ok {s₀ s : State} {base : Addr} (h : MFrame s₀ base s) :
    WP isa addCall s fun t => MFrame s₀ base t ∧ Keeps (.x30 :: VG.Proof.X448.AArch64.Fast.fclob) s t ∧
      pt (EV t.mem base) 3 4 5 = addPt (pt (EV s.mem base) 3 4 5) (pt (EV s.mem base) 6 7 8) ∧
      (∀ i : Index, i.val < 3 → EV t.mem base i = EV s.mem base i) := by
  refine WP.mono (addCall_ok h.scr h.env (zero_env h.zero).2) fun t ⟨k, b, sm, _, _, _, e, _⟩ => ?_
  obtain n19 : (19 : Index) ∉ temps ++ [3, 4, 5] := by decide
  obtain nt : ∀ i : Index, i.val < 3 → i ∉ temps ++ [3, 4, 5] := by decide
  refine ⟨⟨k.scr h.scr, b, fun w hw => by rw [sm 19 n19 w hw]; exact h.zero w hw,
    by rw [k.regs.1 _ (by decide)]; exact h.out, by rw [k.regs.2.1]; exact h.rd, by rw [k.regs.2.2]; exact h.wr,
    h.mem.trans k.mem⟩, k.regs, ?_, fun i hi => Same.env sm (nt i hi)⟩
  rw [e, genEnv_pt, (zero_env h.zero).1, genPt_eq]

theorem setX1_ok (s : State) :
    WP isa (.block [.movz .w .x1 4 0]) s fun t => t.gpr .x1 = BitVec.ofNat 64 4 ∧ Keeps [.x1] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl⟩, rfl⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem dec_x1 : ∀ n < 4, BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n ∧
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

theorem decX1_ok (s : State) {n : Nat} (hn : n < 4) (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t ∧ t.mem = s.mem ∧
        (t.gpr .x1 != 0) = decide (n ≠ 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    (dec_x1 n hn).1, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl,
    (dec_x1 n hn).2⟩

/-- The doublings' state with `m` of them left: `A` in slots 3–5, `B` in 0–2. -/
structure DInv (s₀ : State) (base : Addr) (v w : ℤ) (m : Nat) (s : State) : Prop where
  frame : MFrame s₀ base s
  counter : s.gpr .x1 = BitVec.ofNat 64 m
  a : Rep (pt (EV s.mem base) 3 4 5) ((2 ^ (4 - m) * v) • baseAff)
  b : Rep (pt (EV s.mem base) 0 1 2) (w • baseAff)

theorem dbl_ok {s₀ s : State} {base : Addr} {v w : ℤ} {m : Nat} (hm : 1 ≤ m) (hm4 : m ≤ 4)
    (h : DInv s₀ base v w m s) :
    WP isa (.seq (.block (copy3 6 3)) (.seq addCall (.block [.subImm .x .x1 .x1 1]))) s
      fun t => DInv s₀ base v w (m - 1) t ∧ (t.gpr .x1 != 0) = decide (m - 1 ≠ 0) := by
  refine WP.seq (WP.mono (copy3_ok h.frame 6 3 (by decide) (by decide) (by decide))
    fun t1 ⟨f1, p1, k1, g1⟩ => ?_)
  obtain e1 : ∀ i : Index, i.val < 6 → EV t1.mem base i = EV s.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (k1 i (.inl hi)))
  refine WP.seq (WP.mono (addC_ok f1) fun t2 ⟨f2, kk2, q2, b2⟩ => ?_)
  refine WP.mono (decX1_ok (n := m - 1) t2 (by omega_arith) (by
      rw [kk2.1 _ (by decide), g1.1 _ (by decide), h.counter]; congr 1; omega_arith))
    fun u ⟨uc, uk, um, uz⟩ => ⟨⟨f2.keeps uk (by decide) (by decide) um, uc, ?_, ?_⟩, uz⟩
  · rw [um, q2]
    obtain p3 : pt (EV t1.mem base) 3 4 5 = pt (EV s.mem base) 3 4 5 := by
      simp only [pt]; rw [e1 3 (by decide), e1 4 (by decide), e1 5 (by decide)]
    have p6 : pt (EV t1.mem base) 6 7 8 = pt (EV s.mem base) 3 4 5 := p1
    rw [p3, p6]
    have := addPt_rep h.a h.a
    rw [← add_smul] at this
    rw [show (2 : ℤ) ^ (4 - (m - 1)) * v = 2 ^ (4 - m) * v + 2 ^ (4 - m) * v by
      rw [show 4 - (m - 1) = (4 - m) + 1 by omega_arith, pow_succ]; ring]
    exact this
  · rw [um]
    simp only [pt]
    rw [b2 0 (by decide), b2 1 (by decide), b2 2 (by decide), e1 0 (by decide), e1 1 (by decide),
      e1 2 (by decide)]
    exact h.b

theorem EV_of_keep {m m' : Mem} {base : Addr} {i : Index}
    (h : ∀ j < 8, limbs m' base (slot i.val) j = limbs m base (slot i.val) j) : EV m' base i = EV m base i :=
  congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

/-- `combineMid`: `16 A + B` in slots 0–2, for `A` in slots 0–2 and `B` in 3–5. -/
theorem combineMid_ok {s₀ s : State} {base : Addr} {v w : ℤ} (f0 : MFrame s₀ base s)
    (ha : Rep (pt (EV s.mem base) 0 1 2) (v • baseAff)) (hb : Rep (pt (EV s.mem base) 3 4 5) (w • baseAff)) :
    WP isa combineMid s fun t => MFrame s₀ base t ∧
      Rep (pt (EV t.mem base) 0 1 2) ((16 * v + w) • baseAff) := by
  unfold combineMid
  rw [WP.seq_iff, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy3_ok f0 6 0 (by decide) (by decide) (by decide)) fun t1 ⟨f1, p1, k1, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy3_ok f1 0 3 (by decide) (by decide) (by decide)) fun t2 ⟨f2, p2, k2, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy3_ok f2 3 6 (by decide) (by decide) (by decide)) fun t3 ⟨f3, p3, k3, _⟩ => ?_
  refine WP.mono (setX1_ok t3) fun t4 ⟨c4, kk4, m4⟩ => ?_
  have p1' : pt (EV t1.mem base) 6 7 8 = pt (EV s.mem base) 0 1 2 := p1
  have p2' : pt (EV t2.mem base) 0 1 2 = pt (EV t1.mem base) 3 4 5 := p2
  have p3' : pt (EV t3.mem base) 3 4 5 = pt (EV t2.mem base) 6 7 8 := p3
  obtain pA : pt (EV t3.mem base) 3 4 5 = pt (EV s.mem base) 0 1 2 := by
    obtain q : pt (EV t2.mem base) 6 7 8 = pt (EV t1.mem base) 6 7 8 := by
      simp only [pt]
      rw [EV_of_keep (k2 6 (.inr (by decide))), EV_of_keep (k2 7 (.inr (by decide))),
        EV_of_keep (k2 8 (.inr (by decide)))]
    rw [p3', q, p1']
  obtain pB : pt (EV t3.mem base) 0 1 2 = pt (EV s.mem base) 3 4 5 := by
    obtain q : pt (EV t3.mem base) 0 1 2 = pt (EV t2.mem base) 0 1 2 := by
      simp only [pt]
      rw [EV_of_keep (k3 0 (.inl (by decide))), EV_of_keep (k3 1 (.inl (by decide))),
        EV_of_keep (k3 2 (.inl (by decide)))]
    obtain q' : pt (EV t1.mem base) 3 4 5 = pt (EV s.mem base) 3 4 5 := by
      simp only [pt]
      rw [EV_of_keep (k1 3 (.inl (by decide))), EV_of_keep (k1 4 (.inl (by decide))),
        EV_of_keep (k1 5 (.inl (by decide)))]
    rw [q, p2', q']
  obtain d4 : DInv s₀ base v w 4 t4 :=
    ⟨f3.keeps kk4 (by decide) (by decide) m4, c4, by rw [m4, pA]; simpa using ha, by rw [m4, pB]; exact hb⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => DInv s₀ base v w 0 t)
    (fun m (t : State) => 1 ≤ m ∧ m ≤ 4 ∧ DInv s₀ base v w m t) ?_ 4 t4 ⟨by decide, le_refl _, d4⟩) ?_)
  · intro m t ⟨h1, h4, ht⟩
    refine WP.mono (dbl_ok h1 h4 ht) fun u ⟨hu, hz⟩ => ?_
    simp only [eval, State.read, BitVec.setWidth_eq, hz]
    by_cases hm : m = 1
    · subst hm; exact .inl ⟨rfl, hu⟩
    · exact .inr ⟨by simp only [decide_eq_true (by omega_arith : m - 1 ≠ 0)], m - 1,
        by omega_arith, by omega_arith, by omega_arith, hu⟩
  · intro t ht
    refine WP.seq (WP.mono (copy3_ok ht.frame 6 0 (by decide) (by decide) (by decide))
      fun t5 ⟨f5, p5, k5, _⟩ => ?_)
    refine WP.seq (WP.mono (addC_ok f5) fun t6 ⟨f6, _, q6, _⟩ => ?_)
    refine WP.mono (copy3_ok f6 0 3 (by decide) (by decide) (by decide)) fun t7 ⟨f7, p7, _, _⟩ => ⟨f7, ?_⟩
    have p5' : pt (EV t5.mem base) 6 7 8 = pt (EV t.mem base) 0 1 2 := p5
    have p7' : pt (EV t7.mem base) 0 1 2 = pt (EV t6.mem base) 3 4 5 := p7
    obtain a5 : pt (EV t5.mem base) 3 4 5 = pt (EV t.mem base) 3 4 5 := by
      simp only [pt]
      rw [EV_of_keep (k5 3 (.inl (by decide))), EV_of_keep (k5 4 (.inl (by decide))),
        EV_of_keep (k5 5 (.inl (by decide)))]
    rw [p7', q6, a5, p5']
    obtain r := addPt_rep ht.a ht.b
    rw [← add_smul, show (2 : ℤ) ^ (4 - 0) * v + w = 16 * v + w by norm_num] at r
    exact r

/-- **`16 A + B` by calls**, from `Frame`: `[16 v + w] B` in `A`, the return address kept. -/
theorem combineCall_frame {s₀ s : State} {base : Addr} {v w : ℤ} (h : VG.Proof.X448.AArch64.Base.Frame s₀ base s)
    (ha : Rep (pt (EV s.mem base) 0 1 2) (v • baseAff)) (hb : Rep (pt (EV s.mem base) 3 4 5) (w • baseAff)) :
    WP isa combineCall s fun t => VG.Proof.X448.AArch64.Base.Frame s₀ base t ∧
      Rep (pt (EV t.mem base) 0 1 2) ((16 * v + w) • baseAff) := by
  unfold combineCall
  rw [WP.seq_iff]
  refine WP.mono (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide)) fun t₁ ⟨g₁, m₁, r₁, w₁, _, l₁, _⟩ => ?_
  obtain f₁ : MFrame s₀ base t₁ :=
    ⟨h.scr.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide), m₁ ▸ h.env, m₁ ▸ h.zero,
      by rw [g₁]; exact h.out, by rw [r₁]; exact h.rd, by rw [w₁]; exact h.wr, m₁ ▸ h.mem⟩
  rw [WP.seq_iff]
  refine WP.mono (WP.preservedV (combineMid_ok f₁ (m₁ ▸ ha) (m₁ ▸ hb)) (by lit_decide))
    fun t₂ ⟨⟨f₂, r₂⟩, v₂⟩ => ?_
  refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t₂ (by decide) (by decide)) fun u ⟨um, ur, uw, _, ul, uo⟩ => ?_
  obtain l30 : u.gpr .x30 = s₀.gpr .x30 := by
    rw [ul _ List.mem_cons_self]
    show (t₂.v .v8).extractLsb' (64 * 0) 64 = _
    rw [v₂ .v8 (by decide)]
    exact (l₁ _ List.mem_cons_self).trans h.lr
  obtain ku : Keeps [.x30] t₂ u := ⟨fun r hr => uo r (by simpa using hr), ur, uw⟩
  refine ⟨⟨f₂.scr.of_keeps ku (by decide), um ▸ f₂.env, um ▸ f₂.zero, l30,
    by rw [ku.1 _ (by decide)]; exact f₂.out, by rw [ur]; exact f₂.rd, by rw [uw]; exact f₂.wr, um ▸ f₂.mem⟩, ?_⟩
  rw [um]
  exact r₂

end VG.Proof.Ed448.AArch64.Point56
