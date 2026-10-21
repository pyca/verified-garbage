module

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryTransport
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.RawArgs
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Choose symmetric squares using only public operand indices -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86

def dispatchHead : List Instr := [.mov .eax (.mem (rawArg 3)), .mov .edx (.mem (rawArg 4)), .alu .cmp .eax (.reg .edx)]

theorem sub_beq_zero (x y : BitVec 32) : (x - y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have H := congrArg BitVec.toNat h
    change (x - y).toNat = 0 at H
    rw [BitVec.toNat_sub] at H
    have := x.isLt
    have := y.isLt
    omega
  · intro h
    rw [h, BitVec.sub_self]
    rfl

theorem dispatchHead_ok {s : State} (A : Compact.Entry s) :
    WP isa (.block dispatchHead) s fun t => t.zf = some (decide (arg s 3 = arg s 4)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  have ha := raw_args A
  unfold dispatchHead
  refine wp_movS (ha.read 3 (by decide)) fun s1 U1 _ =>
    wp_movS ((ha.of_upd U1 (by decide)).read 4 (by decide)) fun s2 U2 _ =>
    wp_cmpS rfl fun t F zf => WP.block_nil ?_
  refine ⟨?_, F.mem.trans (U2.mem.trans U1.mem),
    ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (F.keeps _)⟩
  rw [zf, U2.other .eax (by decide), U1.gpr, U2.gpr, sub_beq_zero]

theorem dispatchHead_trace : RelCT isa (VG.X86.Taint.Agree (argTaint [] 24)) (.block dispatchHead)
    (VG.X86.Taint.Agree {argTaint [.eax, .edx] 24 with flags := true}) :=
  erased_relCT _ _ (.block []) rfl rfl rfl rfl

end VG.Proof.Mont.X86.PreparedSquare
