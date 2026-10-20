module
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Dsa.X86.KeyPointerStep
import VerifiedGarbage.Proof.Dsa.X86.HeaderFrame
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # Unpacking the p, q, g, y, and x pointers from a packed key -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem keyPointers_ok {s : State} {base : Addr} {size : Nat} {key plen qlen : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hp : pointerValue base s (.input .p) = key)
    (hpl : pointerValue base s (.input .pLen) = plen)
    (hql : pointerValue base s (.input .qLen) = qlen) :
    WP isa (.block Entry.keyPointers) s fun t =>
      pointerValue base t (.input .q) = key + plen ∧
      pointerValue base t (.input .g) = key + plen + qlen ∧
      pointerValue base t (.input .y) = key + plen + qlen + plen ∧
      pointerValue base t (.input .x) = key + plen + qlen + plen + plen ∧
      Keeps [.eax] s t ∧
      Outs base [(Layout.field .q, 4), (Layout.field .g, 4), (Layout.field .y, 4), (Layout.field .x, 4)] s.mem t.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds .p
  unfold Entry.keyPointers
  simp only [List.append_assoc, List.singleton_append]
  refine wp_movS (readSrc_sc hs (by omega)) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine WP.block_append (WP.mono (addPointer_ok .pLen .q hu hz) fun s1 ⟨A1, V1, K1, O1⟩ => ?_)
  have P0 : pointerValue base u (.input .pLen) = plen := by simpa only [pointerValue, U.mem] using hpl
  have Q1 : pointerValue base s1 (.input .qLen) = qlen := by
    rw [field_keep O1 (by decide)]
    simpa only [pointerValue, U.mem] using hql
  have X1 : s1.gpr .eax = key + plen := by rw [A1, P0, U.gpr]; exact congrArg (· + plen) hp
  refine WP.block_append (WP.mono (addPointer_ok .qLen .g (hu.of_keeps K1 (by decide)) hz)
    fun s2 ⟨A2, V2, K2, O2⟩ => ?_)
  have X2 : s2.gpr .eax = key + plen + qlen := by rw [A2, X1, Q1]
  have P2 : pointerValue base s2 (.input .pLen) = plen := by
    rw [field_keep O2 (by decide), field_keep O1 (by decide), P0]
  have K12 := K1.trans K2
  refine WP.block_append (WP.mono (addPointer_ok .pLen .y (hu.of_keeps K12 (by decide)) hz)
    fun s3 ⟨A3, V3, K3, O3⟩ => ?_)
  have X3 : s3.gpr .eax = key + plen + qlen + plen := by rw [A3, X2, P2]
  have P3 : pointerValue base s3 (.input .pLen) = plen := by rw [field_keep O3 (by decide), P2]
  refine WP.mono (addPointer_ok .pLen .x (hu.of_keeps (K12.trans K3) (by decide)) hz)
    fun t ⟨_, V4, K4, O4⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, U.keeps.trans (((K12).trans K3).trans K4), ?_⟩
  · rw [field_keep O4 (by decide), field_keep O3 (by decide), field_keep O2 (by decide), V1, P0, U.gpr]
    exact congrArg (· + plen) hp
  · rw [field_keep O4 (by decide), field_keep O3 (by decide), V2, X1, Q1]
  · rw [field_keep O4 (by decide), V3, X2, P2]
  · rw [V4, X3, P3]
  · rw [U.mem] at O1
    exact (((Outs.of_outside O1 (by simp)).trans (Outs.of_outside O2 (by simp))).trans
      (Outs.of_outside O3 (by simp))).trans (Outs.of_outside O4 (by simp))

end VG.Proof.Dsa.X86
