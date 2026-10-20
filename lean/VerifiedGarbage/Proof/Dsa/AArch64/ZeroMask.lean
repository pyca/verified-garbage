module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Dsa.AArch64.Operands

/-! # Branch-free zero and equality masks -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem exec_tst_x (s : State) (r : Reg) :
    exec (.tst .x r r) s = some {s with nf := (s.gpr r).msb, zf := (s.gpr r == 0), c := false, vf := false} := by
  simp only [exec, State.read, Size.bits, BitVec.setWidth_eq, BitVec.and_self]
  rfl

theorem exec_cselc_x (s : State) (d n m : Reg) (c : CondCode) :
    exec (.cselc .x d n m c) s = some (s.write .x d (if c.holds s then s.gpr n else s.gpr m)) := rfl

theorem zeroMask_ok (r : Reg) (invert : Bool) {s : State} :
    WP isa (.block (Checks.zeroMask r invert)) s fun t =>
      t.gpr .x3 = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.gpr .x3 = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
    t.mem = s.mem) ?_ rfl rfl rfl) fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold Checks.zeroMask
  cases invert <;> brun [exec_tst_x, exec_cselc_x, CondCode.holds, State.write, mask]
  all_goals split <;> simp_all

end VG.Proof.Dsa.AArch64
