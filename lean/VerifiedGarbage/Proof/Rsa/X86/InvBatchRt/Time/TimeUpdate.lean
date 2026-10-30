module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # A batch's update in both runs, in `crt_values`' layout -/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)

variable {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

theorem relUpdate (F : Fits Z len) :
    RelCT isa (Both lay B Z len N args sp C fun _ => True ∧ True) (update lay)
      (Both lay B Z len N args sp C fun _ => True ∧ True) := by
  have F1 := F.fit
  have r0 := rv_a len 0; have r1 := rv_a len 1; have r4 := rv_a len 4; have r5 := rv_a len 5
  have r6 := rv_a len 6; have r7 := rv_a len 7; have r11 := rv_a len 11; have r13 := rv_a len 13
  have r14 := rv_a len 14
  unfold update
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relLinear F.toRoom (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relShr30 (stable_true _) rfl F.even (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relLinear F.toRoom (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relShr30 (stable_true _) rfl F.even (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relLinear F.toRoom (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relReduce F.toRoom (by decide) (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relLinear F.toRoom (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relReduce F.toRoom (by decide) (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  exact relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)

end VG.Proof.Rsa.X86.InvBatchRt.Time
