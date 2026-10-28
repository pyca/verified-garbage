module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2

/-! # `init` of the batched inverse in both runs, in `crt_values`' layout -/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)

variable {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem relInit (F : Fits Z len) :
    RelCT isa (fun s t => Pre0 lay B Z len N args sp s ∧ Pre0 lay B Z len N args sp t) (init lay)
      (Both lay B Z len N args sp (· = 3 * (nw len + 1)) fun _ => True ∧ True) := by
  have F1 := F.fit
  have F2 := F.two
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r4 := rv_a len 4; have r5 := rv_a len 5
  have r6 := rv_a len 6; have r7 := rv_a len 7; have r8 := rv_a len 8; have r12 := rv_a len 12
  have h41 := rv_half1' len 4; have h51 := rv_half1' len 5
  unfold init
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relSlots rfl (by taint_decide)) ?_
  refine RelCT.seq (relCopy rfl (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relVirtualize rfl (stable_true _) F2 F1 (by taint_decide)) ?_
  refine RelCT.seq (relCopy rfl (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeroWord rfl (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopy rfl (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeroWord rfl (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros rfl (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relEvenMask rfl (stable_true _) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn rfl (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainAdd (X := fun _ => True) rfl (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relWinOne rfl (stable_true _) F1 (by taint_decide)) ?_
  refine RelCT.seq (relZeros rfl (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros rfl (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relA7One rfl (stable_true _) F1 (by taint_decide)) ?_
  refine RelCT.seq (relInverse rfl (stable_true _) F1 (by taint_decide)) ?_
  exact relBatches rfl (stable_true _) (by taint_decide)

end VG.Proof.Rsa.X86.InvBatchRt.Time
