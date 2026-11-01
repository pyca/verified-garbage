module
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Weierstrass.PointContract

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming

/-! # Public stack addresses suffice for every verifier straight-line fragment -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Dsa.X86

theorem encArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block encArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem pubArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block pubArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmpArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block cmpArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem save_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (stackAt statusOffset) .eax])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem result_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block result)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem length_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block lenCheck)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem ret0_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) ret0
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmp_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .eax])) (.block test0)
    (VG.X86.Taint.Agree (τr [.esp, .eax])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Sig.X86.Ver
