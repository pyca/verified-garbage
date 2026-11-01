module
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Dsa.X86.PublicDomain
import VerifiedGarbage.Proof.Dsa.X86.SigningOperationTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperationTiming
import VerifiedGarbage.Proof.Dsa.X86.SharedPublic

/-! # Whole-operation constant time against the shared DSA contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem verifyingConstantTime : ConstantTime isa (Spec.Dsa.verifyContract abi 108).pre
    (Spec.Dsa.verifyContract abi 108).pub (Entry.operation false) := by
  intro s t tr ur sf tf S T H E F
  have Args := verifyingPublicArgs H
  have Domain := verifyingPublicDomain H
  exact verifyingOperation_agrees (verifyingABI_of S) (verifyingABI_of T) Args.2 Args.1 Domain.1 Domain.2 E F

theorem signingConstantTime : ConstantTime isa (Spec.Dsa.signContract abi 108).pre
    (Spec.Dsa.signContract abi 108).pub (Entry.operation true) := by
  intro s t tr ur sf tf S T H E F
  have Args := signingPublicArgs H
  have Domain := signingPublicDomain H
  exact signingOperation_agrees (signingABI_of S) (signingABI_of T) Args.2 Args.1 Domain.1 Domain.2 E F

end VG.Proof.Dsa.X86
