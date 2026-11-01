module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Choose
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Ffdh.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Ffdh.AArch64
open VG VG.AArch64 VG.Proof.Bignum.AArch64

def contract : Contract isa where
  pre _ := True
  post s t := t.gpr .x0 = Spec.Ffdh.choose (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) ∧ t.mem = s.mem
  pub _ _ := True

theorem correct (s : State) (_ : contract.pre s) :
    ∃ tr t, Exec isa Impl.Ffdh.AArch64.choose s tr t ∧ abiPreserved s t ∧ contract.post s t := by
  have h : WP isa Impl.Ffdh.AArch64.choose s (fun t =>
      t.gpr .x0 = Spec.Ffdh.choose (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) ∧ t.mem = s.mem) := by
    unfold Impl.Ffdh.AArch64.choose
    rw [VG.Proof.Ffdh.choose_low_bit]
    brun [exec, CondCode.holds, decide_eq_true_eq]
    rfl
  obtain ⟨tr, t, he, ho, hk⟩ := WP.keep [.x0, .x1, .x2, .x3] h rfl rfl rfl
  refine ⟨tr, t, he, ⟨?_, hk.sp, hk.vcs⟩, ho⟩
  intro r hr
  exact hk.gpr r (by revert r; decide)

theorem ct : ConstantTime isa contract.pre contract.pub Impl.Ffdh.AArch64.choose := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Impl.Ffdh.AArch64.choose, Exec.block_iff] at h
  cases h
  rfl

def sat : State where
  gpr _ := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := []

theorem verified : Verified target Impl.Ffdh.AArch64.choose (Proof.Ffdh.chooseContract abi) :=
  Verified.of_correct correct ct (by
    sig_implies [Proof.Ffdh.chooseContract, Proof.Ffdh.chooseSig, contract, abi, argRegs] [sat] using sat)

end VG.Proof.Ffdh.AArch64
