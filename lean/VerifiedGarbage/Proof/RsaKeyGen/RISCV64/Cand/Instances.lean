module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Verified
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTTest
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.TrialOk

/-!
# `vg_rsa_keygen_candidate` on RISC-V: verified

`cand_verified`: correctness (`cand_correct`), constant time (`cand_ct`, with
the test's `test_ct`) and the contract's satisfiable precondition, for any
trial division and any implementation of the Miller–Rabin round;
`candidate_verified`: with the shared trial division (`Trial.trial hTrial`,
`trial_divOk`), which the registration
(`Generic/MillerRabin/RISCV64/RsaKeyGen.lean`) takes from each variant.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

theorem cand_verified {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    Verified target (VG.Impl.RsaKeyGen.RISCV64.Candidate.code trial R.name R.code) contract :=
  ⟨cand_correct D R, cand_ct D R (test_ct D R), ⟨satState, sat⟩⟩

theorem candidate_verified (R : RoundImpl) :
    Verified target (VG.Impl.RsaKeyGen.RISCV64.Candidate.code
      (VG.Impl.RsaKeyGen.RISCV64.Trial.trial VG.Impl.RsaKeyGen.RISCV64.Candidate.hTrial) R.name R.code) contract :=
  cand_verified TrialOk.trial_divOk R

end VG.Proof.RsaKeyGen.RISCV64.Cand
