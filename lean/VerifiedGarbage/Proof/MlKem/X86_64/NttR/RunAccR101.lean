module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunAccR100
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunAccR100
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit

/-!
# ML-KEM on x86-64: the NTT on registers, the second half of pass B to an accumulator

The state after half 1 of pass B storing to the accumulator at `r10`, as a
literal, from that after half 0 (`stAccR101F`, the run by `St.runF`,
`Fast.lean`), and the check of its output (`checkAcc_r10`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stAccR101`, run by `St.runF`. -/
def stAccR101F : Option St :=
  stAccR100F.bind fun σ => σ.runF zmTab fwdRules (St.step fwdRules (rsBA .r10)) passBAccR101

theorem stAccR101_eq : stAccR101 = stAccR101F := by
  simp only [stAccR101, stAccR100_eq, stAccR101F, St.runF_eq]

materialize_value stAccR101F

theorem checkAcc_r10 : checkAcc passBsAccR10 .r10 = true :=
  checkAcc_of (p₀ := passBAccR100) (p₁ := passBAccR101)
    (show stAccR101.any outAccOk = true by rw [stAccR101_eq, stAccR101F.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
