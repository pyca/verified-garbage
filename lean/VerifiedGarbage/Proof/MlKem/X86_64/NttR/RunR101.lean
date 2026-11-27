module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR100
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR100
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
# ML-KEM on x86-64: the NTT on registers, the second half of pass B to `r10`

The state after half 1 of pass B storing to `r10`, as a literal, from that
after half 0 (`stR101F`, the run by `St.runF`, `Fast.lean`), and the check of
its output (`check_r10`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stR101`, run by `St.runF`. -/
def stR101F : Option St := stR100F.bind fun σ => σ.runF zmTab fwdRules (St.step fwdRules (rsB .r10)) passBR101

theorem stR101_eq : stR101 = stR101F := by
  simp only [stR101, stR100_eq, stR101F, St.runF_eq]

materialize_value stR101F

theorem check_r10 : check passBsR10 .r10 = true :=
  check_of (p₀ := passBR100) (p₁ := passBR101)
    (show stR101.any outOk = true by rw [stR101_eq, stR101F.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
