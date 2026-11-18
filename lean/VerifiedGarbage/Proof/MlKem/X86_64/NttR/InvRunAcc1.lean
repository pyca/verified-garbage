module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the second half of pass B from an accumulator

The state after half 1 of pass B, as a literal, from that after half 0
(`stIAcc1F`, the run by `St.runF`, `Fast.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stIAcc1`, run by `St.runF`. -/
def stIAcc1F : Option St := stIAcc0F.bind fun σ => σ.runF zmTab invRules (St.step invRules rsA) passIBAcc1

theorem stIAcc1_eq : stIAcc1 = stIAcc1F := by
  simp only [stIAcc1, stI1, stIAcc0_eq, stIAcc1F, St.runF_eq]

materialize_value stIAcc1F

end VG.Proof.MlKem.X86_64.NttR
