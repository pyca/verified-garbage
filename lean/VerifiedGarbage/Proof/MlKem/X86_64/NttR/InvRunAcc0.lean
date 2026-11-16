module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
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
# ML-KEM on x86-64: `NTT⁻¹` on registers, the first half of pass B from an accumulator

The state after half 0 of pass B reading an accumulator, for the functions that inline `NTT⁻¹`, as a literal.
The kernel evaluates the run by `St.runF` (`Fast.lean`): `stIAcc0F`, which is `stIAcc0` (`stIAcc0_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stIAcc0`, run by `St.runF`. -/
def stIAcc0F : Option St := (initIB .acc).runF zmTab invRules (St.step invRules rsA) passIBAcc0

theorem stIAcc0_eq : stIAcc0 = stIAcc0F := by
  simp only [stIAcc0, stI0, stIAcc0F, St.runF_eq]

materialize_value stIAcc0F

end VG.Proof.MlKem.X86_64.NttR
