module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc1
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, pass A after reading an accumulator

The state after pass A, as a literal, from that after pass B (`stIAccAF`,
the run by `St.runF`, `Fast.lean`), and the check of its output
(`checkI_acc`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stIAccA`, run by `St.runF`. -/
def stIAccAF : Option St :=
  stIAcc1F.bind fun σ => (toB σ).runF zmTab invRules (St.step invRules (rsB .rdi)) passIA

theorem stIAccA_eq : stIAccA = stIAccAF := by
  simp only [stIAccA, stIA, stIAcc1_eq, stIAccAF, St.runF_eq]

materialize_value stIAccAF

theorem checkI_acc : checkI .acc passIBsAcc = true :=
  checkI_of (p₀ := passIBAcc0) (p₁ := passIBAcc1)
    (show stIAccA.any outOk = true by rw [stIAccA_eq, stIAccAF.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
