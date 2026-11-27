module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
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
# ML-KEM on x86-64: the NTT on registers, the first half of pass B to an accumulator

The state after half 0 of pass B storing to the accumulator at `r10`, as a
literal, from that after pass A. The kernel evaluates the run by `St.runF`
(`Fast.lean`): `stAccR100F`, which is `stAccR100` (`stAccR100_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stAccR100`, run by `St.runF`. -/
def stAccR100F : Option St :=
  stA.bind fun σ => (toBA σ).runF zmTab fwdRules (St.step fwdRules (rsBA .r10)) passBAccR100

theorem stAccR100_eq : stAccR100 = stAccR100F := by
  simp only [stAccR100, stAccB0, stAccR100F, St.runF_eq]

materialize_value stAccR100F

end VG.Proof.MlKem.X86_64.NttR
