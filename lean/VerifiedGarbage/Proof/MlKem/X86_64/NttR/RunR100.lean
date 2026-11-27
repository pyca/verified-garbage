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
# ML-KEM on x86-64: the NTT on registers, the first half of pass B to `r10`

The state after half 0 of pass B storing to `r10`, for the functions that inline the NTT, as a
literal, from that after pass A. The kernel evaluates the run by `St.runF` (`Fast.lean`): `stR100F`,
which is `stR100` (`stR100_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stR100`, run by `St.runF`. -/
def stR100F : Option St := stA.bind fun σ => (toB σ).runF zmTab fwdRules (St.step fwdRules (rsB .r10)) passBR100

theorem stR100_eq : stR100 = stR100F := by
  simp only [stR100, stB0, stR100F, St.runF_eq]

materialize_value stR100F

end VG.Proof.MlKem.X86_64.NttR
