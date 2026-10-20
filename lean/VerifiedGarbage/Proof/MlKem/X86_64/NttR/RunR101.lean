module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunR100
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

/-!
# ML-KEM on x86-64: the NTT on registers, the second half of pass B to `r10`

The state after half 1 of pass B storing to `r10`, as a literal, from that
after half 0, and the check of its output (`check_r10`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stR101

theorem check_r10 : check passBsR10 .r10 = true :=
  check_of (p₀ := passBR100) (p₁ := passBR101) (show stR101.any outOk = true by rw [stR101.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
