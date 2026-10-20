module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunAcc0
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the second half of pass B from an accumulator

The state after half 1 of pass B, as a literal, from that after half 0.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stIAcc1

end VG.Proof.MlKem.X86_64.NttR
