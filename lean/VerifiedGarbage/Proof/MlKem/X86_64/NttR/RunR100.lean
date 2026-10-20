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

/-!
# ML-KEM on x86-64: the NTT on registers, the first half of pass B to `r10`

The state after half 0 of pass B storing to `r10`, for the functions that inline the NTT, as a
literal, from that after pass A.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stR100

end VG.Proof.MlKem.X86_64.NttR
