module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# ML-KEM on x86-64: the NTT on registers, the first half of pass B to an accumulator

The state after half 0 of pass B storing to the accumulator at `r10`, as a
literal, from that after pass A.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stAccR100

end VG.Proof.MlKem.X86_64.NttR
