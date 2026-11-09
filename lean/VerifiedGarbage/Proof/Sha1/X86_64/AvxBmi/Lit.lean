module

public import VerifiedGarbage.Impl.Sha1.X86_64.AvxBmi
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha1.X86_64.AvxBmi
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-1 with AVX and BMI on x86-64: the code as a literal

The compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha1.X86_64.AvxBmi.compress

end VG
