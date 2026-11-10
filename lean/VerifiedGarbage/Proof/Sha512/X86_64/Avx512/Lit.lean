module

public import VerifiedGarbage.Impl.Sha512.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha512.X86_64.Avx512
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# SHA-512 with AVX-512VL on x86-64: the code as literals

The compression functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.X86_64.Avx512.compress
materialize_code Impl.Sha512.X86_64.Avx512.compress2

end VG
