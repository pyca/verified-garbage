module

public import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# Poly1305 on x86-64 with AVX2: the code as a literal

`blocksAvx2` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
which the kernel checks once here and then evaluates in every check of the
code (constant time, `spSafe`, properties of every instruction).
-/

@[expose] public section

namespace VG

materialize_code Impl.Poly1305.X86_64.Avx2.blocksAvx2

end VG
