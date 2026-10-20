module

public import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Argon2 compression with AVX-512 as a checked instruction literal -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.X86_64.Avx512.compress

end VG
