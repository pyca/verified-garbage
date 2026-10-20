module

public import VerifiedGarbage.Impl.Aes.X86.AesNi
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Aes.X86.AesNi
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

@[expose] public section

namespace VG.Impl.Aes.X86.AesNi
materialize_code expandKey
materialize_code ctr32
end VG.Impl.Aes.X86.AesNi
