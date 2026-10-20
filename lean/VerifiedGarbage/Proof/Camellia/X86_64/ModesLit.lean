module

public import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
public import VerifiedGarbage.Impl.Camellia.X86_64.Fb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
meta import VerifiedGarbage.Impl.Camellia.X86_64.Fb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Camellia-CBC, -OFB, -CFB128 and -CTR's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Camellia.X86_64.cbcEncryptChained
materialize_code Impl.Camellia.X86_64.cbcDecryptChained
materialize_code Impl.Camellia.X86_64.ofb
materialize_code Impl.Camellia.X86_64.cfbEncrypt
materialize_code Impl.Camellia.X86_64.cfbDecrypt
materialize_code Impl.Camellia.X86_64.ctr

end VG
