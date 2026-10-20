module

public import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
meta import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
public import VerifiedGarbage.Impl.Camellia.X86_64.Fb
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Camellia.X86_64.Fb
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.TCB.X86_64.Target

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
