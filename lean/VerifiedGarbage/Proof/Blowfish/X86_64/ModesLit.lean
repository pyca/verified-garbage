module

public import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Blowfish-CBC, -OFB and -CFB64's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.X86_64.cbcEncryptChained
materialize_code Impl.Blowfish.X86_64.cbcDecryptChained
materialize_code Impl.Blowfish.X86_64.ofb
materialize_code Impl.Blowfish.X86_64.cfbEncrypt
materialize_code Impl.Blowfish.X86_64.cfbDecrypt

end VG
