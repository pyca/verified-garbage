module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # Triple DES-OFB, -CFB64 and -CFB8's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.ofb
materialize_code Impl.TripleDes.AArch64.cfbEncrypt
materialize_code Impl.TripleDes.AArch64.cfbDecrypt
materialize_code Impl.TripleDes.AArch64.cfb8Encrypt
materialize_code Impl.TripleDes.AArch64.cfb8Decrypt

end VG
