module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # Triple DES-OFB, -CFB64 and -CFB8's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.ofb
materialize_code Impl.TripleDes.X86_64.cfbEncrypt
materialize_code Impl.TripleDes.X86_64.cfbDecrypt
materialize_code Impl.TripleDes.X86_64.cfb8Encrypt
materialize_code Impl.TripleDes.X86_64.cfb8Decrypt
materialize_code Impl.TripleDes.X86_64.ofbI
materialize_code Impl.TripleDes.X86_64.cfbEncryptI
materialize_code Impl.TripleDes.X86_64.cfbDecryptI
materialize_code Impl.TripleDes.X86_64.cfb8EncryptI
materialize_code Impl.TripleDes.X86_64.cfb8DecryptI

end VG
