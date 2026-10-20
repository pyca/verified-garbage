module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

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
