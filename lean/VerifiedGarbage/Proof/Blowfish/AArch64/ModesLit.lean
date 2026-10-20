module

public import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Blowfish-CBC, -OFB and -CFB64's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

/-! The batches, whose registers `crypt`'s proof checks. -/

materialize_code Impl.Blowfish.AArch64.batchEnc
materialize_code Impl.Blowfish.AArch64.batchDec

/-! The functions. -/

materialize_code Impl.Blowfish.AArch64.cbcEncryptChained
materialize_code Impl.Blowfish.AArch64.cbcDecryptChained
materialize_code Impl.Blowfish.AArch64.ofb
materialize_code Impl.Blowfish.AArch64.cfbEncrypt
materialize_code Impl.Blowfish.AArch64.cfbDecrypt

end VG
