module

public import VerifiedGarbage.Proof.Seed.AArch64.Lit
meta import VerifiedGarbage.Proof.Seed.AArch64.Lit
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
meta import VerifiedGarbage.Impl.Seed.AArch64.Modes
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # SEED-CBC, -OFB and -CFB128's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Seed.AArch64.cbcEncryptChained
materialize_code Impl.Seed.AArch64.cbcDecryptChained
materialize_code Impl.Seed.AArch64.ofb
materialize_code Impl.Seed.AArch64.cfbEncrypt
materialize_code Impl.Seed.AArch64.cfbDecrypt

end VG
