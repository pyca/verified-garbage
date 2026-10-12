import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
import VerifiedGarbage.Impl.Blowfish.AArch64.Modes

/-! # Blowfish-CBC, -OFB and -CFB64's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

/-! The batches, whose registers `crypt`'s proof checks. -/

materialize_code Impl.Blowfish.AArch64.batchEnc
materialize_code Impl.Blowfish.AArch64.batchDec

/-! The functions. -/

materialize_code Impl.Blowfish.AArch64.cbcEncrypt
materialize_code Impl.Blowfish.AArch64.cbcDecrypt
materialize_code Impl.Blowfish.AArch64.ofb
materialize_code Impl.Blowfish.AArch64.cfbEncrypt
materialize_code Impl.Blowfish.AArch64.cfbDecrypt

end VG
