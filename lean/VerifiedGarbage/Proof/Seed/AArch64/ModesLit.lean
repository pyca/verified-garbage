import VerifiedGarbage.Proof.Seed.AArch64.Lit
import VerifiedGarbage.Impl.Seed.AArch64.Modes

/-! # SEED-CBC, -OFB and -CFB128's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Seed.AArch64.cbcEncrypt
materialize_code Impl.Seed.AArch64.cbcDecrypt
materialize_code Impl.Seed.AArch64.ofb
materialize_code Impl.Seed.AArch64.cfbEncrypt
materialize_code Impl.Seed.AArch64.cfbDecrypt

end VG
