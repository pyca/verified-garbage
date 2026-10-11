import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Impl.Seed.X86_64.Modes

/-! # SEED-CBC, -OFB and -CFB128's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Seed.X86_64.cbcEncrypt
materialize_code Impl.Seed.X86_64.cbcDecrypt
materialize_code Impl.Seed.X86_64.ofb
materialize_code Impl.Seed.X86_64.cfbEncrypt
materialize_code Impl.Seed.X86_64.cfbDecrypt

end VG
