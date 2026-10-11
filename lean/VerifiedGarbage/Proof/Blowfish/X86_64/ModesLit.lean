import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
import VerifiedGarbage.Impl.Blowfish.X86_64.Modes

/-! # Blowfish-CBC, -OFB and -CFB64's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Blowfish.X86_64.cbcEncrypt
materialize_code Impl.Blowfish.X86_64.cbcDecrypt
materialize_code Impl.Blowfish.X86_64.ofb
materialize_code Impl.Blowfish.X86_64.cfbEncrypt
materialize_code Impl.Blowfish.X86_64.cfbDecrypt

end VG
