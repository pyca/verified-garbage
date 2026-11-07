module

public import VerifiedGarbage.Impl.Blowfish.X86_64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Blowfish.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Blowfish-CFB64's final functions' x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.X86_64.cfbEncryptFinal
materialize_code Impl.Blowfish.X86_64.cfbDecryptFinal

end VG
