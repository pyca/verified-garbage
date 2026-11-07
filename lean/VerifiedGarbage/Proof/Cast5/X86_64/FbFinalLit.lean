module

public import VerifiedGarbage.Impl.Cast5.X86_64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Cast5.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # CAST5-CFB64's and CAST5-OFB's final functions' x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Cast5.X86_64.cfbEncryptFinal
materialize_code Impl.Cast5.X86_64.cfbDecryptFinal
materialize_code Impl.Cast5.X86_64.ofbFinal

end VG
