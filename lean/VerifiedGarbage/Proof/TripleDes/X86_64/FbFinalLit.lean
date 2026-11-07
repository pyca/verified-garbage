module

public import VerifiedGarbage.Impl.TripleDes.X86_64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Triple DES-CFB64's final functions' x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.cfbEncryptFinal
materialize_code Impl.TripleDes.X86_64.cfbDecryptFinal
materialize_code Impl.TripleDes.X86_64.cfbEncryptFinalI
materialize_code Impl.TripleDes.X86_64.cfbDecryptFinalI

end VG
