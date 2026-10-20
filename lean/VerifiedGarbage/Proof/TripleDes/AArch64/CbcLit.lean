module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # Triple DES-CBC's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.cbcEncryptChained
materialize_code Impl.TripleDes.AArch64.cbcDecryptChained

end VG
