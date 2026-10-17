module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! # Triple DES-CBC's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.cbcEncryptChained
materialize_code Impl.TripleDes.X86_64.cbcDecryptChained
materialize_code Impl.TripleDes.X86_64.cbcEncryptChainedI
materialize_code Impl.TripleDes.X86_64.cbcDecryptChainedI

end VG
