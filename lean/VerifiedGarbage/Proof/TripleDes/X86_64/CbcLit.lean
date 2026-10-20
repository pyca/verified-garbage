module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Triple DES-CBC's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.cbcEncryptChained
materialize_code Impl.TripleDes.X86_64.cbcDecryptChained
materialize_code Impl.TripleDes.X86_64.cbcEncryptChainedI
materialize_code Impl.TripleDes.X86_64.cbcDecryptChainedI

end VG
