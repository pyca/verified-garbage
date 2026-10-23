module

public import VerifiedGarbage.Impl.Idea.PPC64LE.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Idea.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # IDEA's modes on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_value Impl.Idea.PPC64LE.cryptBlock
materialize_code Impl.Idea.PPC64LE.cbcEncryptChained
materialize_code Impl.Idea.PPC64LE.cbcDecryptChained
materialize_code Impl.Idea.PPC64LE.ofb
materialize_code Impl.Idea.PPC64LE.cfbEncrypt
materialize_code Impl.Idea.PPC64LE.cfbDecrypt

end VG
