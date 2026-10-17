module

import VerifiedGarbage.Proof.Idea.AArch64.Lit
meta import VerifiedGarbage.Proof.Idea.AArch64.Lit
public import VerifiedGarbage.Impl.Idea.AArch64.Modes
meta import VerifiedGarbage.Impl.Idea.AArch64.Modes
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! # IDEA-CBC, -OFB and -CFB64's AArch64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Idea.AArch64.cryptBlock

/-! The functions. -/

materialize_code Impl.Idea.AArch64.cbcEncryptChained
materialize_code Impl.Idea.AArch64.cbcDecryptChained
materialize_code Impl.Idea.AArch64.ofb
materialize_code Impl.Idea.AArch64.cfbEncrypt
materialize_code Impl.Idea.AArch64.cfbDecrypt

end VG
