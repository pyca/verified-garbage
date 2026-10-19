module

import VerifiedGarbage.Proof.Idea.X86_64.Lit
meta import VerifiedGarbage.Proof.Idea.X86_64.Lit
public import VerifiedGarbage.Impl.Idea.X86_64.Modes
meta import VerifiedGarbage.Impl.Idea.X86_64.Modes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # IDEA-CBC, -OFB and -CFB64's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

/-! The block code the functions share, evaluated once. -/

materialize_value Impl.Idea.X86_64.cryptBlock

/-! The functions. -/

materialize_code Impl.Idea.X86_64.cbcEncryptChained
materialize_code Impl.Idea.X86_64.cbcDecryptChained
materialize_code Impl.Idea.X86_64.ofb
materialize_code Impl.Idea.X86_64.cfbEncrypt
materialize_code Impl.Idea.X86_64.cfbDecrypt

end VG
