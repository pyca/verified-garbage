module

public import VerifiedGarbage.Impl.Idea.X86.Modes
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Idea.X86.Modes
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# IDEA's modes on x86 (32-bit): the code as literals

The code of CBC, OFB and CFB64 as literals (`materialize_flat_code`), which
the checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG.Proof.Idea.X86

materialize_flat_code cbcEncryptChainedCode := Impl.Idea.X86.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Idea.X86.cbcDecryptChained
materialize_flat_code ofbCode := Impl.Idea.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Idea.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Idea.X86.cfbDecrypt

end VG.Proof.Idea.X86
