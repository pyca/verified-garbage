module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Blowfish.X86.Modes
meta import VerifiedGarbage.Impl.Blowfish.X86.Modes
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Blowfish's modes on x86 (32-bit): the code as literals

The code of CBC, OFB and CFB64 as literals (`materialize_flat_code`), which
the checks of the whole functions (`taint_decide`, `lit_decide`) read rather
than build the code again.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

materialize_flat_code cbcEncryptChainedCode := Impl.Blowfish.X86.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Blowfish.X86.cbcDecryptChained
materialize_flat_code ofbCode := Impl.Blowfish.X86.ofb
materialize_flat_code cfbEncryptCode := Impl.Blowfish.X86.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Blowfish.X86.cfbDecrypt

end VG.Proof.Blowfish.X86
