module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Cast5.X86.Modes
meta import VerifiedGarbage.Impl.Cast5.X86.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# CAST5-CBC, -OFB and -CFB64 on x86 (32-bit): the code as literals

The code of the modes over CAST5's core as literals (`materialize_flat_code`),
which the checks of the whole functions (`taint_decide`, `lit_decide`) read
rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

materialize_flat_code cbcEncryptCode := Impl.Cast5.X86.Modes.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Cast5.X86.Modes.cbcDecrypt
materialize_flat_code ofbCode := Impl.Cast5.X86.Modes.ofb
materialize_flat_code cfbEncryptCode := Impl.Cast5.X86.Modes.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Cast5.X86.Modes.cfbDecrypt

end VG.Proof.Cast5.X86
