module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Sm4.X86.Modes
meta import VerifiedGarbage.Impl.Sm4.X86.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# SM4-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code cbcEncryptCode := Impl.Sm4.X86.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Sm4.X86.cbcDecrypt

end VG.Proof.Sm4.X86
