module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Camellia.X86.Modes
meta import VerifiedGarbage.Impl.Camellia.X86.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Camellia-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_flat_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code cbcEncryptChainedCode := Impl.Camellia.X86.cbcEncryptChained
materialize_flat_code cbcDecryptChainedCode := Impl.Camellia.X86.cbcDecryptChained

end VG.Proof.Camellia.X86
