module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Seed.X86.Modes
meta import VerifiedGarbage.Impl.Seed.X86.Modes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# SEED-CBC on x86 (32-bit): the code as literals

The code of CBC encryption and decryption as literals
(`materialize_code`), which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build the code again.
Not flattened (`materialize_flat_code`): its unfolding measured slower here.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_code cbcEncryptChainedCode := Impl.Seed.X86.cbcEncryptChained
materialize_code cbcDecryptChainedCode := Impl.Seed.X86.cbcDecryptChained

end VG.Proof.Seed.X86
