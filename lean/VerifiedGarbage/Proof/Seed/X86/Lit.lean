module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Seed.X86.Ecb
meta import VerifiedGarbage.Impl.Seed.X86.Ecb
public import VerifiedGarbage.Impl.Seed.X86.ExpandKey
meta import VerifiedGarbage.Impl.Seed.X86.ExpandKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# SEED on x86 (32-bit): the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_flat_code expandKeyCode := Impl.Seed.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Seed.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Seed.X86.ecb .decrypt

end VG.Proof.Seed.X86
