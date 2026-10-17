module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Impl.Camellia.X86.Ecb
meta import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Camellia on x86 (32-bit): the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code expandKeyCode := Impl.Camellia.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.X86.ecb .decrypt

end VG.Proof.Camellia.X86
