module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
meta import VerifiedGarbage.Impl.Camellia.X86_64.Ecb
public import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Camellia on X86_64: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again (seconds for the key expansion's).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

materialize_flat_code expandKeyCode := Impl.Camellia.X86_64.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.X86_64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.X86_64.ecb .decrypt

end VG.Proof.Camellia.X86_64
