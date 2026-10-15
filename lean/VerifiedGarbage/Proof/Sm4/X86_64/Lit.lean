module

public import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
meta import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
public import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SM4 on X86_64: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

materialize_flat_code expandKeyCode := Impl.Sm4.X86_64.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.X86_64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.X86_64.ecb .decrypt

end VG.Proof.Sm4.X86_64
