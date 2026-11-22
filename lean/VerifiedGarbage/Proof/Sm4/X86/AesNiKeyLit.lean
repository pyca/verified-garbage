module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.X86.AesNiKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# The SM4 key schedule by the AES S-box on x86 (32-bit): the code as a literal

The key schedule's code as a literal (`materialize_flat_code`), which the
checks of the whole function (`taint_decide`, `lit_decide`) read rather than
build the code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNiKey

materialize_flat_code expandKeyCode := Impl.Sm4.X86.AesNiKey.expandKey

end VG.Proof.Sm4.X86.AesNiKey
