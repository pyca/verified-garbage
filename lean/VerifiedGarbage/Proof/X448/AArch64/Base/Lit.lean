import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.X448.AArch64.Base

/-!
# X448 of the base point on AArch64: the code as a literal

Untrusted: everything here is checked by Lean. Materializing the code once
avoids rebuilding its tables' immediates and the unrolled arithmetic in each
kernel-evaluated check.
-/

namespace VG

materialize_code Impl.X448.AArch64.Base.x448Base

end VG
