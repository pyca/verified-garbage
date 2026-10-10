import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.X448.AArch64.Fast

/-!
# X448 on AArch64: the code as a literal

Untrusted: everything here is checked by Lean. Materializing the code once
avoids rebuilding the unrolled arithmetic in each kernel-evaluated check.
The field operations, the butterfly and the AdvSIMD pair of products are
templates (`materialize_template`), each evaluated once with its offsets free.
-/

namespace VG.Proof.X448.AArch64.Fast.Lit
open VG.Impl.Curve448.AArch64

materialize_template mulT := Fast.mul
materialize_template sqrT := Fast.sqr
materialize_template subT := Fast.sub
materialize_template addSubT := Fast.addSub
materialize_template smallT := Fast.small
materialize_template copyT := copy
materialize_template butterflyT := Fast.butterfly
materialize_template mul2T := Neon.mul2

end VG.Proof.X448.AArch64.Fast.Lit

namespace VG

materialize_code Impl.X448.AArch64.Fast.x448

end VG
