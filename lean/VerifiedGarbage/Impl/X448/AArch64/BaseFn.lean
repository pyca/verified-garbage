import VerifiedGarbage.Impl.Ed448.AArch64.Point56

/-!
# X448 of the base point on AArch64: the function

`vg_x448_base` (`Base.lean`): the comb's setup, its steps, whose additions are calls of
`vg_ed448_r56_comb_add` (`Point56.combLoop`), `16 A + B` by calls of `vg_ed448_r56_point_add`
(`Point56.combineCall`), both of which Ed448's comb calls too, and the finish. In a module of its own, since `Point56.lean` imports `Base.lean`.
-/

namespace VG.Impl.X448.AArch64.Base

open VG.AArch64

def x448Base : Prog isa :=
  .seq setup <| .seq (Ed448.AArch64.Point56.combLoop 56) <| .seq Ed448.AArch64.Point56.combineCall finish

end VG.Impl.X448.AArch64.Base
