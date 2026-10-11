import VerifiedGarbage.Impl.Ed448.AArch64.CombBase

/-!
# X448 of the base point on AArch64: the function

`vg_x448_base` (`Base.lean`): the comb's setup, the comb of 56 tables by a call of
`vg_ed448_r56_comb_base` (`CombBase.call 56`, which Ed448 calls for 57), `16 A + B` by calls of
`vg_ed448_r56_point_add` (`Point56.combineCall`), and the finish. In a
module of its own, since `CombBase.lean` imports `Base.lean`.
-/

namespace VG.Impl.X448.AArch64.Base

open VG.AArch64

def x448Base : Prog isa :=
  .seq setup <| .seq (Ed448.AArch64.CombBase.call 56) <| .seq Ed448.AArch64.Point56.combineCall finish

end VG.Impl.X448.AArch64.Base
