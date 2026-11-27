module

public import VerifiedGarbage.Impl.Ed448.AArch64.CombBase
public import VerifiedGarbage.Impl.Ed448.AArch64.Point56
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-!
# X448 of the base point on AArch64: the function

`vg_x448_base` (`Base.lean`): the comb's setup, the comb of 56 tables by a call of
`vg_ed448_r56_comb_base` (`CombBase.call 56`, which Ed448 calls for 57), `16 A + B` by calls of
`vg_ed448_r56_point_add` (`Point56.combineCall`), and the finish. In a
module of its own, since `CombBase.lean` imports `Base.lean`.
-/

@[expose] public section

namespace VG.Impl.X448.AArch64.Base

open VG.AArch64

def x448Base : Prog isa :=
  .seq setup <| .seq (Ed448.AArch64.CombBase.call 56) <| .seq Ed448.AArch64.Point56.combineCall finish

namespace Fn

/-- `vg_x448_base` as emitted: `x448Base`, then its cleanup, which clears
the registers it writes that the calling convention does not preserve
(`Impl.Scrub.AArch64.scrubAll`; it has no result and uses no stack), so
that it returns without secret residue. -/
def x448Base : Prog isa :=
  Scrub.AArch64.scrubAll 0 0
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
      .v26, .v27, .v28, .v29, .v30, .v31],
     [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]⟩
    Base.x448Base

end Fn

end VG.Impl.X448.AArch64.Base
