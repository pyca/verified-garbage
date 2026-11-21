module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-!
# ECDH on P-521 on AArch64, as emitted

`vg_ecdh_p521`: `exchange` (`Code.lean`), then its cleanup
(`Impl.Scrub.AArch64.scrubAll`), which clears the registers it writes that
the calling convention does not preserve, but its 32-bit result, and zeroes
its 3456 bytes of stack, so that it returns without secret residue.
-/

-- separate module: `Code.lean` has 22 importers, which this definition, read only by its theorem, would rebuild

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.P521Native.Fn

open VG.AArch64

/-- `vg_ecdh_p521` as emitted: `exchange`, then its cleanup. -/
def exchange : Prog isa :=
  Scrub.AArch64.scrubAll 3456 32
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v24, .v25, .v26,
      .v28, .v29, .v31], []⟩
    P521Native.exchange

end VG.Impl.Weierstrass.AArch64.P521Native.Fn
