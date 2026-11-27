module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

@[expose] public section

namespace VG.Impl.ChaCha20.AArch64

open VG.AArch64

/-- A stream implementation called by ChaCha20-Poly1305. -/
structure XorCallee where
  name : String
  code : Prog isa
  suffix : String
  /-- Whether the eight-block kernel uses SVE2 (`Mixed8.xor true`), and so
  does ChaCha20-Poly1305's own copy of it (`Stitch.bulk`). -/
  sve : Bool := false
  /-- The registers its code writes, of those the calling convention does not
  preserve: the cleanup of a function that calls it clears them with the
  function's own (`Impl.Scrub.AArch64.Clear.union`). -/
  clear : Impl.Scrub.AArch64.Clear

/-- A call of the stream, its destination (`x4`) set first: to its source
(`x1`) plus `x28` if `to` (ChaCha20-Poly1305's `open`, which keeps there the
distance from its source to its destination), else to its source (in place). -/
def XorCallee.callWith (c : XorCallee) (to : Bool) : Prog isa :=
  .seq (.block [if to then .add .x .x4 .x1 .x28 else Xor.mov .x4 .x1]) (.call c.name c.code)

/-- A call of the stream in place: its destination (`x4`) set to its source
(`x1`) first. -/
def XorCallee.inPlace (c : XorCallee) : Prog isa := c.callWith false

/-- The registers the eight-block kernel writes, with or without SVE2. -/
def XorCallee.mixed8Clear : Impl.Scrub.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24,
    .v25, .v26, .v27, .v28, .v29, .v30, .v31],
   [.v8, .v9]⟩

def XorCallee.scalar : XorCallee :=
  ⟨"vg_chacha20_xor", Xor.xor, "", false,
   ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
    [], []⟩⟩
def XorCallee.neon : XorCallee :=
  ⟨"vg_chacha20_xor_neon", Mixed8.xor false, "_neon", false, XorCallee.mixed8Clear⟩
def XorCallee.sve2 : XorCallee :=
  ⟨"vg_chacha20_xor_sve2", Mixed8.xor true, "_sve2", true, XorCallee.mixed8Clear⟩

end VG.Impl.ChaCha20.AArch64
