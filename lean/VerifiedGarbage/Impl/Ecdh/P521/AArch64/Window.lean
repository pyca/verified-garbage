module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Point

/-! # P-521 ECDH with a bounded scalar and Jacobian accumulator

The original scalar remains in D for the final range check. Mask only its
working copy in K to 521 bits, so invalid scalars still execute safely and
are rejected. The signed recoding needs 131 windows, rather than the 145
needed for arbitrary nine-word integers. Normalize the eight peer multiples
with one inversion; keep the accumulator Jacobian and use mixed additions,
with the existing complete formula on the last window.
-/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.P521Window

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont
open VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64

abbrev c := p521

def config (C : VG.Impl.Ecdsa.AArch64.Cfg) : VG.Impl.Weierstrass.WinCfg :=
  { C.winCfg PX PY with J := 131, bits := 3304 }

abbrev cfg := config c

def maskK : List Instr :=
  [ld .x3 (c.sl K+64), .movz .x .x4 511 0,
    .logic .and .x .x3 .x3 .x4, st .x3 (c.sl K+64)]

def prepFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block (WinCfg.addConst C.n (C.sl K) 3944 (WinCfg.offset 131)))
    (bits 3944 3304 (8*(C.n+1)))

/-- The window's doublings, with their products inline. -/
def doubleBodiesFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa × Prog isa :=
  let k := config C
  (P521.double k.M k.S k.R k.D, P521.double k.M k.S k.D k.R)

/-- Preserve the caller's link in an unused vector lane while calling a straight-line doubling. -/
def callDouble (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v31 1 .x30)])
    (.seq (.call name body) (.block [.umov .x .x30 .v31 1]))

/-- Both window steps use the same two doubling bodies. -/
def doublesFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa × Prog isa :=
  let dd := doubleBodiesFor C
  (callDouble "vg_p521_window_double_rd" dd.1, callDouble "vg_p521_window_double_dr" dd.2)

/-- The window's mixed addition, with its products inline. -/
def maddFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  let k := config C
  P521.madd k.M k.S k.R k.E k.D

def coreFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (prepFor C) (WinCfg.windowJ (config C) (Cfg.invJ C) C.padd (some (doublesFor C)) (some (maddFor C)))

abbrev core := coreFor c

def multiply : Prog isa := .seq (.block maskK) core

def code : Prog isa := Cfg.exchangeWith c multiply

end VG.Impl.Ecdh.AArch64.P521Window
