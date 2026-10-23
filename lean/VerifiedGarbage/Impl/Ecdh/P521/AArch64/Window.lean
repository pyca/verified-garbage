module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64

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

abbrev prep := prepFor c

def doublesFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa × Prog isa :=
  let k := config C
  (fprogB k.M (VG.Impl.Weierstrass.dblJS k.S k.R k.D),
   fprogB k.M (VG.Impl.Weierstrass.dblJS k.S k.D k.R))

abbrev doubles := doublesFor c

def coreFor (C : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (prepFor C) (WinCfg.windowJ (config C) (Cfg.invJ C) C.padd (some (doublesFor C)))

abbrev core := coreFor c

def multiply : Prog isa := .seq (.block maskK) core

def code : Prog isa := Cfg.exchangeWith c multiply

end VG.Impl.Ecdh.AArch64.P521Window
