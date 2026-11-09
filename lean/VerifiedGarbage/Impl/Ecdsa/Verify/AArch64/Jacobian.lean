module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
public import VerifiedGarbage.Impl.Weierstrass.AArch64.NafPrep

/-! Public-scalar Jacobian multiplication for P-256 verification. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.Cfg
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64

/-- Signed five-bit recoding uses 52 digits and sixteen positive table entries. -/
def jacOffset : Nat := 16 * ((32^52-1)/31)

def jacWinCfg (c : Impl.Ecdsa.AArch64.Cfg) : WinCfg :=
  { c.winCfg PX PY with J := 52 }

/-- The fifth scalar word captures the carry from adding the signed-digit offset. -/
def jacWinPrep (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block (WinCfg.addConst 4 (c.sl V) c.winK jacOffset))
    (bits c.winK c.winBits 40)

end VG.Impl.Ecdsa.Verify.AArch64.Cfg
