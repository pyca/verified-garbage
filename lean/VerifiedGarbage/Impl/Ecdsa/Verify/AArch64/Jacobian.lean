module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
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

/-- Both multiplication loops retain Jacobian coordinates until their final conversions. -/
def jacPoints (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8*c.n)) <|
  .seq (Jacobian.jacComb c.combCfg) <|
  .seq (.block (save c)) <|
  .seq (jacWinPrep c) <|
  .seq (Jacobian.jacWindow (jacWinCfg c) 5) (sum c)

/-- The existing verifier prefix and final checks around the public Jacobian loops. -/
def jacVerify (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block (args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (jacPoints c) (tail c)


/-- A public scalar is recoded into 257 signed NAF bytes. -/
def nafWinPrep (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  Naf.prep (jacWinCfg c) (c.sl V)

/-- Sparse odd-multiple lookup for the public variable-point multiplication. -/
def nafPoints (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8*c.n)) <|
  .seq (Jacobian.jacComb c.combCfg) <|
  .seq (.block (save c)) <|
  .seq (nafWinPrep c) <|
  .seq (Naf.window (jacWinCfg c)) (sum c)

/-- The existing verifier checks around the sparse public-scalar multiplication. -/
def nafVerify (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block (args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (nafPoints c) (tail c)

end VG.Impl.Ecdsa.Verify.AArch64.Cfg
