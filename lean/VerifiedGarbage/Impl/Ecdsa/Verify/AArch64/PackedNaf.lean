module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf

/-! Verification with `[v]Q` by the public width-five NAF (`PubNaf`), for
fields whose products are calls. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.Cfg
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64

/-- Compact table layout for nine-word verification: the table and cached
powers end at byte 8056 of the existing 8192-byte scratch allocation. -/
def packedNafQ (c : Impl.Ecdsa.AArch64.Cfg) : WinCfg :=
  { c.winCfg PX PY with tbl := slot c.n 71 }

/-- `[u]G` by the comb, `[v]Q` by the public NAF, and their sum, into `R`. -/
def packedNafPoints (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (TCombCfg.comb c.combCfg true) <|
  .seq (.block (save c)) <| .seq (PubNaf.prep (packedNafQ c) (c.sl V)) <|
  .seq (PubNaf.window (packedNafQ c)) (sum c)

/-- `vg_ecdsa_<curve>_verify` with `packedNafPoints`. -/
def packedNafVerify (c : Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (loadS c)) <| .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (packedNafPoints c) (tail c)

end VG.Impl.Ecdsa.Verify.AArch64.Cfg
