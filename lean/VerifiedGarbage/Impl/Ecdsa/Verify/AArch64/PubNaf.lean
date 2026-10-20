module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf

/-! Verification with `[v]Q` by the public width-five NAF (`PubNaf`), for
fields whose products are calls. -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.AArch64.Cfg
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64

/-- `[u]G` by the comb, `[v]Q` by the public NAF (with the doubling `dd` if
given), and their sum, into `R`. -/
def pubNafPoints (c : Impl.Ecdsa.AArch64.Cfg) (dd : Option (Prog isa) := none) : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (TCombCfg.comb c.combCfg true) <|
  .seq (.block (save c)) <| .seq (PubNaf.prep (c.winCfg PX PY) (c.sl V)) <|
  .seq (PubNaf.window (c.winCfg PX PY) dd) (sum c)

/-- `vg_ecdsa_<curve>_verify` with `pubNafPoints`. -/
def pubNafVerify (c : Impl.Ecdsa.AArch64.Cfg) (dd : Option (Prog isa) := none) : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (loadS c)) <| .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (pubNafPoints c dd) (tail c)

end VG.Impl.Ecdsa.Verify.AArch64.Cfg
