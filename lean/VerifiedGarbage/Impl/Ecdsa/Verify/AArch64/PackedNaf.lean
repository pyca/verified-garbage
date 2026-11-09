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

end VG.Impl.Ecdsa.Verify.AArch64.Cfg
