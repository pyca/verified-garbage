import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
import VerifiedGarbage.Proof.Framework.AArch64.TaintSymMono

/-!
# P-521 on AArch64: summaries of the shared code, for constant time

Signing, verification and public-key derivation all run the inversions
modulo `p` and `n` (`pPow`, `nPow`), and signing and key derivation run the
comb. Their constant-time checks are by `taintS [p521.tsym]`, so each of
these is analysed once here (`taint_summary`), from what every caller has
public there, keeping the registers it never writes, and the checks use
the summaries (`taint_decide_sum`) instead of analysing it again.
-/

namespace VG.Proof.P521.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64

taint_summary pPowSum : (taintS [p521.tsym]) (Taint.ofRegs [.x0]) (Cfg.pPow p521)
  keeping (Taint.ofRegs [.x0, .x20, .x26, .x27, .x28, .x30])
taint_summary nPowSum : (taintS [p521.tsym]) (Taint.ofRegs [.x0]) (Cfg.nPow p521)
  keeping (Taint.ofRegs [.x0, .x20, .x26, .x27, .x28, .x30])
taint_summary combSum : (taintS [p521.tsym]) (Taint.ofRegs [.x0])
  (Impl.Weierstrass.AArch64.TCombCfg.comb p521.combCfg) keeping (Taint.ofRegs [.x0, .x20])

end VG.Proof.P521.AArch64
