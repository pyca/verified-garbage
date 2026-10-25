module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP2
public import VerifiedGarbage.Impl.P384.CombArithmetic

/-!
# ECDSA over P-384 on AArch64: the pipelined comb's checks

`jp2_checks`: what `tcombJP2_ok` needs of P-384's comb
(`Impl.P384.CombArithmetic.comb`), evaluated on its code (`JPChecks2`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P384

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass VG.Impl.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass

/-- The two-pass pipelined comb's code: its addition scalar code storing within
the working space, apart from the table its selection reads at `x30`. -/
theorem jp2_checks : JPChecks2 p384.combCfg 8192 Impl.P384.CombArithmetic.mixed :=
  ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end VG.Proof.Ecdsa.AArch64.P384
