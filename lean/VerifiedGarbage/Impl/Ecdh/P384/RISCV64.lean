module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-! # P-384's check of a public point and public keys on RISC-V

ECDH, which calls `vg_p384_mul`, is in `Impl/Ecdsa/P384/RISCV64Window.lean`.
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p384_check_point`. -/
def checkP384 : Prog isa := Cfg.checkFn p384

/-- `vg_ec_p384_public_key`, with `[d]G` by the comb, `vg_p384_mul_g`. -/
def publicKeyP384 : Prog isa := Cfg.publicKeyFn p384 Comb.mulGP384Name Comb.mulGP384

end VG.Impl.Ecdh.RISCV64
