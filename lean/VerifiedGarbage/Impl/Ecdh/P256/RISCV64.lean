module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Spec.Weierstrass.CheckPoint

/-! # P-256's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p256_check_point`. -/
def checkP256 : Prog isa := Cfg.checkFn p256

/-- `vg_ecdh_p256`. -/
def ecdhP256 : Prog isa :=
  Cfg.ecdhFn p256 Spec.Weierstrass.CheckPoint.p256.checkApi.name Spec.Weierstrass.Mul.p256.mulApi.name checkP256
    mulP256

/-- `vg_ec_p256_public_key`, with `[d]G` by the comb, `vg_p256_mul_g`. -/
def publicKeyP256 : Prog isa := Cfg.publicKeyFn p256 Comb.mulGP256Name Comb.mulGP256

end VG.Impl.Ecdh.RISCV64
