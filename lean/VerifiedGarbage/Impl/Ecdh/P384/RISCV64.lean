module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-! # P-384's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p384_check_point`. -/
def checkP384 : Prog isa := Cfg.checkFn p384

/-- `vg_ecdh_p384`. -/
def ecdhP384 : Prog isa := Cfg.ecdhFn p384 "vg_p384_check_point" "vg_p384_mul" checkP384 mulP384

/-- `vg_ec_p384_public_key`, with `[d]G` by the ladder, `vg_p384_mul`. -/
def publicKeyP384 : Prog isa := Cfg.publicKeyFn p384 "vg_p384_mul" mulP384

end VG.Impl.Ecdh.RISCV64
