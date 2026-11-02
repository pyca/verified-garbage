module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P521.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-! # P-521's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p521_check_point`. -/
def checkP521 : Prog isa := Cfg.checkFn p521

/-- `vg_ecdh_p521`. -/
def ecdhP521 : Prog isa := Cfg.ecdhFn p521 "vg_p521_check_point" "vg_p521_mul" checkP521 mulP521

/-- `vg_ec_p521_public_key`, with `[d]G` by the ladder, `vg_p521_mul`. -/
def publicKeyP521 : Prog isa := Cfg.publicKeyFn p521 "vg_p521_mul" mulP521

end VG.Impl.Ecdh.RISCV64
