module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P521.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.CombU
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # P-521's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p521_check_point`. -/
def checkP521 : Prog isa := Cfg.checkFn p521

/-- `vg_ecdh_p521`. -/
def ecdhP521 : Prog isa := Cfg.ecdhFn p521 "vg_p521_check_point" "vg_p521_mul" checkP521 mulP521

/-- `vg_ec_p521_public_key`, with `[d]G` by the comb, `vg_p521_mul_g`. -/
def publicKeyP521 : Prog isa := Cfg.publicKeyFn p521 CombU.mulGP521Name CombU.mulGP521

end VG.Impl.Ecdh.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.Ecdh.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdh_p521` as emitted. -/
def exchangeP521 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.ecdhP521

/-- `vg_ec_p521_public_key` as emitted. -/
def publicKeyP521 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.publicKeyP521

end VG.Impl.Ecdh.RISCV64.Fn
