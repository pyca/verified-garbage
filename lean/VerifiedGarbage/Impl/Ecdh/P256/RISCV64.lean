module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # P-256's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p256_check_point`. -/
def checkP256 : Prog isa := Cfg.checkFn p256

/-- `vg_ecdh_p256`, with `[d]P` by windows (`Impl/Ecdsa/RISCV64/Window.lean`). -/
def ecdhP256 : Prog isa :=
  Cfg.ecdhFn p256 "vg_p256_check_point" "vg_p256_mul" checkP256
    Window.mulP256

/-- `vg_ec_p256_public_key`, with `[d]G` by the comb, `vg_p256_mul_g`. -/
def publicKeyP256 : Prog isa := Cfg.publicKeyFn p256 Comb.mulGP256Name Comb.mulGP256

end VG.Impl.Ecdh.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.Ecdh.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdh_p256` as emitted. -/
def exchangeP256 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.ecdhP256

/-- `vg_ec_p256_public_key` as emitted. -/
def publicKeyP256 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.publicKeyP256

end VG.Impl.Ecdh.RISCV64.Fn
