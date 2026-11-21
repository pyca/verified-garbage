module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Impl.Scrub.RISCV64

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

/-! ## The public key as emitted

`vg_ec_p384_public_key`, then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. ECDH's is with ECDH, in
`Impl/Ecdsa/P384/RISCV64Window.lean`. -/

namespace VG.Impl.Ecdh.RISCV64.Fn

open VG.RISCV64

/-- `vg_ec_p384_public_key` as emitted. -/
def publicKeyP384 : Prog isa := Impl.Scrub.RISCV64.scrubAll 32 0 VG.Impl.Ecdh.RISCV64.publicKeyP384

end VG.Impl.Ecdh.RISCV64.Fn
