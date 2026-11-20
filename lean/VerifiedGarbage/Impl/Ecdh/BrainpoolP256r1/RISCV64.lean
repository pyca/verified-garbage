module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb.BrainpoolP256r1
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # brainpoolP256r1's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_brainpoolp256r1_check_point`. -/
def checkBrainpoolP256r1 : Prog isa := Cfg.checkFn brainpoolp256r1

/-- `vg_ecdh_brainpoolp256r1`. -/
def ecdhBrainpoolP256r1 : Prog isa :=
  Cfg.ecdhFn brainpoolp256r1 "vg_brainpoolp256r1_check_point" "vg_brainpoolp256r1_mul" checkBrainpoolP256r1 mulBrainpoolP256r1

/-- `vg_ec_brainpoolp256r1_public_key`, with `[d]G` by the comb, `vg_brainpoolp256r1_mul_g`. -/
def publicKeyBrainpoolP256r1 : Prog isa :=
  Cfg.publicKeyFn brainpoolp256r1 Ecdsa.RISCV64.Comb.mulGBrainpoolP256r1Name Ecdsa.RISCV64.Comb.mulGBrainpoolP256r1

end VG.Impl.Ecdh.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.Ecdh.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdh_brainpoolp256r1` as emitted. -/
def exchangeBrainpoolP256r1 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.ecdhBrainpoolP256r1

/-- `vg_ec_brainpoolp256r1_public_key` as emitted. -/
def publicKeyBrainpoolP256r1 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.publicKeyBrainpoolP256r1

end VG.Impl.Ecdh.RISCV64.Fn
