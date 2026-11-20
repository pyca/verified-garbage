module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # brainpoolP512r1's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_brainpoolp512r1_check_point`. -/
def checkBrainpoolP512r1 : Prog isa := Cfg.checkFn brainpoolp512r1

/-- `vg_ecdh_brainpoolp512r1`. -/
def ecdhBrainpoolP512r1 : Prog isa := Cfg.ecdhFn brainpoolp512r1 "vg_brainpoolp512r1_check_point" "vg_brainpoolp512r1_mul" checkBrainpoolP512r1 mulBrainpoolP512r1

/-- `vg_ec_brainpoolp512r1_public_key`, with `[d]G` by the ladder, `vg_brainpoolp512r1_mul`. -/
def publicKeyBrainpoolP512r1 : Prog isa := Cfg.publicKeyFn brainpoolp512r1 "vg_brainpoolp512r1_mul" mulBrainpoolP512r1

end VG.Impl.Ecdh.RISCV64

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the
caller-saved registers cleared but the 32 bits of its result (it uses no
stack), so that it returns without secret residue. -/

namespace VG.Impl.Ecdh.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdh_brainpoolp512r1` as emitted. -/
def exchangeBrainpoolP512r1 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.ecdhBrainpoolP512r1

/-- `vg_ec_brainpoolp512r1_public_key` as emitted. -/
def publicKeyBrainpoolP512r1 : Prog isa := Impl.Scrub.RISCV64.scrub 32 0 VG.Impl.Ecdh.RISCV64.publicKeyBrainpoolP512r1

end VG.Impl.Ecdh.RISCV64.Fn
