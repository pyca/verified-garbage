module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

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
