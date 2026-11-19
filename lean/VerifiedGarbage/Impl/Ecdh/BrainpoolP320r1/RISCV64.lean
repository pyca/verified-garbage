module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-! # brainpoolP320r1's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_brainpoolp320r1_check_point`. -/
def checkBrainpoolP320r1 : Prog isa := Cfg.checkFn brainpoolp320r1

/-- `vg_ecdh_brainpoolp320r1`. -/
def ecdhBrainpoolP320r1 : Prog isa := Cfg.ecdhFn brainpoolp320r1 "vg_brainpoolp320r1_check_point" "vg_brainpoolp320r1_mul" checkBrainpoolP320r1 mulBrainpoolP320r1

/-- `vg_ec_brainpoolp320r1_public_key`, with `[d]G` by the ladder, `vg_brainpoolp320r1_mul`. -/
def publicKeyBrainpoolP320r1 : Prog isa := Cfg.publicKeyFn brainpoolp320r1 "vg_brainpoolp320r1_mul" mulBrainpoolP320r1

end VG.Impl.Ecdh.RISCV64
