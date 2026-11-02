module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-! # brainpoolP384r1's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_brainpoolp384r1_check_point`. -/
def checkBrainpoolP384r1 : Prog isa := Cfg.checkFn brainpoolp384r1

/-- `vg_ecdh_brainpoolp384r1`. -/
def ecdhBrainpoolP384r1 : Prog isa := Cfg.ecdhFn brainpoolp384r1 "vg_brainpoolp384r1_check_point" "vg_brainpoolp384r1_mul" checkBrainpoolP384r1 mulBrainpoolP384r1

/-- `vg_ec_brainpoolp384r1_public_key`, with `[d]G` by the ladder, `vg_brainpoolp384r1_mul`. -/
def publicKeyBrainpoolP384r1 : Prog isa := Cfg.publicKeyFn brainpoolp384r1 "vg_brainpoolp384r1_mul" mulBrainpoolP384r1

end VG.Impl.Ecdh.RISCV64
