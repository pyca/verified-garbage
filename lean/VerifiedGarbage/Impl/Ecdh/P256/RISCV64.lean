module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64

/-! # P-256's check of a public point on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_p256_check_point`. -/
def checkP256 : Prog isa := Cfg.checkFn p256

end VG.Impl.Ecdh.RISCV64
