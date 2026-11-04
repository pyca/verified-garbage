module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb.Secp256k1
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-! # secp256k1's check of a public point, ECDH and public keys on RISC-V -/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_secp256k1_check_point`. -/
def checkSecp256k1 : Prog isa := Cfg.checkFn secp256k1

/-- `vg_ecdh_secp256k1`. -/
def ecdhSecp256k1 : Prog isa :=
  Cfg.ecdhFn secp256k1 "vg_secp256k1_check_point" "vg_secp256k1_mul" checkSecp256k1 mulSecp256k1

/-- `vg_ec_secp256k1_public_key`, with `[d]G` by the comb, `vg_secp256k1_mul_g`. -/
def publicKeySecp256k1 : Prog isa :=
  Cfg.publicKeyFn secp256k1 Ecdsa.RISCV64.Comb.mulGSecp256k1Name Ecdsa.RISCV64.Comb.mulGSecp256k1

end VG.Impl.Ecdh.RISCV64
