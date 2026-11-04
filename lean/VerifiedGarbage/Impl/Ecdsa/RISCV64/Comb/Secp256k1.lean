module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64
public import VerifiedGarbage.Impl.Secp256k1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-! # `vg_secp256k1_mul_g` on RISC-V: `[k]G` by the comb, for any `a` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Comb

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Ecdsa.RISCV64

/-- The table's symbol. -/
def secp256k1Sym : String := "VG_SECP256K1_COMB"

/-- The words of secp256k1's tables (`Impl/Secp256k1/CombTable7.lean`),
in Montgomery's form. -/
@[irreducible] def secp256k1CombWords : List (BitVec 64) :=
  tcombWords 4 (2 ^ 256) Spec.Secp256k1.curve.p Impl.Secp256k1.secp256k1Comb7

def secp256k1CombConsts : List (String × List (BitVec 64)) :=
  [(secp256k1Sym, secp256k1CombWords)]

/-- `vg_secp256k1_mul_g`. -/
def mulGSecp256k1 : Prog isa :=
  Cfg.combFnA secp256k1 secp256k1Sym Impl.Secp256k1.secp256k1Comb7Start

/-- The name of `vg_secp256k1_mul_g`. -/
def mulGSecp256k1Name : String := "vg_secp256k1_mul_g"

end VG.Impl.Ecdsa.RISCV64.Comb
