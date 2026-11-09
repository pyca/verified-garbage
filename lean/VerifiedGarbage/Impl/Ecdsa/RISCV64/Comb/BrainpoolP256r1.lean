module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Impl.BrainpoolP256r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-! # `vg_brainpoolp256r1_mul_g` on RISC-V: `[k]G` by the comb, for any `a` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Comb

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Ecdsa.RISCV64

/-- The table's symbol. -/
def brainpoolP256r1Sym : String := "VG_BRAINPOOLP256R1_COMB"

/-- The words of brainpoolP256r1's tables (`Impl/BrainpoolP256r1/CombTable7.lean`),
in Montgomery's form. -/
@[irreducible] def brainpoolP256r1CombWords : List (BitVec 64) :=
  tcombWords 4 (2 ^ 256) Spec.BrainpoolP256r1.curve.p Impl.BrainpoolP256r1.comb7

def brainpoolP256r1CombConsts : List (String × List (BitVec 64)) :=
  [(brainpoolP256r1Sym, brainpoolP256r1CombWords)]

/-- `vg_brainpoolp256r1_mul_g`. -/
def mulGBrainpoolP256r1 : Prog isa :=
  Cfg.combFnA brainpoolp256r1 brainpoolP256r1Sym Impl.BrainpoolP256r1.comb7Start

/-- The name of `vg_brainpoolp256r1_mul_g`. -/
def mulGBrainpoolP256r1Name : String := "vg_brainpoolp256r1_mul_g"

end VG.Impl.Ecdsa.RISCV64.Comb
