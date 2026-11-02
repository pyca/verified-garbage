module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Secp256k1Field
public import VerifiedGarbage.Spec.Secp256k1

/-! # secp256k1 on RISC-V: four-word field elements and scalars, and `vg_secp256k1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of secp256k1's `p`. -/
def secp256k1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.secp256k1p, Weierstrass.RISCV64.Secp256k1Field.mulFn,
    Weierstrass.RISCV64.Secp256k1Field.addFn, Weierstrass.RISCV64.Secp256k1Field.subFn⟩

/-- The functions of secp256k1's `n`. -/
def secp256k1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.secp256k1n, Weierstrass.RISCV64.Gen4.mulFn Spec.Secp256k1.n,
    Weierstrass.RISCV64.Gen4.addFn Spec.Secp256k1.n, Weierstrass.RISCV64.Gen4.subFn Spec.Secp256k1.n⟩

/-- secp256k1 as the code has it. -/
def secp256k1 : Cfg := { n := 4, C := Spec.Secp256k1.curve, FP := secp256k1Field }

/-- `vg_secp256k1_mul`. -/
def mulSecp256k1 : Prog isa := secp256k1.mulFn

end VG.Impl.Ecdsa.RISCV64
