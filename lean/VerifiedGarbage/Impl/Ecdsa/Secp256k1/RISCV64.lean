module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Impl.Weierstrass.JacMul
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Secp256k1Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Secp256k1Order
public import VerifiedGarbage.Spec.Secp256k1

/-! # secp256k1 on RISC-V: four-word field elements and scalars, and `vg_secp256k1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of secp256k1's `p`. -/
def secp256k1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.secp256k1p, Weierstrass.RISCV64.Secp256k1Field.mulFn,
    Weierstrass.RISCV64.Secp256k1Field.addFn, Weierstrass.RISCV64.Secp256k1Field.subFn,
    Weierstrass.RISCV64.Secp256k1Field.mulFnA, Weierstrass.RISCV64.Secp256k1Field.addFnA,
    Weierstrass.RISCV64.Secp256k1Field.subFnA⟩

/-- The functions of secp256k1's `n`. -/
def secp256k1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.secp256k1n, Weierstrass.RISCV64.Secp256k1Order.mulFn,
    Weierstrass.RISCV64.Secp256k1Order.addFn, Weierstrass.RISCV64.Secp256k1Order.subFn,
    Weierstrass.RISCV64.Secp256k1Order.mulFnA, Weierstrass.RISCV64.Secp256k1Order.addFnA,
    Weierstrass.RISCV64.Secp256k1Order.subFnA⟩

/-- secp256k1 as the code has it: `a = 0`, so verification adds by the
complete addition for any `a` (`am3 := false`). -/
def secp256k1 : Cfg := { n := 4, C := Spec.Secp256k1.curve, FP := secp256k1Field, am3 := false }

/-- `vg_secp256k1_mul`, by four-bit windows with the Jacobian doubling for `a = 0`
(`Impl/Ecdsa/RISCV64/WindowA.lean`). -/
def mulSecp256k1 : Prog isa := WindowA.Cfg.mulFn secp256k1 Impl.Weierstrass.dblJ0

end VG.Impl.Ecdsa.RISCV64
