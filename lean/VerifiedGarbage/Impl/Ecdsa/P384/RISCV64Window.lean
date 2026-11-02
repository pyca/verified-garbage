module

public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA

/-! # `vg_p384_mul` on RISC-V, by four-bit windows, and ECDH

Apart from `Impl/Ecdsa/P384/RISCV64.lean` and `Impl/Ecdh/P384/RISCV64.lean`,
which the windows' imports (the comb, verification) import.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- P-384 as `vg_p384_mul`'s four-bit windows have it: the table at 4096, past
the slots, as verification's, and the complete addition for any `a`, from `a`
and `3 b`, which the contract's caller provides (`am3 := false`); the
doublings are those for `a = -3`. -/
def p384w : Cfg := { p384 with am3 := false }

/-- `vg_p384_mul`, by four-bit windows with the Jacobian doubling for `a = -3`
(`Impl/Ecdsa/RISCV64/WindowA.lean`). -/
def mulP384 : Prog isa := WindowA.Cfg.mulFn p384w Impl.Weierstrass.dblJ

end VG.Impl.Ecdsa.RISCV64

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Ecdsa.RISCV64

/-- `vg_ecdh_p384`. -/
def ecdhP384 : Prog isa := Cfg.ecdhFn p384 "vg_p384_check_point" "vg_p384_mul" checkP384 mulP384

end VG.Impl.Ecdh.RISCV64
