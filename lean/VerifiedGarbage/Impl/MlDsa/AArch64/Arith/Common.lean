module

public import VerifiedGarbage.Impl.MlKem.AArch64.Compress
public import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-DSA on AArch64: arithmetic modulo `q`

Pieces of code that the ML-DSA arithmetic functions share, for
`q = 8380417 < 2²³`. Coefficients are `u32`s, loaded with `ldr w` (which
zero-extends them) and computed on in 64-bit registers, where no
intermediate value wraps. The model has no flags, conditional select,
`umulh` or register-offset addressing (`TCB/AArch64/Isa.lean`): pointers
advance by an immediate, loops count down to zero (`cbnz`), and conditional
steps use the sign bit of a 64-bit difference.

* `csub d t qr` (ML-KEM's, `Impl/MlKem/AArch64/Basic.lean`): `d ← d mod q`
  for `d < 2q`, with `q` in `qr`: `d - q`, plus `q` times its sign bit;
* `storeTab t n b`: the table `t 0, …, t (n - 1)` of constants stored as
  `u32`s at `b` (in the working space), through `x9`.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Arith

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov csub movImm)

/-- `q = 8380417`. -/
def qNat : Nat := 8380417

/-- A word `v` into `d`: `movz` of its low half, then `movk` of its high half. -/
def movW (d : Reg) (v : BitVec 32) : List Instr :=
  [.movz .w d (v.extractLsb' 0 16) 0, .movk .w d (v.extractLsb' 16 16) 1]

/-- `t i` to `[b + 4i]`, through `x9`. -/
def tabStep (t : Nat → Nat) (b : Reg) (i : Nat) : List Instr :=
  movW .x9 (BitVec.ofNat 32 (t i)) ++ ([.str .w .x9 b (4 * i)] : List Instr)

/-- The table `t 0, …, t (n - 1)` at `b`. -/
def storeTab (t : Nat → Nat) (n : Nat) (b : Reg) : List Instr := (List.range n).flatMap (tabStep t b)

end VG.Impl.MlDsa.AArch64.Arith
