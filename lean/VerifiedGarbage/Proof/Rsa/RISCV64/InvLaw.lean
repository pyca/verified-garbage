module

public import VerifiedGarbage.Proof.Rsa.RISCV64.IbOps

/-! # The contract of the batched inverse on RISC-V

`InvLaw`: what `Impl/Rsa/RISCV64/InvBatch.lean`'s `inverse` and `gcd` do, for
their callers to use without importing the algebra of their proofs
(`IbInverse.lean`'s `inverse_ok` and `gcd_ok`); the registration supplies the
instance (`Instances.lean`).

From `x` in array 0 and an odd `m` in array 8, both below `2^(32 n)` for `n`
in `s8` (`1 ≤ n ≤ 2 w`), `inverse` leaves `gcd(x, m)` in array 1 and, for
`m > 1`, `y < m` with `y x ≡ gcd(x, m) (mod m)` in array 3; `gcd` leaves only
the GCD. Each writes only the arrays `invArrs` (`gcdArrs`) and the registers
`invRegs`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys

/-- The arrays `inverse` writes. -/
abbrev invArrs : List Nat := [1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13]

/-- The arrays `gcd` writes. -/
abbrev gcdArrs : List Nat := [1, 2, 4, 5, 6, 7, 9, 11, 12]

/-- The registers `inverse` and `gcd` change. -/
abbrev invRegs : List Reg := .s7 :: kRegs

end VG.Proof.Rsa.RISCV64.InvBatch

namespace VG.Proof.Rsa.RISCV64

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Proof.Rsa.RISCV64.InvBatch

class InvLaw : Prop where
  inverse_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
      (hx : num s.mem B w Impl.Rsa.RISCV64.InvBatch.aX = x) (hxn : x < 2 ^ (32 * n))
      (hm : num s.mem B w Impl.Rsa.RISCV64.InvBatch.aMin = m) (hmn : m < 2 ^ (32 * n))
      (hodd : m % 2 = 1) :
      WP isa Impl.Rsa.RISCV64.InvBatch.inverse s fun t => Ws t B Z w N ∧
        Keys.Frame B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
        (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
          (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m)
  gcd_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
      (hx : num s.mem B w Impl.Rsa.RISCV64.InvBatch.aX = x) (hxn : x < 2 ^ (32 * n))
      (hm : num s.mem B w Impl.Rsa.RISCV64.InvBatch.aMin = m) (hmn : m < 2 ^ (32 * n))
      (hodd : m % 2 = 1) :
      WP isa Impl.Rsa.RISCV64.InvBatch.gcd s fun t => Ws t B Z w N ∧
        Keys.Frame B w gcdArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
        (1 < m → num t.mem B w 1 = Nat.gcd x m)

end VG.Proof.Rsa.RISCV64
