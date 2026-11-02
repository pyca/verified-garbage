module

public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
public import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet

/-!
# Operations of `vg_rsa_keygen_key` on RISC-V, beyond the key routines'

On the working space of the RSA key operations (`Impl/Rsa/RISCV64/KeyWs.lean`),
whose slots are words holding 0 or 1:

* slot operations: `notS d a` (`d := 1 - a`), `andNotS d a b`
  (`d := (1 - a) b`) and `selS d a b c` (`d := c ? b : a`);
* `setLow j x`: the low word of `[j]` := `x`;
* `mulTo o a b`: `[o] := [a] [b]` modulo `2^(64 w)`, by `[o] := 0` and the
  schoolbook product of `vg_rsa_recover_primes_det` (`RecoverDet.mulLow`);
* `invOf a m k`: the batched divsteps (`Impl/Rsa/RISCV64/InvBatch.lean`) on
  `[a]` and the odd `[m]`, `k` setting the digit count in `s8`:
  `gcd([a], [m])` in array 1 and the inverse in array 3.

They use `t0`–`t6` and `a4` as the key routines do; `mulTo` also `a2`, `a3`,
`a6` and `s8`, and `invOf` `a5`, `a7`, `s7` and `s8`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Key

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys

/-- The array holding zero, which the inverse leaves (`InvBatch.invArrs` has not 10). -/
def aZero : Nat := 10

/-- The slot `d` := 1 - the slot `a`. -/
def notS (d a : Nat) : List Instr :=
  [.load .d .t5 .s11 a, .logicImm .xor .t5 .t5 1, .store .d .t5 .s11 d]

/-- The slot `d` := (1 - the slot `a`) and the slot `b`. -/
def andNotS (d a b : Nat) : List Instr :=
  [.load .d .t5 .s11 a, .logicImm .xor .t5 .t5 1, .load .d .t6 .s11 b,
    .logic .and .t5 .t5 .t6, .store .d .t5 .s11 d]

/-- The slot `d` := the slot `b` if the slot `c` is 1, the slot `a` if it is 0:
`a ^ ((a ^ b) & c)`. -/
def selS (d a b c : Nat) : List Instr :=
  [.load .d .t5 .s11 a, .load .d .t6 .s11 b, .logic .xor .t6 .t6 .t5, .load .d .t4 .s11 c,
    .logic .and .t6 .t6 .t4, .logic .xor .t5 .t5 .t6, .store .d .t5 .s11 d]

/-- The low word of `[j]` := `x`. -/
def setLow (j : Nat) (x : Int) : List Instr := ptr .t0 j ++ [.li .t5 x, .store .d .t5 .t0 0]

/-- `[o] := [a] [b]` modulo `2^(64 w)`. -/
def mulTo (o a b : Nat) : Prog isa := .seq (copy o aZero) (VG.Impl.Rsa.RISCV64.RecoverDet.mulLow o a b)

/-- `[a]` modulo the odd `[m]` by the batched divsteps
(`Impl/Rsa/RISCV64/InvBatch.lean`): `x = [a]` in array 0, `m = [m]` in array
8, `n` the instructions setting the digit count in `s8`; `gcd([a], [m])` in
array 1 and the inverse in array 3. -/
def invOf (a m : Nat) (n : List Instr) : Prog isa := seqs [
  copy VG.Impl.Rsa.RISCV64.InvBatch.aX a, copy VG.Impl.Rsa.RISCV64.InvBatch.aMin m, .block n,
  VG.Impl.Rsa.RISCV64.InvBatch.inverse]

end VG.Impl.RsaKeyGen.RISCV64.Key
