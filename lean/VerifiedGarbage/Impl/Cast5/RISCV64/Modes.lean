module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Cast5.RISCV64

/-!
# CAST5's modes on RISC-V

`dirCore up n`: ECB's block function (`crypt`), inlined, as a core for the
modes (`Impl/Modes/RISCV64/Seq.lean`), encrypting (`up`) or decrypting the
block in its buffer (slot 6 of the mode's frame) in place with `n` rounds,
as on PPC64LE (`Impl/Cast5/PPC64LE/Modes.lean`). It reads the subkeys where
the caller passed them, through `a0`, which the block function keeps. The
block function writes `s0`–`s10`, among them the mode's `s1`–`s4`, but not
`a3`, `a4`, `s11` or `ra`: the core saves our caller's `s0`, `s5`–`s11` and
`ra` in slots 7 to 15, keeps the mode's `s1`–`s4` in `a3`, `a4`, `s11` and
`ra` meanwhile, rather than in memory, so they stay public, and restores
them all after. Each block, it forms the buffer's address, the table's
(`lla`) and the count of rounds in the registers the block function reads
them from. 16 slots in all.

The functions take the number of rounds as their second argument, which the
modes' code does not: `modeFn m` moves `rounds` to `t0` and the others down
to the modes' registers (schedule = a0, iv = a1, data = a2, n = a3), then
branches on the public `rounds` (12 or 16) to the mode `m n` over the core
with that count.
-/

@[expose] public section

namespace VG.Impl.Cast5.RISCV64

open VG.RISCV64
open VG.Impl.Modes.RISCV64 (sb)

/-- The buffer's slot. -/
def bufSlot : Nat := 6

/-- Our caller's registers the core saves, and their slots: those the block
function writes but the mode's `s1`–`s4`, and those it keeps the mode's in. -/
def modeSaved : List (Reg × Nat) :=
  [.s0, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra].zipIdx.map fun (r, i) => (r, 8 * (i + 7))

/-- The block in the buffer encrypted (`up`) or decrypted with `n` rounds:
our caller's registers saved, the mode's `s1`–`s4` to `a3`, `a4`, `s11`
and `ra`, the buffer's and the table's addresses and `n` set, the block
function, and the registers back. -/
def modeCrypt (up : Bool) (n : Nat) : Prog isa :=
  .seq (.block (modeSaved.map (fun (r, d) => .store .d r sb d) ++
      ([.addi dat sb (8 * bufSlot), mov .a3 .s1, mov .a4 .s2, mov .s11 .s3, mov .ra .s4, .lla tbl s1234Sym,
        .li rnd n] : List Instr)))
    (.seq (crypt up dat)
      (.block (([mov .s1 .a3, mov .s2 .a4, mov .s3 .s11, mov .s4 .ra] : List Instr) ++
        modeSaved.map (fun (r, d) => .load .d r sb d))))

/-- CAST5's core for the modes, encrypting (`up`) or decrypting with `n` rounds. -/
def dirCore (up : Bool) (n : Nat) : Modes.RISCV64.Core where
  prepare := .block []
  crypt := modeCrypt up n
  total := 16
  buf := bufSlot
  G := 1
  bw := 2

/-- `f(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4)`: the mode
`m 12` or `m 16`, as `rounds` says, with the arguments in the modes'
registers. -/
def modeFn (m : Nat → Prog isa) : Prog isa :=
  .seq (.block [mov .t0 .a1, mov .a1 .a2, mov .a2 .a3, mov .a3 .a4, .addi .t0 .t0 (-12)])
    (.ite (.zero .t0) (m 12) (m 16))

/-- `vg_cast5_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := modeFn fun n => (dirCore false n).seq (Modes.Mode.cbcDecChained 2)

/-- `vg_cast5_ofb`. -/
def ofb : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.ofb 2)

/-- `vg_cast5_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.cfbEnc 2)

/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := modeFn fun n => (dirCore true n).seq (Modes.Mode.cfbDec 2)

end VG.Impl.Cast5.RISCV64
