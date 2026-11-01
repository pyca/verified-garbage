module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Modes.Ctr
public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb

/-!
# Camellia's modes on RISC-V

`dirCore d R`: ECB's key setup and batch (`Ecb.lean`), inlined, as a core
for the modes (`Impl/Modes/RISCV64/Seq.lean`), with `R` rounds and the
subkeys in the order of the direction `d`: encryption's for CBC
encryption, OFB, CFB and CTR, decryption's for CBC decryption, as on
PPC64LE (`Impl/Camellia/PPC64LE/Modes.lean`), where they are the bodies of
`vg_camellia_prepare_keys` and `vg_camellia_crypt_prepared`. ECB's scratch
buffer is the core's slots, from `coreSlot` (`ecbOff` bytes into the
frame), and its tail buffer is the core's buffer: `prepare` runs ECB's
prologue (`prologue`: the base to `a5`, the caller's `s0`–`s11` saved, the
masks set) and builds the table of bitsliced subkeys once (`keys d`);
`crypt` saves the registers the same way, sets `a4` at the postwhitening's
entry for `R` rounds and transforms the eight blocks of the tail buffer
(`crypt8`), of which the modes use the first (they take one step at a
time). Both restore the registers after.

The key setup and the rounds write neither `a2`, `a3`, `a5` nor `ra`, and
memory is secret to the analysis of constant time, so the modes' state
(`s1`–`s3`, which address and count) waits in `a2`, `a3` and `ra`
(`park`), `ra` itself and `a0` in two slots of the scratch buffer that ECB
does not use (`raSlot`, `a0Slot`); the frame's base (`s4`) is ECB's base
less `ecbOff` (`unpark`).

The functions take the number of rounds as their second argument, which the
modes' code does not: `modeFn m` moves `rounds` to `t0` and the others down
to the modes' registers (schedule = a0, iv = a1, data = a2, n = a3), then
branches on the public `rounds` (18 or 24) to the mode `m R` over the core
with that many, as CAST5's do (`Impl/Cast5/RISCV64/Modes.lean`).

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt`,
`cfbDecrypt` and `ctr` are the modes over it.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Impl.Modes.RISCV64 (mov coreSlot)

/-- ECB's scratch buffer: the core's slots, from `coreSlot`. -/
def ecbOff : Nat := 8 * coreSlot

/-- The slots of ECB's scratch buffer where `ra` and `a0` wait, between the
saved registers and the tail buffer. -/
def raSlot : Nat := savedSlot + 12
def a0Slot : Nat := savedSlot + 13

/-- ECB's base to `t0`, `ra` and `a0` to their slots, and the modes'
`s1`–`s3` to `a2`, `a3` and `ra`. -/
def park : List Instr :=
  [.addi t0 Modes.RISCV64.sb (ecbOff : Int), .store .d .ra Modes.RISCV64.sb (ecbOff + 8 * raSlot),
    .store .d .a0 Modes.RISCV64.sb (ecbOff + 8 * a0Slot), movR .a2 .s1, movR .a3 .s2, movR .ra .s3]

/-- The modes' state back, the frame's base from ECB's, and `ra` and `a0`
from their slots. -/
def unpark : List Instr :=
  [movR .s1 .a2, movR .s2 .a3, movR .s3 .ra, .addi Modes.RISCV64.sb sb (-(ecbOff : Int)),
    .load .d .ra sb (8 * raSlot), .load .d .a0 sb (8 * a0Slot)]

/-- The table, built once: ECB's prologue for `R` rounds, the key setup,
and the registers back. -/
def prepareKeys (d : Dir) (R : Nat) : Prog isa :=
  .seq (.block (park ++ ([.li .a1 R] : List Instr) ++ prologue t0))
    (.seq (keys d) (.block (restoreRegs ++ unpark)))

/-- The eight blocks of the tail buffer, under the table, with `R` rounds:
the registers saved, `a4` at the postwhitening's entry, the rounds, and the
registers back. -/
def cryptBlocks (R : Nat) : Prog isa :=
  .seq (.block (park ++ ([movR sb t0] : List Instr) ++ saveRegs ++ endAddr (R / 6)))
    (.seq crypt8 (.block (restoreRegs ++ unpark)))

/-- Camellia's core for the modes, with `R` rounds in the direction `d`. -/
def dirCore (d : Dir) (R : Nat) : Modes.RISCV64.Core where
  prepare := prepareKeys d R
  crypt := cryptBlocks R
  total := coreSlot + slots
  buf := coreSlot + tailSlot
  G := 1
  bw := 4

/-- `f(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4)`: the mode
`m 18` or `m 24`, as `rounds` says, with the arguments in the modes'
registers. -/
def modeFn (m : Nat → Prog isa) : Prog isa :=
  .seq (.block [mov .t0 .a1, mov .a1 .a2, mov .a2 .a3, mov .a3 .a4, .addi .t0 .t0 (-18)])
    (.ite (.zero .t0) (m 18) (m 24))

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := modeFn fun R => (dirCore .encrypt R).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := modeFn fun R => (dirCore .decrypt R).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := modeFn fun R => (dirCore .encrypt R).seq (Modes.Mode.ofb 4)

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := modeFn fun R => (dirCore .encrypt R).seq (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := modeFn fun R => (dirCore .encrypt R).seq (Modes.Mode.cfbDec 4)

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := modeFn fun R => (dirCore .encrypt R).seq Modes.Mode.ctr

end VG.Impl.Camellia.RISCV64
