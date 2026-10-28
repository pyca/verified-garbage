module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb

/-!
# SEED's modes on RISC-V

`dirCore d`: ECB's batch (`Ecb.lean`), inlined, as a core for the modes
(`Impl/Modes/RISCV64/Seq.lean`), on one block, as on PPC64LE: ECB's
scratch buffer is the core's slots from `coreSlot` (`ecbOff` bytes into the
frame), and ECB's prologue (`prologue`) moves its base to `a5`, saves the
caller's `s0`–`s11` and builds `g16`'s masks; the block of the core's buffer
(slot `bufSlot`, after ECB's slots) is copied into lane 0 of the arrays
(ECB's copy loop, once), sixteen rounds run on every lane (`rounds d`, the
other fifteen lanes holding whatever they hold), and lane 0 is copied back,
under the schedule at `a0`, read in place, the round keys in the order of the
direction `d`: encryption's for CBC encryption, OFB and CFB, decryption's
for CBC decryption.

The rounds keep only `ra`, `a0`–`a3` and `a5`, and memory is secret to the
analysis of constant time, so the modes' state (`s1`–`s3`, which address
and count) waits in `a1`, `a2` and `ra` (`park`), `ra` itself in the core's
last slot (`raSlot`); the frame's base (`s4`) is ECB's base less `ecbOff`.
After the block, ECB's epilogue restores `s0`–`s11`, then the modes' state
and `ra` are put back (`coreOut`). 138 slots in all, with the modes'.

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = a0, iv = a1, data = a2, n = a3) are the modes over
it.
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Spec.Seed (Direction)

/-- ECB's scratch buffer: the core's slots, from `coreSlot`. -/
def ecbOff : Nat := 8 * Modes.RISCV64.coreSlot

/-- The core's buffer, after ECB's slots. -/
def bufSlot : Nat := Modes.RISCV64.coreSlot + scratchSlots

/-- Where `ra` waits during the block, as an offset from ECB's base. -/
def raOff : Nat := 8 * (scratchSlots + 2)

/-- The modes' state to `a1`, `a2` and `ra`, `ra` to its slot. -/
def park : List Instr := [.store .d .ra sb raOff, movR .a1 .s1, movR .a2 .s2, movR .ra .s3]

/-- The key pointer at the first round's key; one block to copy, from the
buffer, into lane 0. -/
def copyFrom (d : Direction) : List Instr :=
  [.addi .a0 .a0 (keyStart d), .li t2 1, .addi .t3 sb ((8 * scratchSlots : Nat) : Int), movR .t4 sb]

/-- ECB's base and prologue, and the modes' state parked. -/
def coreIn (d : Direction) : List Instr :=
  [.addi t0 Modes.RISCV64.sb ecbOff] ++ prologue t0 ++ park ++ copyFrom d

/-- One block to copy out, from lane 0 to the buffer. -/
def copyTo : List Instr := [.li t2 1, .addi .t3 sb ((8 * scratchSlots : Nat) : Int), movR .t4 sb]

/-- The key pointer back, the caller's registers restored, the modes' state
and `ra` back, and the frame's base. -/
def coreOut (d : Direction) : List Instr :=
  [.addi .a0 .a0 (-(keyStart d : Int))] ++ seedRestore ++
    [movR .s1 .a1, movR .s2 .a2, movR .s3 .ra, .load .d .ra sb raOff,
      .addi Modes.RISCV64.sb sb (-(ecbOff : Int))]

/-- The block: copied into lane 0, enciphered, and copied back. -/
def coreCrypt (d : Direction) : Prog isa :=
  .seq (.block (coreIn d)) (.seq (.loop (.block copyInBody) (.nonzero t2)) (.seq (rounds d)
    (.seq (.block copyTo) (.seq (.loop (.block copyOutBody) (.nonzero t2)) (.block (coreOut d))))))

/-- SEED's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Modes.RISCV64.Core where
  prepare := .block []
  crypt := coreCrypt d
  total := bufSlot + 3
  buf := bufSlot
  G := 1
  bw := 4

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_seed_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 4)

end VG.Impl.Seed.RISCV64
