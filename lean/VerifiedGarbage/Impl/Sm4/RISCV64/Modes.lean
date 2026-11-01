module

public import VerifiedGarbage.Impl.Modes.RISCV64.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Modes.Ctr
public import VerifiedGarbage.Impl.Sm4.RISCV64.Ecb

/-!
# SM4's modes on RISC-V

`dirCore d`: ECB's two halves (`Ecb.lean`), inlined, as a core for the modes
(`Impl/Modes/RISCV64/Seq.lean`), on one block of a batch of sixteen, as on
PPC64LE (`Impl/Sm4/PPC64LE/Modes.lean`, which calls them instead). ECB's
scratch buffer is the core's slots from `ecbSlot` (slot 7 of the mode's
frame), and the key argument waits in the core's first slot (`keySlot`).
`prepare` saves the caller's `s0`–`s11`, sets the masks and builds the table
of bitsliced round keys in the order of the direction `d` (`keys d`, from
the schedule at `a0`); `crypt` saves them, transforms the sixteen blocks of
the tail buffer (`crypt16`), of which the modes use the first (slot
`ecbSlot + tailSlot` of the frame), and restores them.

ECB keeps only `ra`, `a1`, `a2`, `a4` and `a5` (its base), and memory is
secret to the analysis of constant time, so the modes' state (`s1`–`s3`,
which address and count) waits in `a1`, `a2` and `a4` (`park`), and the
frame's base (`s4`) is ECB's base less `ecbOff` (`unpark`). 404 slots in
all, with the modes'.

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt`, `cfbDecrypt`
and `ctr` (schedule = a0, iv = a1, data = a2, n = a3) are the modes over it.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- The core's first slot, which keeps the key argument. -/
def keySlot : Nat := Modes.RISCV64.coreSlot

/-- ECB's scratch buffer: the core's slots after `keySlot`. -/
def ecbSlot : Nat := keySlot + 1

def ecbOff : Nat := 8 * ecbSlot

/-- ECB's base, from the frame's, and the caller's registers saved. -/
def coreIn : List Instr := [.addi sb Modes.RISCV64.sb (ecbOff : Int)] ++ saveRegs

/-- The modes' state to `a1`, `a2` and `a4`. -/
def park : List Instr := [movR .a1 .s1, movR .a2 .s2, movR .a4 .s3]

/-- The caller's registers restored, the modes' state back, the frame's base,
and the key argument from its slot. -/
def unpark : List Instr :=
  restoreRegs ++ [movR .s1 .a1, movR .s2 .a2, movR .s3 .a4, .addi Modes.RISCV64.sb sb (-(ecbOff : Int)),
    .load .d .a0 Modes.RISCV64.sb (8 * keySlot)]

/-- The key argument to its slot, the masks, and the table of `d`. -/
def corePrepare (d : Dir) : Prog isa :=
  .seq (.block ([.store .d .a0 Modes.RISCV64.sb (8 * keySlot)] ++ coreIn ++ setSlots (keyMasks ++ bsKs) ++ park))
    (.seq (keys d) (.block unpark))

/-- The sixteen blocks of the tail buffer. -/
def coreCrypt : Prog isa :=
  .seq (.block (coreIn ++ park ++ slotAddr .a0 tableEnd)) (.seq crypt16 (.block unpark))

/-- SM4's core for the modes, in the direction `d`. -/
def dirCore (d : Dir) : Modes.RISCV64.Core where
  prepare := corePrepare d
  crypt := coreCrypt
  total := ecbSlot + slots + 1
  buf := ecbSlot + tailSlot
  G := 1
  bw := 4

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 4)

/-- `vg_sm4_ctr`. -/
def ctr : Prog isa := (dirCore .encrypt).seq Modes.Mode.ctr

end VG.Impl.Sm4.RISCV64
