module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Impl.Cast5.AArch64.Modes
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec

/-!
# CAST5-CBC and -CFB64 decryption on AArch64, sixteen blocks at a time

`cbcDecryptChained` and `cfbDecrypt` (schedule = x0, rounds = x1, iv = x2,
data = x3, n = x4, scratch = x5): the modes' CBC decryption that updates the
chaining value and batched CFB decryption (`Impl/Modes/AArch64/CbcChained.lean`,
`CfbDec.lean`), whose blocks are deciphered or enciphered independently,
over the ECB functions' batch of sixteen blocks (`Tbl.batch`), with the
working space in the scratch buffer, which the artifact allocates on the
stack.

The core's slots are the buffer's sixteen blocks, on which the batch runs in
place. The key is the subkeys where the caller passed them, at `x0`, and the
number of rounds in `x1`: neither the modes nor the batch write either, so
`prepare` does nothing. `crypt` keeps the scratch buffer's address (`sb` =
`x5`, the batch's pointer to the subkeys) in `x22`, points `x4` at the
buffer, copies the number of rounds to `x16`, sets the batch's constants and
the table's address, and runs the batch. The batch writes most vector
registers, `v8`–`v15` among them, whose low halves the calling convention
preserves: `crypt` keeps them in `x11`, `x12`, `x19`–`x21` and `x26`–`x28`,
which the batch does not write (the modes save `x19`–`x28` in their own
slots on entry, and restore them on return), and puts them back (`dup`), so
that every run of `crypt` keeps them. It keeps `x23` and `x24`, which carry
the data's address and the blocks left.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64.Tbl

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb movR)

/-- `v8`–`v15`, whose low halves the calling convention preserves. -/
def modeV (k : Nat) : VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15].getD k .v8

/-- Where `crypt` keeps the low half of `modeV k`. -/
def modeKeep (k : Nat) : Reg := [.x11, .x12, .x19, .x20, .x21, .x26, .x27, .x28].getD k .x11

/-- The low halves of `v8`–`v15` to their registers. -/
def modeSave : List Instr := (List.range 8).map fun k => .umov .x (modeKeep k) (modeV k) 0

/-- `v8`–`v15` back, and `sb` back from `x22`. -/
def modeRestore : List Instr :=
  (List.range 8).map (fun k => .vop (.dup .d2 (modeV k) (modeKeep k))) ++ ([movR sb .x22] : List Instr)

/-- `sb` to `x22`, `x4` to the buffer (at `sb`), the number of rounds to
`x16`, the batch's constants and the table's address. -/
def modeSetup : List Instr := ([movR .x22 sb, movR .x4 sb, movR .x16 .x1] : List Instr) ++ setup

/-- The batch of each direction, named for their literals. -/
def batchEnc : Prog isa := batch true
def batchDec : Prog isa := batch false

def batchOf : Bool → Prog isa
  | true => batchEnc
  | false => batchDec

/-- The batch on the buffer, in the direction `up`. -/
def modeCrypt (up : Bool) : Prog isa :=
  .seq (.block modeSave) (.seq (.block modeSetup) (.seq (batchOf up) (.block modeRestore)))

/-- CAST5's core of sixteen blocks for the modes, in the direction `up`. -/
def batchCore (up : Bool) : Impl.Modes.AArch64.Core where
  prepare := .block []
  crypt := modeCrypt up
  slots := 16
  total := 28
  buf := 0
  lgG := 4
  bw := 1
  keyRegs := [.x0, .x1]
  dataReg := .x23
  leftReg := .x24

/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (batchCore false).cbcDecryptChained modeRegs

/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (batchCore true).cfbDecryptBatched modeRegs

end VG.Impl.Cast5.AArch64.Tbl
