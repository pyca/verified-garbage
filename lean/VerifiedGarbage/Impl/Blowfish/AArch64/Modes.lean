module

public import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# Blowfish-CBC, -OFB and -CFB64 on AArch64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and `cfbDecrypt`
(schedule = x0, iv = x1, data = x2, n = x3, scratch = x4): the modes'
generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/AArch64/CbcChained.lean`, `Fb.lean`) over `vg_blowfish_ecb_{en,de}crypt`'s batch of sixteen blocks
(`batch`), with the working space in the scratch buffer, which the artifact
allocates on the stack. CBC decryption deciphers sixteen blocks at a time;
the other modes encipher one block per batch, of which the other fifteen
lanes are unused.

The core's slots are the buffer's sixteen blocks, on which the batch runs in
place. The key is the schedule where the caller passed it, at `x0`, which
neither the modes nor the batch write; `prepare` does nothing. `crypt`
keeps the scratch buffer's address (`sb` = `x5`, the batch's P-array
pointer) in `x16`, points `x4` at the buffer, sets the batch's constants and
runs it. The batch writes `x5`–`x7` and most vector registers, `v8`–`v15`
among them, whose low halves the calling convention preserves: `crypt` keeps them in `x8`–`x15`, which the batch does not write,
and puts them back (`dup`), so that every run of `crypt` keeps them. It
keeps `x23` and `x24`, which carry the data's address and the blocks left,
and `x25`, where CBC encryption and the feedback modes keep the IV's address.
-/

@[expose] public section

namespace VG.Impl.Blowfish.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb movR)

/-- `v8`–`v15`, whose low halves the calling convention preserves. -/
def modeV (k : Nat) : VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15].getD k .v8

/-- Where `crypt` keeps the low half of `modeV k`: `x8`–`x15`. -/
def modeKeep (k : Nat) : Reg := [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15].getD k .x8

/-- The low halves of `v8`–`v15` to `x8`–`x15`. -/
def modeSave : List Instr := (List.range 8).map fun k => .umov .x (modeKeep k) (modeV k) 0

/-- `v8`–`v15` back from `x8`–`x15`, and `sb` back from `x16`. -/
def modeRestore : List Instr :=
  (List.range 8).map (fun k => .vop (.dup .d2 (modeV k) (modeKeep k))) ++ ([movR sb .x16] : List Instr)

/-- `sb` to `x16`, `x4` to the buffer (at `sb`), the batch's constants. -/
def modeSetup : List Instr := ([movR .x16 sb, movR .x4 sb] : List Instr) ++ constants

/-- The batch of each direction, named for their literals. -/
def batchEnc : Prog isa := batch true
def batchDec : Prog isa := batch false

def batchOf : Bool → Prog isa
  | true => batchEnc
  | false => batchDec

/-- The batch on the buffer, in the direction `up`. -/
def modeCrypt (up : Bool) : Prog isa :=
  .seq (.block modeSave) (.seq (.block modeSetup) (.seq (batchOf up) (.block modeRestore)))

/-- Blowfish's core for the modes, in the direction `up`. -/
def dirCore (up : Bool) : Impl.Modes.AArch64.Core where
  prepare := .block []
  crypt := modeCrypt up
  slots := 16
  total := 28
  buf := 0
  lgG := 4
  bw := 1
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.AArch64.CtrRegs := ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore true).cbcEncryptChained modeRegs .x25

/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).cbcDecryptChained modeRegs

/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := (dirCore true).fb .ofb modeRegs .x25

/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).fb .cfbEnc modeRegs .x25

/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).fb .cfbDec modeRegs .x25

end VG.Impl.Blowfish.AArch64
