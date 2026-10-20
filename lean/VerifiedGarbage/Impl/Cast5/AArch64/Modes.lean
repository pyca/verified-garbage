module

public import VerifiedGarbage.Impl.Cast5.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# CAST5-CBC, -OFB and -CFB64 on AArch64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and `cfbDecrypt`
(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5): the
modes' generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/AArch64/CbcChained.lean`, `Fb.lean`) over the block code of
`vg_cast5_ecb_{en,de}crypt` (`encryptBlock`, `decryptBlock`), one 8-byte
block at a time, with the working space in the scratch buffer, which the
artifact allocates on the stack.

The core's one slot is the buffer's block. The key is the subkeys where the
caller passed them, at `x0`, and the number of rounds in `x1`: neither the
modes nor the block code write either, so `prepare` does nothing. `crypt`
keeps the scratch buffer's address (`sb` = `x5`, which the block code
overwrites) in `x16`, points `x2` at the buffer, and runs the block code,
which reads the table of S-boxes from the static `VG_CAST5_S1234` and
writes only `x2`–`x15` and `v0`–`v5`: it keeps `x23` and `x24`, which carry
the data's address and the blocks left, and `x25`, where CBC encryption and the
feedback modes keep the IV's address.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb movR)

/-- `sb` to `x16`, `x2` to the buffer (at `sb`). -/
def modeSetup : List Instr := [movR .x16 sb, movR .x2 sb]

/-- `sb` back from `x16`. -/
def modeFinish : List Instr := [movR sb .x16]

/-- The block code on the buffer, encrypting (`up`) or decrypting. -/
def cryptCode (up : Bool) : Prog isa :=
  .seq (.block modeSetup) (.seq (if up then encryptBlock else decryptBlock) (.block modeFinish))

/-- CAST5's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Impl.Modes.AArch64.Core where
  prepare := .block []
  crypt := cryptCode up
  slots := 1
  total := 13
  buf := 0
  lgG := 0
  bw := 1
  keyRegs := [.x0, .x1]
  dataReg := .x23
  leftReg := .x24

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.AArch64.CtrRegs := ⟨.x2, .x3, .x4, .x5⟩

/-- `vg_cast5_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore true).cbcEncryptChained modeRegs .x25

/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).cbcDecryptChained modeRegs

/-- `vg_cast5_ofb`. -/
def ofb : Prog isa := (dirCore true).fb .ofb modeRegs .x25

/-- `vg_cast5_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).fb .cfbEnc modeRegs .x25

/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).fb .cfbDec modeRegs .x25

end VG.Impl.Cast5.AArch64
