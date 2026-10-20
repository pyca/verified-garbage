module

public import VerifiedGarbage.Impl.Idea.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained
public import VerifiedGarbage.Impl.TripleDes.AArch64.Common

/-!
# IDEA-CBC, -OFB and -CFB64 on AArch64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and `cfbDecrypt`
(schedule = x0, iv = x1, data = x2, n = x3, scratch = x4): the modes'
generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/AArch64/CbcChained.lean`, `Fb.lean`) over the block code of `vg_idea_ecb` (`cryptBlock`), one 8-byte
block at a time, with the working space in the scratch buffer, which the
artifact allocates on the stack. IDEA decrypts with the same code under the
decryption subkeys, so one core serves every function.

The core's slots: the buffer's one block, then a copy of the 104-byte
schedule, which `prepare` makes so that nothing the modes write can reach
it. `crypt` points `x0` and `x1` at the copy and the buffer, sets the mask
in `x15`, and keeps the scratch buffer's address (`sb`, which the block code
overwrites) in `x2`. The block code writes only `x3`–`x14`: it keeps `x23`
and `x24`, which carry the data's address and the blocks left, and `x25`,
where CBC encryption and the feedback modes keep the IV's address.
-/

@[expose] public section

namespace VG.Impl.Idea.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Impl.Modes.AArch64 (copyW)
open VG.Impl.TripleDes.AArch64 (rr)

/-- The schedule's copy, after the buffer. -/
def schedSlot : Nat := 1

/-- IDEA's core for the modes. -/
def modeCore : Impl.Modes.AArch64.Core where
  prepare := .block ((List.range 13).flatMap (copyW .x6 sb .x0 (8 * schedSlot) 0))
  crypt := .block (([rr .x2 sb, .addImm .x .x0 sb (8 * schedSlot), rr .x1 sb, setMask] : List Instr) ++
    cryptBlock ++ ([rr sb .x2] : List Instr))
  slots := schedSlot + 13
  total := schedSlot + 25
  buf := 0
  lgG := 0
  bw := 1
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.AArch64.CtrRegs := ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_idea_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := modeCore.cbcEncryptChained modeRegs .x25

/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := modeCore.cbcDecryptChained modeRegs

/-- `vg_idea_ofb`. -/
def ofb : Prog isa := modeCore.fb .ofb modeRegs .x25

/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := modeCore.fb .cfbEnc modeRegs .x25

/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := modeCore.fb .cfbDec modeRegs .x25

end VG.Impl.Idea.AArch64
