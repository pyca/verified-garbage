module

public import VerifiedGarbage.Impl.Idea.X86_64
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# IDEA-CBC, -OFB and -CFB64 on x86-64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and `cfbDecrypt`
(schedule = rdi, iv = rsi, data = rdx, n = rcx, scratch = r8): the modes'
generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/X86_64/CbcChained.lean`, `Fb.lean`) over the block code of `vg_idea_ecb` (`cryptBlock`), one 8-byte
block at a time, with the working space in the scratch buffer, which the
artifact allocates on the stack. IDEA decrypts with the same code under the
decryption subkeys, so one core serves every function.

The core's slots: the buffer's one block, then a copy of the 104-byte
schedule, which `prepare` makes so that nothing the modes write can reach
it. `crypt` points `rdi` and `rsi` at the copy and the buffer and keeps the
scratch buffer's address (`sb`, which the block code overwrites) in `rcx`.
The block code keeps `r12` and `r13`, which carry the data's address and the
blocks left.
-/

@[expose] public section

namespace VG.Impl.Idea.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Impl.Modes.X86_64 (copyW)

/-- The schedule's copy, after the buffer. -/
def schedSlot : Nat := 1

/-- IDEA's core for the modes. -/
def modeCore : Impl.Modes.X86_64.Core where
  prepare := .block ((List.range 13).flatMap (copyW .rax sb .rdi (8 * schedSlot) 0))
  crypt := .block (([movR .rcx sb, movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))),
      movR .rsi sb] : List Instr) ++ cryptBlock ++ ([movR sb .rcx] : List Instr))
  slots := schedSlot + 13
  total := schedSlot + 21
  buf := 0
  G := 1
  bw := 1
  keyRegs := [.rdi]
  dataReg := .r12
  leftReg := .r13

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.X86_64.CtrRegs := ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_idea_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := modeCore.cbcEncryptChained modeRegs

/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := modeCore.cbcDecryptChained modeRegs

/-- `vg_idea_ofb`. -/
def ofb : Prog isa := modeCore.fb .ofb modeRegs

/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := modeCore.fb .cfbEnc modeRegs

/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := modeCore.fb .cfbDec modeRegs

end VG.Impl.Idea.X86_64
