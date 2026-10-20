module

public import VerifiedGarbage.Impl.Blowfish.X86_64
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# Blowfish-CBC, -OFB and -CFB64 on x86-64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and `cfbDecrypt`
(schedule = rdi, iv = rsi, data = rdx, n = rcx, scratch = r8): the modes'
generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/X86_64/CbcChained.lean`, `Fb.lean`) over the block code of `vg_blowfish_ecb_{en,de}crypt` (`cipher`),
one 8-byte block at a time, with the working space in the scratch buffer,
which the artifact allocates on the stack.

The core's slots: the buffer's one block, then the 16 bytes through which
`storeBlock` carries the halves out of the vector registers. The key is the
schedule where the caller passed it, at `rdi`, which neither the modes nor
the block code write; `prepare` does nothing. `crypt` points `rsi` and `rcx`
at the buffer and the 16 bytes, and keeps the scratch buffer's address
(`sb`, the block code's row counter `r9`) in `rdx`. The block code uses
every `xmm` register, `xmm15` (where CBC encryption and the feedback modes keep the IV's
address, its upper half zero) among them: `crypt` keeps its low half in
`r14`, which neither the block code nor the modes use, and puts it back.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb movR)

/-- The 16 bytes of working space, after the buffer. -/
def wsSlot : Nat := 1

/-- `xmm15`'s low half to `r14`. -/
def saveIv : List Instr := [.movqR .r14 .xmm15]

/-- `xmm15` back from `r14`, its upper half zero. -/
def restoreIv : List Instr := [.xop (.movq .xmm15 .r14)]

/-- `sb` to `rdx`; `rsi` and `rcx` to the buffer and the 16 bytes; the
scans' constants; the buffer's block into the halves. -/
def setup : List Instr :=
  ([movR .rdx sb, movR .rsi sb, movR .rcx sb, .alu .add .rcx (.imm (BitVec.ofNat 32 (8 * wsSlot)))] :
    List Instr) ++ constants ++ loadBlock

/-- The halves back to the buffer, and `sb` back from `rdx`. -/
def finish : List Instr := storeBlock ++ ([movR sb .rdx] : List Instr)

/-- The block code on the buffer, in the direction `up`. -/
def cryptCode (up : Bool) : Prog isa :=
  .seq (.block saveIv) (.seq (.block setup) (.seq (cipher .rdi up) (.seq (.block finish) (.block restoreIv))))

/-- Blowfish's core for the modes, in the direction `up`. -/
def dirCore (up : Bool) : Impl.Modes.X86_64.Core where
  prepare := .block []
  crypt := cryptCode up
  slots := 3
  total := 11
  buf := 0
  G := 1
  bw := 1
  keyRegs := [.rdi]
  dataReg := .r12
  leftReg := .r13

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.X86_64.CtrRegs := ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore true).cbcEncryptChained modeRegs

/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).cbcDecryptChained modeRegs

/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := (dirCore true).fb .ofb modeRegs

/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).fb .cfbEnc modeRegs

/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).fb .cfbDec modeRegs

end VG.Impl.Blowfish.X86_64
