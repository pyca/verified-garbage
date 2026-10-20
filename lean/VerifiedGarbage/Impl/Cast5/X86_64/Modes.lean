module

public import VerifiedGarbage.Impl.Cast5.X86_64
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# CAST5-CBC, -OFB and -CFB64 on x86-64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and `cfbDecrypt`
(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, n = r8, scratch = r9):
the modes' generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/X86_64/CbcChained.lean`, `Fb.lean`) over the block code of
`vg_cast5_ecb_{en,de}crypt` (`encryptBlock`, `decryptBlock`), one 8-byte
block at a time, with the working space in the scratch buffer, which the
artifact allocates on the stack.

The core's slots: the 16 bytes through which the rounds carry the S-boxes'
outputs (ECB's working space at `r8`), the buffer's one block, the modes'
data pointer and blocks left (`r12` and `r13`, which the rounds use), then a
copy of the 128-byte schedule, which `prepare` makes so that nothing the
modes write can reach it. The number of rounds stays in `rsi`, which
neither the modes nor the block code write. `crypt` points `r8`, `rdx` and
`rdi` at the working space, the buffer and the copy; `r8` is the scratch
buffer's address (`sb`, which the rounds overwrite) again after the block.

CBC encryption and the feedback modes keep the IV's address in `xmm15` (its upper half zero),
which the block code does not write; but its scans load the table into
`xmm5`, after which the taint analysis no longer knows `xmm15` public.
`crypt` keeps its low half in `rcx`, which the block code only counts down
by one (`store`), and puts it back from there after the block.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Impl.Modes.X86_64 (copyW)

/-- The buffer's block, after the working space. -/
def bufSlot : Nat := 2

/-- Where `r12` and `r13` are kept during the block. -/
def keepSlot : Nat := 3

/-- The schedule's copy. -/
def schedSlot : Nat := 5

/-- `r8`, `rdx` and `rdi` to the working space, the buffer and the copy;
`r12` and `r13` to their slots. -/
def modeSetup : List Instr :=
  [movR .r8 sb, .store (at_ .r8 (8 * keepSlot)) .r12, .store (at_ .r8 (8 * keepSlot + 8)) .r13,
   movR .rdx sb, .alu .add .rdx (imm (8 * bufSlot)),
   movR .rdi sb, .alu .add .rdi (imm (8 * schedSlot))]

/-- `r12`, `r13` and `sb` back. -/
def modeFinish : List Instr :=
  [.mov .r12 (.mem (at_ .r8 (8 * keepSlot))), .mov .r13 (.mem (at_ .r8 (8 * keepSlot + 8))), movR sb .r8]

/-- `xmm15`'s low half to `rcx`, which the block code only counts down by one. -/
def saveIv : List Instr := [.movqR .rcx .xmm15]

/-- `xmm15` back from `rcx`, its upper half zero. -/
def restoreIv : List Instr := [.alu .add .rcx (imm 1), .xop (.movq .xmm15 .rcx)]

/-- The block code on the buffer, encrypting (`up`) or decrypting. -/
def cryptCode (up : Bool) : Prog isa :=
  .seq (.block (saveIv ++ modeSetup)) (.seq (if up then encryptBlock else decryptBlock)
    (.block (modeFinish ++ restoreIv)))

/-- CAST5's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Impl.Modes.X86_64.Core where
  prepare := .block ((List.range 16).flatMap (copyW .rax sb .rdi (8 * schedSlot) 0))
  crypt := cryptCode up
  slots := schedSlot + 16
  total := schedSlot + 24
  buf := bufSlot
  G := 1
  bw := 1
  keyRegs := [.rdi, .rsi]
  dataReg := .r12
  leftReg := .r13

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.X86_64.CtrRegs := ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_cast5_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore true).cbcEncryptChained modeRegs

/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore false).cbcDecryptChained modeRegs

/-- `vg_cast5_ofb`. -/
def ofb : Prog isa := (dirCore true).fb .ofb modeRegs

/-- `vg_cast5_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore true).fb .cfbEnc modeRegs

/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore true).fb .cfbDec modeRegs

end VG.Impl.Cast5.X86_64
