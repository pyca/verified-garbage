module

public import VerifiedGarbage.Impl.Seed.X86_64.Ecb
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# SEED-CBC, -OFB and -CFB128 on x86-64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = rdi, iv = rsi, data = rdx, n = rcx, scratch = r8):
the modes' generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/X86_64/CbcChained.lean`, `Fb.lean`) over calls of
`vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks` (the ECB code with the
working space as an argument) on sixteen blocks, with the working space in
the scratch buffer, which the artifact allocates on the stack. CBC
decryption deciphers sixteen blocks at a time; the other modes encipher one
block per call, of which the other fifteen lanes are unused.

The core's slots: the blocks function's 136 (its working space, at `sb` =
`r9`), the buffer's sixteen blocks, and a copy of the 128-byte schedule,
which `prepare` makes so that nothing the modes write can reach it. The
callee writes no `xmm` register, and the taint analysis keeps those public
across its stores (unlike its slots, or the callee-saved registers it
restores from them): `crypt` keeps the scratch buffer's address, the data's
address and the blocks left (`r9`, `r12`, `r13`) in `xmm12` … `xmm14`,
points `rdi`, `rsi`, `rdx` and `rcx` at the schedule's copy, the buffer,
its sixteen blocks and the working space, and calls the function, whose
return address is the stack the core uses. CBC encryption and the feedback
modes keep the IV's address in `xmm15`.
-/

@[expose] public section

namespace VG.Impl.Seed.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Impl.Modes.X86_64 (copyW)
open VG.Spec.Seed (Direction)

/-- The core's buffer, after the blocks function's working space
(`Proof.Seed.blocksSig`'s 136 words). -/
def bufSlot : Nat := 136

/-- The schedule's copy, after the buffer. -/
def schedSlot : Nat := bufSlot + 32

/-- A call of `vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks` (the ECB
code with the working space as an argument). -/
def blockCall : Direction → Prog isa
  | .encrypt => .call "vg_seed_encrypt_blocks" encrypt
  | .decrypt => .call "vg_seed_decrypt_blocks" decrypt

/-- `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt` within its frame, which
allocates the working space at `rcx`: a call of the blocks function in the
direction `d`. -/
abbrev ecbCall (d : Direction) : Prog isa := blockCall d

/-- Before the call: the scratch buffer's address, the data's address and
the blocks left to `xmm12` … `xmm14`, then the arguments: the schedule's
copy, the buffer, its sixteen blocks and the working space (`sb`). -/
def cryptHead : List Instr :=
  [.xop (.movq .xmm12 sb), .xop (.movq .xmm13 .r12), .xop (.movq .xmm14 .r13),
   movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))),
   movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * bufSlot))), .movImm64 .rdx 16, movR .rcx sb]

/-- After the call: the three registers back. -/
def cryptTail : List Instr := [.movqR sb .xmm12, .movqR .r12 .xmm13, .movqR .r13 .xmm14]

/-- SEED's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Impl.Modes.X86_64.Core where
  prepare := .block ((List.range 16).flatMap (copyW .rax sb .rdi (8 * schedSlot) 0))
  crypt := .seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail))
  slots := schedSlot + 16
  total := schedSlot + 24
  buf := bufSlot
  G := 16
  keyRegs := [.rdi, .rsp]
  dataReg := .r12
  leftReg := .r13
  stack := 8

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.X86_64.CtrRegs := ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).cbcEncryptChained modeRegs

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained modeRegs

/-- `vg_seed_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).fb .ofb modeRegs

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).fb .cfbEnc modeRegs

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).fb .cfbDec modeRegs

end VG.Impl.Seed.X86_64
