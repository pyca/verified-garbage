module

public import VerifiedGarbage.Impl.Seed.X86_64.Ecb
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# SEED-CBC, -OFB and -CFB128 on x86-64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = rdi, iv = rsi, data = rdx, n = rcx, scratch = r8):
the modes' generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/X86_64/CbcChained.lean`, `Fb.lean`) over `vg_seed_ecb_{en,de}crypt`'s batch of sixteen blocks
(`batch`), with the working space in the scratch buffer, which the artifact
allocates on the stack. CBC decryption deciphers sixteen blocks at a time;
the other modes encipher one block per batch, of which the other fifteen
lanes are unused.

The core's slots: the batch's 132 (its working area, at `sb` = `r9` as the
batch needs, with the masks that `prepare` writes), the buffer's sixteen
blocks, and a copy of the 128-byte schedule, which `prepare` makes so that
nothing the modes write can reach it. `crypt` keeps the data's address and
the blocks left (`r12`, `r13`, which the batch overwrites) in `xmm13` and
`xmm14`, which the batch does not touch (and which, unlike its slots, the
taint analysis keeps public across its stores), points `rsi`, `rdx` and
`rdi` at the buffer, its sixteen blocks and the copy's first round key, and
runs the batch.
-/

@[expose] public section

namespace VG.Impl.Seed.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Impl.Modes.X86_64 (copyW)
open VG.Spec.Seed (Direction)

/-- The core's buffer, after the batch's slots. -/
def bufSlot : Nat := scratchSlots

/-- The schedule's copy, after the buffer. -/
def schedSlot : Nat := bufSlot + 32

/-- SEED's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Impl.Modes.X86_64.Core where
  prepare := .block ((List.range 16).flatMap (copyW .rax sb .rdi (8 * schedSlot) 0) ++ setG16Masks)
  crypt := .seq (.block [.xop (.movq .xmm13 .r12), .xop (.movq .xmm14 .r13), movR .rsi sb,
      .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * bufSlot))), .movImm64 .rdx 16, movR .rdi sb,
      .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot + keyStart d)))])
    (.seq (batch d) (.block [.movqR .r12 .xmm13, .movqR .r13 .xmm14]))
  slots := schedSlot + 16
  total := schedSlot + 24
  buf := bufSlot
  G := 16
  keyRegs := [.rdi]
  dataReg := .r12
  leftReg := .r13

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
