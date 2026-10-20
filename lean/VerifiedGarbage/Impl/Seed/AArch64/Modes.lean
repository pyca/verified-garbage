module

public import VerifiedGarbage.Impl.Seed.AArch64.Ecb
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# SEED-CBC, -OFB and -CFB128 on AArch64

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = x0, iv = x1, data = x2, n = x3, scratch = x4): the
modes' generic CBC that updates the chaining value, OFB and CFB
(`Impl/Modes/AArch64/CbcChained.lean`, `Fb.lean`) over `vg_seed_ecb_{en,de}crypt`'s batch of sixteen blocks
(`batch`), with the working space in the scratch buffer, which the artifact
allocates on the stack. CBC decryption deciphers sixteen blocks at a time;
the other modes encipher one block per batch, of which the other fifteen
lanes are unused. As on x86-64 (`Impl/Seed/X86_64/Modes.lean`).

The core's slots: the batch's 122 (its working area, at `sb` = `x5` as the
batch needs), the buffer's sixteen blocks, and a copy of the 128-byte
schedule, which `prepare` makes so that nothing the modes write can reach
it. The batch writes every general-purpose register but `sb` and `x30`, and
no vector register: `crypt` keeps the data's address and the blocks left
(`x23`, `x24`) in `v29` and `v30` (`dup`, back by `umov`), which the taint
analysis keeps public across the batch, points `x1`, `x2` and `x0` at the
buffer, its sixteen blocks and the copy's first round key, and runs the
batch. CBC encryption and the feedback modes keep the IV's address in
`x25`, which `fbCore` keeps in `v31` (`Core.viaV`).
-/

@[expose] public section

namespace VG.Impl.Seed.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Impl.Modes.AArch64 (copyW)
open VG.Spec.Seed (Direction)

/-- The core's buffer, after the batch's slots. -/
def bufSlot : Nat := scratchSlots

/-- The schedule's copy, after the buffer. -/
def schedSlot : Nat := bufSlot + 32

/-- A call of `vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks` (the ECB
code with the working space as an argument). -/
def blockCall : Direction → Prog isa
  | .encrypt => .call "vg_seed_encrypt_blocks" encrypt
  | .decrypt => .call "vg_seed_decrypt_blocks" decrypt

/-- `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt` within its frame, which
allocates the working space at `x3`: a call of the blocks function in the
direction `d`, in a frame saving `x30`. -/
def ecbCall (d : Direction) : Prog isa := .frame (.push .x30) (blockCall d) (.pop .x30)

/-- Before the call: the return address, the scratch buffer's address, the
data's address and the blocks left to `v28`, `v27`, `v29` and `v30` (the
callee writes no vector register, and the taint analysis keeps them public
across it), then the arguments: the schedule's copy, the buffer, its sixteen
blocks and the working space (`sb`). -/
def cryptHead : List Instr :=
  [.vop (.dup .d2 .v28 .x30), .vop (.dup .d2 .v27 sb), .vop (.dup .d2 .v29 .x23), .vop (.dup .d2 .v30 .x24),
   .addImm .x .x0 sb (8 * schedSlot), .addImm .x .x1 sb (8 * bufSlot), .movz .x .x2 16 0, movR .x3 sb]

/-- After the call: the four registers back. -/
def cryptTail : List Instr :=
  [.umov .x sb .v27 0, .umov .x .x30 .v28 0, .umov .x .x23 .v29 0, .umov .x .x24 .v30 0]

/-- SEED's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Impl.Modes.AArch64.Core where
  prepare := .block ((List.range 16).flatMap (copyW .x6 sb .x0 (8 * schedSlot) 0))
  crypt := .seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail))
  slots := schedSlot + 16
  total := schedSlot + 28
  buf := bufSlot
  lgG := 4
  keyRegs := [.x0]
  dataReg := .x23
  leftReg := .x24

/-- The registers of the arguments. -/
def modeRegs : Impl.Modes.AArch64.CtrRegs := ⟨.x1, .x2, .x3, .x4⟩

/-- SEED encryption's core for CBC encryption and the feedback modes: `x25` kept in `v31`
around its code. -/
abbrev fbCore : Impl.Modes.AArch64.Core := (dirCore .encrypt).viaV .x25 .v31

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := fbCore.cbcEncryptChained modeRegs .x25

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained modeRegs

/-- `vg_seed_ofb`. -/
def ofb : Prog isa := fbCore.fb .ofb modeRegs .x25

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := fbCore.fb .cfbEnc modeRegs .x25

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := fbCore.fb .cfbDec modeRegs .x25

end VG.Impl.Seed.AArch64
