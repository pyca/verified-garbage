module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Seed.PPC64LE.Ecb

/-!
# SEED's modes on PPC64LE

`dirCore d`: ECB's batch (`Ecb.lean`), inlined, as a core for the modes
(`Impl/Modes/PPC64LE/Seq.lean`), on one block: the block of its buffer
(slot `bufSlot`, after ECB's 130 slots) is copied into lane 0 of the
arrays (ECB's copy loop, once), sixteen rounds run on every lane
(`rounds d`, the other fifteen lanes holding whatever they hold), and lane
0 is copied back, under the schedule at `r3`, read in place, the round keys in
the order of the direction `d`: encryption's for CBC encryption, OFB and
CFB, decryption's for CBC decryption.

The rounds use the callee-saved registers `r14`–`r31` and the scratch
buffer's address in `r8` (ECB's base). The core copies the modes' base
(`sb`, `r5`) to `r8`, saves the caller's `r14`–`r28` in ECB's slots for
them (`savedRegs`) and restores them after the block; the modes' state
(`r29`–`r31`) waits in `r4`–`r6`, which the rounds keep, so that it never
passes through memory. 138 slots in all, with the modes' (`[u64; 138]`).

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = r3, iv = r4, data = r5, n = r6, scratch = r7) are
the modes over it.
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE

open VG.PPC64LE
open VG.Impl.Aes.PPC64LE (movR stS ldS)
open VG.Spec.Seed (Direction)

/-- The buffer's block, after ECB's slots. -/
def bufSlot : Nat := scratchSlots

/-- The caller's registers the core saves around a block: `r14`–`r28`. -/
def callerRegs : List (Reg × Nat) := savedRegs.take 15

/-- The caller's registers saved, the bases, and the key pointer at the
first round's key; one block to copy, from the buffer, into lane 0. -/
def coreIn (d : Direction) : List Instr :=
  [movR .r8 .r5] ++ callerRegs.map (fun (r, k) => stS k r) ++
    ([.addi .r3 .r3 (keyStart d), .li .r10 1, .addi .r6 .r8 (8 * bufSlot), movR .r7 .r8] : List Instr)

/-- The modes' state to `r4`–`r6`, which the rounds keep. -/
def park : List Instr := [movR .r4 .r29, movR .r5 .r30, movR .r6 .r31]

/-- The modes' state back; one block to copy out, from lane 0 to the buffer. -/
def unpark : List Instr :=
  [movR .r29 .r4, movR .r30 .r5, movR .r31 .r6, .li .r10 1, .addi .r6 .r8 (8 * bufSlot), movR .r7 .r8]

/-- The key pointer and `sb` back, and the caller's registers restored. -/
def coreOut (d : Direction) : List Instr :=
  [.subi .r3 .r3 (keyStart d), movR .r5 .r8] ++ callerRegs.map (fun (r, k) => ldS r k)

/-- The block: copied into lane 0, enciphered, and copied back. -/
def coreCrypt (d : Direction) : Prog isa :=
  .seq (.block (coreIn d)) (.seq (.loop (.block copyInBody) (.nonzero .d .r10)) (.seq (.block park)
    (.seq (rounds d) (.seq (.block unpark) (.seq (.loop (.block copyOutBody) (.nonzero .d .r10))
      (.block (coreOut d)))))))

/-- SEED's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := coreCrypt d
  slots := bufSlot + 2
  total := bufSlot + 8
  buf := bufSlot
  G := 1
  bw := 4

/-- `vg_seed_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_seed_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 4)

end VG.Impl.Seed.PPC64LE
