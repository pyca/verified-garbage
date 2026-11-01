module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Seed.PPC64LE.Ecb

/-!
# SEED's modes on PPC64LE

`blockCall d`: a call of `vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks`
(ECB's code, `Ecb.lean`, with the working space as an argument), which
`vg_seed_ecb_{en,de}crypt` make within a frame saving the link register
(`ecbCall d`, with their working space on the stack), and the modes' core
makes on one block.

`dirCore d`: the core for the modes (`Impl/Modes/PPC64LE/Seq.lean`), with
the round keys in the order of the direction `d`: encryption's for CBC
encryption, OFB and CFB, decryption's for CBC decryption. Its slots are the
blocks function's working space (136, as `Proof.Seed.blocksSig` has it) and
the buffer's block (`bufSlot`), then the modes' six: 144 in all, with the
modes' (`[u64; 144]`).

The blocks function writes every general-purpose register but `r2`, and
restores the callee-saved ones (`r14`–`r31`, the modes' state `r29`–`r31`
among them, which it saves around each batch's rounds, so that the analysis
of constant time finds them as public after the call as before). It leaves
the working space's address in `r8`, from which the core takes `sb` back,
which the analysis then knows to point at the scratch buffer, and the key
pointer at the first round's key. The call leaves the link register
unknown; the modes save the return address in their slot.

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = r3, iv = r4, data = r5, n = r6, scratch = r7) are
the modes over it.
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (mov)
open VG.Spec.Seed (Direction)

/-- A call of `vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks` (the ECB
code with the working space as an argument). -/
def blockCall : Direction → Prog isa
  | .encrypt => .call "vg_seed_encrypt_blocks" encrypt
  | .decrypt => .call "vg_seed_decrypt_blocks" decrypt

/-- `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt` within its frame, which
allocates the working space at `r6`: a call of the blocks function in the
direction `d`, the link register saved in a frame. -/
def ecbCall (d : Direction) : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) (blockCall d) (.pop .r0)) (.block [.mtlr .r0]))

/-- The buffer's block, after the blocks function's working space. -/
def bufSlot : Nat := 136

/-- Before the call, the arguments: the schedule (in `r3` already), the
buffer, one block, and the working space, the scratch buffer's first 136
slots. -/
def cryptHead : List Instr :=
  [.addi .r4 Modes.PPC64LE.sb (8 * bufSlot), mov .r6 Modes.PPC64LE.sb, .li .r5 1]

/-- After the call, `sb` from `r8`, where the blocks function leaves the
working space's address, and `r3` back from the first round's key, where it
leaves the key pointer. -/
def cryptTail (d : Direction) : List Instr := [mov Modes.PPC64LE.sb .r8, .subi .r3 .r3 (keyStart d)]

/-- SEED's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .seq (.block cryptHead) (.seq (blockCall d) (.block (cryptTail d)))
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
