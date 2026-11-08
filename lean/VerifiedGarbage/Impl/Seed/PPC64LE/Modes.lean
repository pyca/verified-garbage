module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Seed.PPC64LE.Ecb

/-!
# SEED's modes on PPC64LE

`blockCall d`: a call of `vg_seed_encrypt_blocks` or `vg_seed_decrypt_blocks`
(ECB's code, `Ecb.lean`, with the working space as an argument), which
`vg_seed_ecb_{en,de}crypt` make within a frame saving the link register
(`ecbCall d`, with their working space on the stack), and the modes' core
makes on one block.

`core d g`: the core for the modes (`Impl/Modes/PPC64LE/Seq.lean`), with
the round keys in the order of the direction `d` (encryption's for CBC
encryption, OFB and CFB, decryption's for CBC decryption), on a buffer of `g`
blocks. Its slots are the blocks function's working space (136, as
`Proof.Seed.blocksSig` has it) and the buffer's `g` blocks (from `bufSlot`),
then the modes' six. The blocks function computes the rounds of sixteen
blocks whatever their number, so a call on one block costs about as much as
on sixteen: the serial modes take one block a step with `dirCore d`, of one
block (144 slots in all, `[u64; 144]`), and CBC and CFB decryption take
sixteen a step while sixteen are left, then one, with `wideCore d`, of
sixteen (174 slots, `[u64; 174]`; `Impl/Modes/PPC64LE/Wide.lean`).

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
buffer, its `g` blocks, and the working space, the scratch buffer's first 136
slots. -/
def cryptHead (g : Nat) : List Instr :=
  [.addi .r4 Modes.PPC64LE.sb (8 * bufSlot), mov .r6 Modes.PPC64LE.sb, .li .r5 g]

/-- After the call, `sb` from `r8`, where the blocks function leaves the
working space's address, and `r3` back from the first round's key, where it
leaves the key pointer. -/
def cryptTail (d : Direction) : List Instr := [mov Modes.PPC64LE.sb .r8, .subi .r3 .r3 (keyStart d)]

/-- SEED's core for the modes, in the direction `d`, on `g` blocks. -/
def core (d : Direction) (g : Nat) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .seq (.block (cryptHead g)) (.seq (blockCall d) (.block (cryptTail d)))
  slots := bufSlot + 2 * g
  total := bufSlot + 2 * g + 6
  buf := bufSlot
  G := g
  bw := 4

/-- The core on one block, for the serial modes. -/
abbrev dirCore (d : Direction) : Modes.PPC64LE.Core := core d 1

/-- The core on sixteen blocks, for CBC and CFB decryption. -/
abbrev wideCore (d : Direction) : Modes.PPC64LE.Core := core d 16

/-- `vg_seed_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_cbc_decrypt_chained`, with its scratch buffer as the fifth
argument: sixteen blocks a step, then one. -/
def cbcDecryptChained : Prog isa :=
  (wideCore .decrypt).seq2 (Modes.Mode.cbcDecWide 4 16) (Modes.Mode.cbcDecChained 4) 4

/-- `vg_seed_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt`, with its scratch buffer as the fifth argument:
sixteen blocks a step, then one. -/
def cfbDecrypt : Prog isa :=
  (wideCore .encrypt).seq2 (Modes.Mode.cfbDecWide 4 16) (Modes.Mode.cfbDecEarly 4) 4

end VG.Impl.Seed.PPC64LE
