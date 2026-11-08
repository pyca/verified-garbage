module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced

/-!
# Triple DES's modes on PPC64LE

`dirCore d`: the verified block function of the direction `d`, called one
block at a time, as a core for the modes (`Impl/Modes/PPC64LE/Seq.lean`).
Its slots: the block function's 512-byte working space (slots 0 to 63, at
`sb`, which is `r5`, the block function's working-space argument) and the
buffer's one block (slot 64). `crypt` points `r4` at the buffer and calls
the block function, which keeps `r3` (the schedule, read in place: the modes
write only the data, the IV and the scratch buffer, which the schedule is
apart from), `r5` and `r29`–`r31` (the modes' state). 72 slots in all, with
the modes' (`[u64; 72]`).

`wideCore d`: the bitsliced ECB of the direction `d` on exactly 64 blocks
(`Bitslice.ecb64`, `Bitsliced.lean`), called (`ecb64Call`), on a buffer of
64 blocks, as a core for the modes whose blocks are
deciphered independently (`Impl/Modes/PPC64LE/Wide.lean`). Its slots: ECB's
1024-byte working space (slots 0 to 127, at `sb`), the buffer's 64 blocks
(from slot 128), then the modes': 200 slots in all (`[u64; 200]`). `crypt`
passes ECB the schedule (in `r3`), the buffer and the working space, and
takes `sb` and `r3` back from `r10` and `r7`, where ECB leaves them; ECB
saves and restores the callee-saved registers it uses, among them the
modes' `r29`–`r31`. ECB costs the same whatever the number of blocks, so the
blocks left after the groups of 64 cost a group each, about as much as the
block function on one.

`cbcEncryptChained`, `ofb`, `cfbEncrypt`, `cfb8Encrypt` and `cfb8Decrypt`
(schedule = r3, iv = r4, data = r5, n = r6, scratch = r7) are the modes
over `dirCore`, and `cbcDecryptChained` and `cfbDecrypt` over `wideCore`, 64
blocks a step, then one: CBC in both directions, and the others with the
encryption.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)
open VG.Spec.TripleDes (Direction)

/-- The buffer's block. -/
def bufSlot : Nat := 64

/-- Triple DES's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .seq (.block [.addi .r4 sb (8 * bufSlot)]) (Ecb.blockCall d)
  slots := bufSlot + 1
  total := 72
  buf := bufSlot
  G := 1
  bw := 2

/-- The wide core's buffer. -/
def wideBuf : Nat := 128

/-- A call of ECB on exactly 64 blocks: its code would put the modes' loops
out of the reach of their conditional branches if inlined. -/
def ecb64Call : Direction → Prog isa
  | .encrypt => .call "vg_triple_des_ecb64_encrypt" (Bitslice.ecb64 .encrypt)
  | .decrypt => .call "vg_triple_des_ecb64_decrypt" (Bitslice.ecb64 .decrypt)

/-- Triple DES's core for the modes, in the direction `d`, on 64 blocks. -/
def wideCore (d : Direction) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .seq (.block [rr .r6 sb, .addi .r4 sb (8 * wideBuf)])
    (.seq (ecb64Call d) (.block [rr sb .r10, rr .r3 .r7]))
  slots := wideBuf + 64
  total := wideBuf + 64 + 8
  buf := wideBuf
  G := 64
  bw := 2

/-- `vg_triple_des_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_triple_des_cbc_decrypt_chained`, with its scratch buffer as the fifth
argument: 64 blocks a step, then one. -/
def cbcDecryptChained : Prog isa :=
  (wideCore .decrypt).seq2 (Modes.Mode.cbcDecWide 2 64) (Modes.Mode.cbcDecChained 2) 6

/-- `vg_triple_des_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 2)

/-- `vg_triple_des_cfb_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb_decrypt`, with its scratch buffer as the fifth
argument: 64 blocks a step, then one. -/
def cfbDecrypt : Prog isa :=
  (wideCore .encrypt).seq2 (Modes.Mode.cfbDecWide 2 64) (Modes.Mode.cfbDecEarly 2) 6

/-- `vg_triple_des_cfb8_encrypt`, with its scratch buffer as the fifth argument. -/
def cfb8Encrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Enc 2)

/-- `vg_triple_des_cfb8_decrypt`, with its scratch buffer as the fifth argument. -/
def cfb8Decrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Dec 2)

end VG.Impl.TripleDes.PPC64LE
