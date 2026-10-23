module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb

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

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt`, `cfbDecrypt`,
`cfb8Encrypt` and `cfb8Decrypt` (schedule = r3, iv = r4, data = r5, n = r6,
scratch = r7) are the modes over it: CBC in both directions, and the others
with the encryption.
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

/-- `vg_triple_des_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_triple_des_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 2)

/-- `vg_triple_des_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 2)

/-- `vg_triple_des_cfb_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 2)

/-- `vg_triple_des_cfb8_encrypt`, with its scratch buffer as the fifth argument. -/
def cfb8Encrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Enc 2)

/-- `vg_triple_des_cfb8_decrypt`, with its scratch buffer as the fifth argument. -/
def cfb8Decrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Dec 2)

end VG.Impl.TripleDes.PPC64LE
