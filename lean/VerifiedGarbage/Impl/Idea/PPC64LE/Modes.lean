module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Idea.PPC64LE

/-!
# IDEA's modes on PPC64LE

`core`: ECB's block code (`cryptBlock`), inlined, as a core for the modes
(`Impl/Modes/PPC64LE/Seq.lean`), running IDEA in place on the block in its
buffer under the subkeys at `r3`, read in place: the encryption subkeys for
encryption, the decryption subkeys (`vg_idea_invert_key`) for CBC
decryption. It sets the mask in `r0` and points `r4` at the buffer (slot 0),
and uses only volatile registers besides: it keeps `r3`, `sb` (`r5`) and
`r29`–`r31` (the modes' state). 8 slots in all, with the modes'
(`[u64; 8]`).

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = r3, iv = r4, data = r5, n = r6, scratch = r7) are
the modes over it.
-/

@[expose] public section

namespace VG.Impl.Idea.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (sb)

/-- The buffer's block. -/
def bufSlot : Nat := 0

/-- IDEA's core for the modes. -/
def core : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := .seq (.block setMask) (.seq (.block [.addi .r4 sb (8 * bufSlot)]) (.block cryptBlock))
  slots := bufSlot + 1
  total := 8
  buf := bufSlot
  G := 1
  bw := 2

/-- `vg_idea_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := core.seq (Modes.Mode.cbcEncChained 2)

/-- `vg_idea_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := core.seq (Modes.Mode.cbcDecChained 2)

/-- `vg_idea_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := core.seq (Modes.Mode.ofb 2)

/-- `vg_idea_cfb64_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := core.seq (Modes.Mode.cfbEnc 2)

/-- `vg_idea_cfb64_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa := core.seq (Modes.Mode.cfbDec 2)

end VG.Impl.Idea.PPC64LE
