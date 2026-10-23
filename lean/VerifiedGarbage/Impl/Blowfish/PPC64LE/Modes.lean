module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Blowfish.PPC64LE

/-!
# Blowfish's modes on PPC64LE

`dirCore up`: ECB's block function, inlined, as a core for the modes
(`Impl/Modes/PPC64LE/Seq.lean`), encrypting (`up`) or decrypting the block
in its buffer in place. Its slots: our caller's `r14`–`r17`, which the
block function uses (slots 0 to 3, saved and restored through `r6`, which
keeps the scratch buffer's address `sb` while the block function uses `r5`
for a half), and the buffer's one block (slot 4). The schedule is read in
place through `r3`, which the block function keeps, as it keeps `r6` and
`r29`–`r31` (the modes' state). 12 slots in all, with the modes'
(`[u64; 12]`).

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = r3, iv = r4, data = r5, n = r6, scratch = r7) are
the modes over it: CBC in both directions, and the others with the
encryption.
-/

@[expose] public section

namespace VG.Impl.Blowfish.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (sb mov)

/-- The buffer's block. -/
def bufSlot : Nat := 4

/-- The buffer's block encrypted (`up`) or decrypted in place: our caller's
`r14`–`r17` saved through `r6` (`sb`), the block into the halves, the block
function, the halves back, and `sb` and our caller's registers restored. -/
def modeCrypt (up : Bool) : Prog isa :=
  .seq (.block (mov .r6 sb :: save)) (.seq (.block [.li zero 0, .addi ptr .r6 (8 * bufSlot)])
    (.seq (.block loadBlock) (.seq (cipher up) (.seq (.block storeBlock) (.block (mov sb .r6 :: restore))))))

/-- Blowfish's core for the modes, encrypting (`up`) or decrypting. -/
def dirCore (up : Bool) : Modes.PPC64LE.Core where
  prepare := .block []
  crypt := modeCrypt up
  slots := bufSlot + 1
  total := 12
  buf := bufSlot
  G := 1
  bw := 2

/-- `vg_blowfish_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore true).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_blowfish_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := (dirCore false).seq (Modes.Mode.cbcDecChained 2)

/-- `vg_blowfish_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore true).seq (Modes.Mode.ofb 2)

/-- `vg_blowfish_cfb_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbEnc 2)

/-- `vg_blowfish_cfb_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa := (dirCore true).seq (Modes.Mode.cfbDec 2)

end VG.Impl.Blowfish.PPC64LE
