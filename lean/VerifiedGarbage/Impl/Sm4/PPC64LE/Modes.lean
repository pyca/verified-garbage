module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared

/-!
# SM4's modes on PPC64LE

`dirCore d`: SM4's core for the modes (`Impl/Modes/PPC64LE/Seq.lean`), its
round keys in the order of the direction `d`: encryption's for CBC
encryption, OFB and CFB, decryption's for CBC decryption. It calls ECB's two
halves (`Prepared.lean`): `prepare` calls `vg_sm4_prepare_keys`, which sets
the masks and builds the table of bitsliced round keys, once; `crypt` calls
`vg_sm4_crypt_prepared`, which transforms the sixteen blocks of the tail
buffer in place, of which the modes use the first (they take one step at a
time).

The core's slots are the functions' 402 (`slots`), the modes' six after
them: 408 in all (`[u64; 408]`). Neither function writes `r5` (`sb`) or `r7`,
so `sb` survives each call, and `r7` keeps `r3` (the schedule's address,
the modes' key argument) across it.

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` (schedule = r3, iv = r4, data = r5, n = r6, scratch = r7) are
the modes over it.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (mov)

/-- The bit `vg_sm4_prepare_keys` takes for the direction. -/
def dirBit : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- `vg_sm4_prepare_keys(r3, d, sb, slots)`, keeping `r3` in `r7`. -/
def prepareCall (d : Dir) : Prog isa :=
  .seq (.block [mov .r7 .r3, .li .r4 (dirBit d), .li .r6 slots])
    (.seq (.call "vg_sm4_prepare_keys" prepareKeys) (.block [mov .r3 .r7]))

/-- `vg_sm4_crypt_prepared(sb, slots)`, keeping `r3` in `r7`. -/
def cryptCall : Prog isa :=
  .seq (.block [mov .r7 .r3, mov .r3 Modes.PPC64LE.sb, .li .r4 slots])
    (.seq (.call "vg_sm4_crypt_prepared" cryptPrepared) (.block [mov .r3 .r7]))

/-- SM4's core for the modes, in the direction `d`. -/
def dirCore (d : Dir) : Modes.PPC64LE.Core where
  prepare := prepareCall d
  crypt := cryptCall
  slots := slots
  total := slots + 6
  buf := tailSlot
  G := 1
  bw := 4

/-- `vg_sm4_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4)

/-- `vg_sm4_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4)

/-- `vg_sm4_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 4)

/-- `vg_sm4_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 4)

/-- `vg_sm4_cfb128_decrypt`, with its scratch buffer as the fifth argument. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 4)

end VG.Impl.Sm4.PPC64LE
