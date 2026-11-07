module

public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal

/-!
# SEED-CFB128 and SEED-OFB of a message's last piece on PPC64LE

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r3, iv = r4, data = r5,
len = r6, scratch = r7): the modes' CFB and OFB over a message's last piece, of any
length (`Impl/Modes/PPC64LE/SeqFinal.lean`), over SEED's core, with the
arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Seed.PPC64LE

open VG.PPC64LE

/-- `vg_seed_cfb128_encrypt_final`, with its scratch buffer as the fifth argument. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt_final`, with its scratch buffer as the fifth argument. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 4)

/-- `vg_seed_ofb_final`, with its scratch buffer as the fifth argument. -/
def ofbFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.ofb 4)

end VG.Impl.Seed.PPC64LE
