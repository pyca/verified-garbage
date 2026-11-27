module

public import VerifiedGarbage.Impl.Seed.X86.AesNi
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal
public import VerifiedGarbage.Impl.Modes.CbcChained

/-!
# SEED's chained modes by the AES S-box on x86 (32-bit)

The modes whose blocks each need the one before, over the core that
enciphers one block at a time (`Impl.Seed.X86.AesNi.core`): CBC encryption,
OFB and CFB128 encryption of whole blocks, and CFB128 and OFB of a
message's last piece (cdecl: schedule, iv, data, the number of blocks or of
bytes, scratch).
-/

@[expose] public section

namespace VG.Impl.Seed.X86.AesNi

open VG.X86

/-- `vg_seed_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := core.seq (Modes.Mode.cbcEncChained 4)

/-- `vg_seed_ofb`, with its scratch buffer as the fifth argument. -/
def ofb : Prog isa := core.seq (Modes.Mode.ofb 4)

/-- `vg_seed_cfb128_encrypt`, with its scratch buffer as the fifth argument. -/
def cfbEncrypt : Prog isa := core.seq (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := core.seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := core.seqFinal (Modes.Mode.cfbDec 4)

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa := core.seqFinal (Modes.Mode.ofb 4)

end VG.Impl.Seed.X86.AesNi
