module

public import VerifiedGarbage.Impl.Camellia.Arm.Cbc

/-!
# Camellia-OFB and Camellia-CFB128 on ARMv7

`ofb`, `cfbEncrypt` and `cfbDecrypt` are the generic modes of
`Impl/Modes/Arm/Seq.lean` over Camellia's ECB encryption. `cfbDecrypt`,
whose blocks can be deciphered independently, calls
`vg_camellia_ecb_encrypt` with the number of rounds (`ecbCore .encrypt`),
once for a group of 8, 4 or 2 blocks, then once per block for those left
(`Impl/Modes/Arm/Wide.lean`). `ofb` and `cfbEncrypt`, whose every block
needs the one before, have the table of subkeys built once, in their own
working space (`Impl/Modes/Arm/SeqKeyed.lean`:
`vg_camellia_ecb_encrypt_keys`), and call `vg_camellia_ecb_keyed` on each
block (`Keyed.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := (scrCore .encrypt).seqK (keyed .encrypt) Modes.Arm.ofb

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (scrCore .encrypt).seqK (keyed .encrypt) cfbEnc

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq8 cfbDec cfbDecW

end VG.Impl.Camellia.Arm
