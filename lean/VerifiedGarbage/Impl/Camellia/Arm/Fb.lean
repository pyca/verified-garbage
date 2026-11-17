module

public import VerifiedGarbage.Impl.Camellia.Arm.Cbc

/-!
# Camellia-OFB and Camellia-CFB128 on ARMv7

`ofb`, `cfbEncrypt` and `cfbDecrypt` are the generic modes of
`Impl/Modes/Arm/Seq.lean` over Camellia's ECB encryption,
`vg_camellia_ecb_encrypt`, which they call with the number of rounds
(`ecbCore .encrypt`): `ofb` and `cfbEncrypt` once per block, and
`cfbDecrypt`, whose blocks can be deciphered independently, once for a
group of 8, 4 or 2 blocks, then once per block for those left
(`Impl/Modes/Arm/Wide.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := (ecbCore .encrypt).seq Modes.Arm.ofb

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore .encrypt).seq cfbEnc

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq8 cfbDec cfbDecW

end VG.Impl.Camellia.Arm
