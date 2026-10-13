module

public import VerifiedGarbage.Impl.Camellia.Arm.Cbc

/-!
# Camellia-OFB and Camellia-CFB128 on ARMv7

`ofb`, `cfbEncrypt` and `cfbDecrypt` are the generic modes of
`Impl/Modes/Arm/Seq.lean` one block at a time over Camellia's ECB encryption,
`vg_camellia_ecb_encrypt`, which they call once per block with the number of
rounds (`ecbCore .encrypt`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := (ecbCore .encrypt).seq Modes.Arm.ofb

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore .encrypt).seq cfbEnc

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq cfbDec

end VG.Impl.Camellia.Arm
