import VerifiedGarbage.Impl.Sm4.Arm.Cbc

/-!
# SM4-OFB and SM4-CFB128 on ARMv7

`ofb`, `cfbEncrypt` and `cfbDecrypt` are the generic modes of
`Impl/Modes/Arm/Seq.lean` over SM4's ECB encryption (`ecbCore .encrypt`),
which they call once per block.
-/

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := (ecbCore .encrypt).seq Modes.Arm.ofb

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore .encrypt).seq cfbEnc

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq cfbDec

end VG.Impl.Sm4.Arm
