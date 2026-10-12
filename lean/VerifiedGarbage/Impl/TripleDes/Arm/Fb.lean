module

public import VerifiedGarbage.Impl.TripleDes.Arm.Cbc

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on ARMv7

`ofb`, `cfbEncrypt`, `cfbDecrypt`, `cfb8Encrypt` and `cfb8Decrypt` are the
generic modes of `Impl/Modes/Arm/Seq.lean` over Triple DES's ECB encryption
(`ecbCore .encrypt`), which they call once per 8-byte block (OFB, CFB64) or
once per byte (CFB8).
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := (ecbCore .encrypt).seq Modes.Arm.ofb

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore .encrypt).seq cfbEnc

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq cfbDec

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := (ecbCore .encrypt).seq cfb8Enc

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := (ecbCore .encrypt).seq cfb8Dec

end VG.Impl.TripleDes.Arm
