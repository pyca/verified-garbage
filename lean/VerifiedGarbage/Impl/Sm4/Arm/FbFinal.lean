module

public import VerifiedGarbage.Impl.Sm4.Arm.Cbc
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# SM4-CFB128 of a message's last piece on ARMv7

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = r0, iv = r1, data = r2,
len = r3, scratch = [sp]): the generic CFB over a message's last piece, of
any length (`Impl/Modes/Arm/SeqFinal.lean`), over Sm4's ECB function, with
the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- SM4's ECB function in the direction `dir`, as the modes call it. -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Sm4.ecbEncryptApi.name
    | .decrypt => Spec.Sm4.ecbDecryptApi.name
  code := ecbCall dir
  bw := 4

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbEnc

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbDecF

end VG.Impl.Sm4.Arm
