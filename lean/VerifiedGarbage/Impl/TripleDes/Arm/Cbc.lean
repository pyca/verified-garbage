import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Impl.Modes.Arm.Seq
import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES-CBC on ARMv7

`vg_triple_des_cbc_encrypt` and `vg_triple_des_cbc_decrypt` are the generic
modes one block at a time (`Impl/Modes/Arm/Seq.lean`) over Triple DES's ECB
functions, `vg_triple_des_ecb_encrypt` and `vg_triple_des_ecb_decrypt`,
which they call once per 8-byte block (`ecbCore`).
-/

namespace VG.Impl.TripleDes.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_triple_des_ecb_encrypt` or `vg_triple_des_ecb_decrypt`,
as its artifact has it. -/
def ecbCode : Spec.TripleDes.Direction → Prog isa
  | .encrypt => Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Ecb.encrypt
  | .decrypt => Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Ecb.decrypt

/-- Triple DES's ECB function in the direction `d`, as the modes call it. -/
def ecbCore (d : Spec.TripleDes.Direction) : Core where
  name := match d with
    | .encrypt => Spec.TripleDes.ecbEncryptApi.name
    | .decrypt => Spec.TripleDes.ecbDecryptApi.name
  code := ecbCode d
  bw := 2

def cbcEncrypt : Prog isa := (ecbCore .encrypt).seq cbcEnc

def cbcDecrypt : Prog isa := (ecbCore .decrypt).seq cbcDec

end VG.Impl.TripleDes.Arm
