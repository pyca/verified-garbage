import VerifiedGarbage.Impl.Sm4.Arm.Ecb
import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Impl.Modes.Arm.Seq
import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4-CBC on ARMv7

`vg_sm4_cbc_encrypt` and `vg_sm4_cbc_decrypt` are the generic modes one
block at a time (`Impl/Modes/Arm/Seq.lean`) over SM4's ECB functions,
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`, which they call once per
block (`ecbCore`).
-/

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_sm4_ecb_encrypt` or `vg_sm4_ecb_decrypt`, as its
artifact has it. -/
def ecbCode (dir : Dir) : Prog isa := Impl.StackScratch.Arm.withRegScratchWiped 1456 .r3 364 (ecb dir)

/-- SM4's ECB function in the direction `dir`, as the modes call it. -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Sm4.ecbEncryptApi.name
    | .decrypt => Spec.Sm4.ecbDecryptApi.name
  code := ecbCode dir
  bw := 4

def cbcEncrypt : Prog isa := (ecbCore .encrypt).seq cbcEnc

def cbcDecrypt : Prog isa := (ecbCore .decrypt).seq cbcDec

end VG.Impl.Sm4.Arm
