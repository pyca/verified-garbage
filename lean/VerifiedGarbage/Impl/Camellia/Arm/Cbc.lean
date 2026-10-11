import VerifiedGarbage.Impl.Camellia.Arm.Ecb
import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Impl.Modes.Arm.Seq
import VerifiedGarbage.Spec.Camellia.Contract

/-!
# Camellia-CBC on ARMv7

`vg_camellia_cbc_encrypt` and `vg_camellia_cbc_decrypt` are the generic
modes one block at a time (`Impl/Modes/Arm/Seq.lean`) over Camellia's ECB
functions, `vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt`, which
they call once per block with the number of rounds (`ecbCore`).
-/

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_camellia_ecb_encrypt` or `vg_camellia_ecb_decrypt`, as
its artifact has it. -/
def ecbCode (dir : Dir) : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (ecb dir)

/-- Camellia's ECB function in the direction `dir`, as the modes call it. -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Camellia.ecbEncryptApi.name
    | .decrypt => Spec.Camellia.ecbDecryptApi.name
  code := ecbCode dir
  bw := 4
  rounds := true

def cbcEncrypt : Prog isa := (ecbCore .encrypt).seq cbcEnc

def cbcDecrypt : Prog isa := (ecbCore .decrypt).seq cbcDec

end VG.Impl.Camellia.Arm
