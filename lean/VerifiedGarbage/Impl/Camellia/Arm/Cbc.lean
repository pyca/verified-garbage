module

public import VerifiedGarbage.Impl.Camellia.Arm.Ecb
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.Camellia.Contract

/-!
# Camellia-CBC on ARMv7

`vg_camellia_cbc_encrypt_chained` and `vg_camellia_cbc_decrypt_chained`
are the generic modes one block at a time (`Impl/Modes/Arm/Seq.lean`),
which return the chaining value in the IV (`Impl/Modes/Arm/CbcChained.lean`),
over Camellia's ECB functions, `vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt`, which
they call once per block with the number of rounds (`ecbCore`).
-/

@[expose] public section

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

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore .encrypt).seq cbcEncChained

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore .decrypt).seq cbcDecChained

end VG.Impl.Camellia.Arm
