import VerifiedGarbage.Impl.Seed.Arm.Ecb
import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Impl.Modes.Arm.Seq
import VerifiedGarbage.Spec.Seed.Contract

/-!
# SEED-CBC, SEED-OFB and SEED-CFB128 on ARMv7

`cbcEncrypt`, `cbcDecrypt`, `ofb`, `cfbEncrypt` and `cfbDecrypt` are the
generic modes one block at a time (`Impl/Modes/Arm/Seq.lean`) over SEED's
ECB functions, `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`, which they
call once per block (`ecbCore`).
-/

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Seed (Direction)

/-- The code of `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt`, as its
artifact has it. -/
def ecbCode (dir : Direction) : Prog isa := Impl.StackScratch.Arm.withRegScratchWiped 752 .r3 188 (ecb dir)

/-- SEED's ECB function in the direction `dir`, as the modes call it. -/
def ecbCore (dir : Direction) : Core where
  name := match dir with
    | .encrypt => Spec.Seed.ecbEncryptApi.name
    | .decrypt => Spec.Seed.ecbDecryptApi.name
  code := ecbCode dir
  bw := 4

/-- `vg_seed_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (ecbCore .encrypt).seq cbcEnc

/-- `vg_seed_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (ecbCore .decrypt).seq cbcDec

/-- `vg_seed_ofb`. -/
def ofb : Prog isa := (ecbCore .encrypt).seq Modes.Arm.ofb

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore .encrypt).seq cfbEnc

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq cfbDec

end VG.Impl.Seed.Arm
