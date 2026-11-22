module

public import VerifiedGarbage.Impl.Seed.Arm.Ecb
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Wide
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Impl.Scrub.Arm.Sel

/-!
# SEED-CBC, SEED-OFB and SEED-CFB128 on ARMv7

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` are the generic modes (`Impl/Modes/Arm/Seq.lean`,
`CbcChained.lean`) over SEED's ECB functions, `vg_seed_ecb_encrypt` and
`vg_seed_ecb_decrypt` as they are emitted (`ecbCore`), which `cbcEncryptChained`, `ofb` and
`cfbEncrypt` call once per block, and `cbcDecryptChained` and `cfbDecrypt`,
whose blocks can be deciphered independently, once for a group of 8, 4 or 2
blocks, then once per block for those left (`Impl/Modes/Arm/Wide.lean`).
-/

@[expose] public section

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Seed (Direction)

/-- The code of `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt`, as its
artifact has it. -/
def ecbCode (dir : Direction) : Prog isa := Impl.StackScratch.Arm.withRegScratchWiped 752 .r3 188 (ecb dir)

namespace Fn

open VG.Impl.Scrub.Arm

/-- `vg_seed_ecb_encrypt`: its code, then its cleanup (`Impl/Seed/Arm/Fn.lean`),
which leaves no word of the stack secret. -/
def ecbEncrypt : Prog isa := scrubSel 0 752 [] (ecbCode .encrypt)

/-- `vg_seed_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 0 752 [] (ecbCode .decrypt)

end Fn

/-- SEED's ECB function in the direction `dir`, as the modes call it: the
artifact `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt`, as it is emitted,
cleanup included (`Fn.ecbEncrypt`), so that its code is in the crate once. -/
def ecbCore (dir : Direction) : Core where
  name := match dir with
    | .encrypt => Spec.Seed.ecbEncryptApi.name
    | .decrypt => Spec.Seed.ecbDecryptApi.name
  code := match dir with
    | .encrypt => Fn.ecbEncrypt
    | .decrypt => Fn.ecbDecrypt
  bw := 4

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore .encrypt).seq cbcEncChained

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore .decrypt).seq8 cbcDecChained cbcDecW

/-- `vg_seed_ofb`. -/
def ofb : Prog isa := (ecbCore .encrypt).seq Modes.Arm.ofb

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore .encrypt).seq cfbEnc

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore .encrypt).seq8 cfbDec cfbDecW

end VG.Impl.Seed.Arm
