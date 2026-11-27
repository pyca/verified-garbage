module

public import VerifiedGarbage.Impl.Seed.Arm.Ecb
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Wide
public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Impl.Modes.Arm.Wrap
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# SEED-CBC, SEED-OFB and SEED-CFB128 on ARMv7

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` are the generic modes (`Impl/Modes/Arm/Seq.lean`,
`CbcChained.lean`) over SEED's ECB functions, `vg_seed_ecb_encrypt_core` and
`vg_seed_ecb_decrypt_core` (`ecbCore`), which `cbcEncryptChained`, `ofb` and
`cfbEncrypt` call once per block, and `cbcDecryptChained` and `cfbDecrypt`,
whose blocks can be deciphered independently, once for a group of 8, 4 or 2
blocks, then once per block for those left (`Impl/Modes/Arm/Wide.lean`).
`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` call the same cores
(`Core.wrap`), so that their code is in the crate once.
-/

@[expose] public section

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Modes.Arm
open VG.Spec.Seed (Direction)

/-- The code of SEED's ECB core in the direction `dir`: `ecb dir` with its
working space in a frame on the stack, which its callers' cleanup zeroes. -/
def ecbCode (dir : Direction) : Prog isa := Impl.StackScratch.Arm.withRegScratch 752 .r3 (ecb dir)

/-- SEED's ECB function in the direction `dir`, as the modes and the public
ECB functions call it: its code as it is verified, without a cleanup, under a
name of its own (`vg_seed_ecb_encrypt_core`, which the emitter writes as an
internal function), whose callers' cleanup covers the frames of the call. -/
def ecbCore (dir : Direction) : Core where
  name := match dir with
    | .encrypt => Spec.Seed.ecbEncryptApi.name ++ "_core"
    | .decrypt => Spec.Seed.ecbDecryptApi.name ++ "_core"
  code := ecbCode dir
  bw := 4

namespace Fn

open VG.Impl.Scrub.Arm

/-- `vg_seed_ecb_encrypt`: a call of the core, then its cleanup, which zeroes
the stack its contract reserves (`Impl/Seed/Arm/Fn.lean`). -/
def ecbEncrypt : Prog isa := scrubAll 0 760 (ecbCore .encrypt).wrap

/-- `vg_seed_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubAll 0 760 (ecbCore .decrypt).wrap

end Fn

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
