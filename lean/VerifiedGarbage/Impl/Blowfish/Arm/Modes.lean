module

public import VerifiedGarbage.Impl.Blowfish.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.Blowfish.Contract

/-!
# Blowfish-CBC, Blowfish-OFB and Blowfish-CFB64 on ARMv7

`cbcEncrypt`, `cbcDecrypt`, `ofb`, `cfbEncrypt` and `cfbDecrypt` are the
generic modes one block at a time (`Impl/Modes/Arm/Seq.lean`) over
Blowfish's ECB functions, `vg_blowfish_ecb_encrypt` and
`vg_blowfish_ecb_decrypt`, which they call once per block (`ecbCore`).
-/

@[expose] public section

namespace VG.Impl.Blowfish.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_blowfish_ecb_encrypt` (`up`) or `vg_blowfish_ecb_decrypt`,
as its artifact has it. -/
def ecbCode (up : Bool) : Prog isa := Impl.StackScratch.Arm.withRegScratchWiped 256 .r3 12 (ecb up)

/-- Blowfish's ECB function, encryption (`up`) or decryption, as the modes
call it. -/
def ecbCore (up : Bool) : Core where
  name := if up then Spec.Blowfish.ecbEncryptApi.name else Spec.Blowfish.ecbDecryptApi.name
  code := ecbCode up
  bw := 2

/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore true).seq cbcEncChained

/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore false).seq cbcDecChained

/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := (ecbCore true).seq Modes.Arm.ofb

/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore true).seq cfbEnc

/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore true).seq cfbDec

end VG.Impl.Blowfish.Arm
