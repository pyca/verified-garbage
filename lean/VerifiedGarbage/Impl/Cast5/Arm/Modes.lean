module

public import VerifiedGarbage.Impl.Cast5.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.Cast5.Contract

/-!
# CAST5-CBC, CAST5-OFB and CAST5-CFB64 on ARMv7

The generic modes one block at a time (`Impl/Modes/Arm/Seq.lean`, `CbcChained.lean`) over
CAST5's ECB functions, `vg_cast5_ecb_encrypt` and `vg_cast5_ecb_decrypt`,
which they call once per block with the number of rounds and with their
256-byte working space (a stack argument) at the end of the mode's own
(`ecbCore`).
-/

@[expose] public section

namespace VG.Impl.Cast5.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- CAST5's ECB function, encryption (`up`) or decryption, as the modes call
it. -/
def ecbCore (up : Bool) : Core where
  name := if up then Spec.Cast5.ecbEncryptApi.name else Spec.Cast5.ecbDecryptApi.name
  code := ecb up
  bw := 2
  rounds := true
  stackScratch := 256

/-- `vg_cast5_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore true).seq cbcEncChained

/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore false).seq cbcDecChained

/-- `vg_cast5_ofb`. -/
def ofb : Prog isa := (ecbCore true).seq Modes.Arm.ofb

/-- `vg_cast5_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (ecbCore true).seq cfbEnc

/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (ecbCore true).seq cfbDec

end VG.Impl.Cast5.Arm
