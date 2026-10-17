module

public import VerifiedGarbage.Impl.Idea.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.Idea.Contract

/-!
# IDEA-CBC, IDEA-OFB and IDEA-CFB64 on ARMv7

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt` and
`cfbDecrypt` are the generic modes one block at a time
(`Impl/Modes/Arm/Seq.lean`, `CbcChained.lean`) over IDEA's
ECB function, `vg_idea_ecb`, which they call once per block (`ecbCore`):
under the encryption subkeys, or for CBC decryption under the decryption
subkeys, which its caller passes.
-/

@[expose] public section

namespace VG.Impl.Idea.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_idea_ecb`, as its artifact has it. -/
def ecbCode : Prog isa := Impl.StackScratch.Arm.withRegScratch 32 .r3 ecb

/-- IDEA's ECB function, as the modes call it. -/
def ecbCore : Core where
  name := Spec.Idea.ecbApi.name
  code := ecbCode
  bw := 2

/-- `vg_idea_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := ecbCore.seq cbcEncChained

/-- `vg_idea_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := ecbCore.seq cbcDecChained

/-- `vg_idea_ofb`. -/
def ofb : Prog isa := ecbCore.seq Modes.Arm.ofb

/-- `vg_idea_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := ecbCore.seq cfbEnc

/-- `vg_idea_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := ecbCore.seq cfbDec

end VG.Impl.Idea.Arm
