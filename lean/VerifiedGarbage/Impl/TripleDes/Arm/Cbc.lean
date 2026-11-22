module

public import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Scrub.Arm.Sel
public import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES-CBC on ARMv7

`vg_triple_des_cbc_encrypt_chained` is the generic mode one block at a time
(`Impl/Modes/Arm/Seq.lean`, `CbcChained.lean`) over Triple DES's ECB
encryption, the function `vg_triple_des_ecb_encrypt` as emitted, which it
calls once per 8-byte block (`ecbCore`). `vg_triple_des_cbc_decrypt_chained`, whose blocks are
deciphered independently, is `Wide.lean`'s, a batch of blocks at a time.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_triple_des_ecb_encrypt` or `vg_triple_des_ecb_decrypt`,
as its artifact has it. -/
def ecbCode : Spec.TripleDes.Direction → Prog isa
  | .encrypt => Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Bitslice.encrypt
  | .decrypt => Impl.StackScratch.Arm.withRegScratchWiped 1024 .r3 256 Bitslice.decrypt

namespace Fn

open VG.Impl.Scrub.Arm

/-- `vg_triple_des_ecb_encrypt`: its code, then its cleanup
(`Impl/TripleDes/Arm/Fn.lean`), which leaves no word of the stack secret. -/
def ecbEncrypt : Prog isa := scrubSel 0 1024 [] (ecbCode .encrypt)

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 0 1024 [] (ecbCode .decrypt)

end Fn

/-- Triple DES's ECB function in the direction `d`, as the modes call it:
the artifact `vg_triple_des_ecb_encrypt` or `vg_triple_des_ecb_decrypt`, as
it is emitted, cleanup included (`Fn.ecbEncrypt`), so that its code is in
the crate once. -/
def ecbCore (d : Spec.TripleDes.Direction) : Core where
  name := match d with
    | .encrypt => Spec.TripleDes.ecbEncryptApi.name
    | .decrypt => Spec.TripleDes.ecbDecryptApi.name
  code := match d with
    | .encrypt => Fn.ecbEncrypt
    | .decrypt => Fn.ecbDecrypt
  bw := 2

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore .encrypt).seq cbcEncChained

end VG.Impl.TripleDes.Arm
