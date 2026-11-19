module

public import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES-CBC on ARMv7

`vg_triple_des_cbc_encrypt_chained` is the generic mode one block at a time
(`Impl/Modes/Arm/Seq.lean`, `CbcChained.lean`) over Triple DES's ECB
encryption, `vg_triple_des_ecb_encrypt`'s code, which it calls once per
8-byte block (`ecbCore`). `vg_triple_des_cbc_decrypt_chained`, whose blocks are
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

/-- Triple DES's ECB function in the direction `d`, as the modes call it:
its code as it is verified, under a name of its own
(`vg_triple_des_ecb_encrypt_entry`), which the emitter writes as an internal
function, since the artifact `vg_triple_des_ecb_encrypt` is that code
scrubbed (`Proof/TripleDes/Arm/Scrub.lean`). -/
def ecbCore (d : Spec.TripleDes.Direction) : Core where
  name := match d with
    | .encrypt => Spec.TripleDes.ecbEncryptApi.name ++ "_entry"
    | .decrypt => Spec.TripleDes.ecbDecryptApi.name ++ "_entry"
  code := ecbCode d
  bw := 2

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore .encrypt).seq cbcEncChained

end VG.Impl.TripleDes.Arm
