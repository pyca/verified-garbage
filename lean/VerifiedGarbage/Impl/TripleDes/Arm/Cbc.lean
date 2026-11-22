module

public import VerifiedGarbage.Impl.TripleDes.Arm.Bitsliced
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Wrap
public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES-CBC on ARMv7

`vg_triple_des_cbc_encrypt_chained` is the generic mode one block at a time
(`Impl/Modes/Arm/Seq.lean`, `CbcChained.lean`) over Triple DES's ECB
encryption, its core `vg_triple_des_ecb_encrypt_core`, which it calls once
per 8-byte block (`ecbCore`), as `vg_triple_des_ecb_encrypt` does
(`Core.wrap`). `vg_triple_des_cbc_decrypt_chained`, whose blocks are
deciphered independently, is `Wide.lean`'s, a batch of blocks at a time.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of Triple DES's ECB core in the direction `d`: the bitsliced
passes with their working space in a frame on the stack, which its callers'
cleanup zeroes. -/
def ecbCode : Spec.TripleDes.Direction → Prog isa
  | .encrypt => Impl.StackScratch.Arm.withRegScratch 1024 .r3 Bitslice.encrypt
  | .decrypt => Impl.StackScratch.Arm.withRegScratch 1024 .r3 Bitslice.decrypt

/-- Triple DES's ECB function in the direction `d`, as the modes and the
public ECB functions call it: its code as it is verified, without a cleanup,
under a name of its own (`vg_triple_des_ecb_encrypt_core`, which the emitter
writes as an internal function), whose callers' cleanup covers the frames of
the call. -/
def ecbCore (d : Spec.TripleDes.Direction) : Core where
  name := match d with
    | .encrypt => Spec.TripleDes.ecbEncryptApi.name ++ "_core"
    | .decrypt => Spec.TripleDes.ecbDecryptApi.name ++ "_core"
  code := ecbCode d
  bw := 2

namespace Fn

open VG.Impl.Scrub.Arm

/-- `vg_triple_des_ecb_encrypt`: a call of the core, then its cleanup, which
zeroes the stack its contract reserves: the core's 1024 bytes and the call's
frame of 8, within 1040, a frame size of the model. -/
def ecbEncrypt : Prog isa := scrubAll 0 1040 (ecbCore .encrypt).wrap

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubAll 0 1040 (ecbCore .decrypt).wrap

end Fn

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (ecbCore .encrypt).seq cbcEncChained

end VG.Impl.TripleDes.Arm
