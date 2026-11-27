module

public import VerifiedGarbage.Impl.Camellia.Arm.Keyed
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Wide
public import VerifiedGarbage.Spec.Camellia.Contract
public import VerifiedGarbage.Impl.Modes.Arm.Wrap
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Camellia-CBC on ARMv7

`vg_camellia_cbc_encrypt_chained` and `vg_camellia_cbc_decrypt_chained`
are the generic modes (`Impl/Modes/Arm/Seq.lean`), which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`). Decryption, whose blocks
can be deciphered independently, calls Camellia's ECB function,
its core `vg_camellia_ecb_decrypt_core`, with the number of rounds (`ecbCore`), once for a
group of 8, 4 or 2 blocks, then once per block for those left
(`Impl/Modes/Arm/Wide.lean`). Encryption, whose every block needs the one
before, has the table of subkeys built once, in its own working space
(`Impl/Modes/Arm/SeqKeyed.lean`: `vg_camellia_ecb_encrypt_keys`), and calls
`vg_camellia_ecb_keyed` on each block (`Keyed.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of Camellia's ECB core in the direction `dir`: `ecb dir` with
its working space in a frame on the stack, which its callers' cleanup
zeroes. -/
def ecbCode (dir : Dir) : Prog isa := Impl.StackScratch.Arm.withStackScratch 2816 0 (ecb dir)

/-- Camellia's ECB function in the direction `dir`, as the modes and the
public ECB functions call it: its code as it is verified, without a cleanup,
under a name of its own (`vg_camellia_ecb_encrypt_core`, which the emitter
writes as an internal function), whose callers' cleanup covers the frames of
the call. -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Camellia.ecbEncryptApi.name ++ "_core"
    | .decrypt => Spec.Camellia.ecbDecryptApi.name ++ "_core"
  code := ecbCode dir
  bw := 4
  rounds := true

namespace Fn

open VG.Impl.Scrub.Arm

/-- `vg_camellia_ecb_encrypt`: a call of the core, then its cleanup, which
zeroes the stack its contract reserves: the core's 2816 bytes and the call's
frame of 8, within 2832, a frame size of the model. -/
def ecbEncrypt : Prog isa := scrubAll 0 2832 (ecbCore .encrypt).wrap

/-- `vg_camellia_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubAll 0 2832 (ecbCore .decrypt).wrap

end Fn

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (scrCore .encrypt).seqK (keyed .encrypt) cbcEncChained

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore .decrypt).seq8 cbcDecChained cbcDecW

end VG.Impl.Camellia.Arm
