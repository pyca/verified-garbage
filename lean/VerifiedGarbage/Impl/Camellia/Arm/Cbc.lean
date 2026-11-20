module

public import VerifiedGarbage.Impl.Camellia.Arm.Keyed
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Modes.Arm.CbcChained
public import VerifiedGarbage.Impl.Modes.Arm.Wide
public import VerifiedGarbage.Spec.Camellia.Contract

/-!
# Camellia-CBC on ARMv7

`vg_camellia_cbc_encrypt_chained` and `vg_camellia_cbc_decrypt_chained`
are the generic modes (`Impl/Modes/Arm/Seq.lean`), which return the chaining
value in the IV (`Impl/Modes/Arm/CbcChained.lean`). Decryption, whose blocks
can be deciphered independently, calls Camellia's ECB function,
`vg_camellia_ecb_decrypt`'s code, with the number of rounds (`ecbCore`), once for a
group of 8, 4 or 2 blocks, then once per block for those left
(`Impl/Modes/Arm/Wide.lean`). Encryption, whose every block needs the one
before, has the table of subkeys built once, in its own working space
(`Impl/Modes/Arm/SeqKeyed.lean`: `vg_camellia_ecb_encrypt_keys`), and calls
`vg_camellia_ecb_keyed` on each block (`Keyed.lean`).
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- The code of `vg_camellia_ecb_encrypt` or `vg_camellia_ecb_decrypt`, as
its artifact has it. -/
def ecbCode (dir : Dir) : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 2816 0 680 (ecb dir)

/-- Camellia's ECB function in the direction `dir`, as the modes call it:
its code as it is verified, under a name of its own
(`vg_camellia_ecb_encrypt_entry`), which the emitter writes as an internal
function, since the artifact `vg_camellia_ecb_encrypt` is that code
scrubbed (`Proof/Camellia/Arm/Scrub.lean`). -/
def ecbCore (dir : Dir) : Core where
  name := match dir with
    | .encrypt => Spec.Camellia.ecbEncryptApi.name ++ "_entry"
    | .decrypt => Spec.Camellia.ecbDecryptApi.name ++ "_entry"
  code := ecbCode dir
  bw := 4
  rounds := true

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (scrCore .encrypt).seqK (keyed .encrypt) cbcEncChained

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (ecbCore .decrypt).seq8 cbcDecChained cbcDecW

end VG.Impl.Camellia.Arm
