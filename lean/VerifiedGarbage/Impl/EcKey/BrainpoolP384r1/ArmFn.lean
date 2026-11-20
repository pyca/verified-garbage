module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# brainpoolP384r1 public keys on 32-bit ARM, as emitted

`vg_ec_brainpoolp384r1_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ec_brainpoolp384r1_public_key`. -/
def publicKeyBrainpoolP384r1 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1Comb

/-- `vg_ec_brainpoolp384r1_public_key_umaal`. -/
def publicKeyBrainpoolP384r1U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1CombU

/-- `vg_ec_brainpoolp384r1_compress_public_key`. -/
def compressBrainpoolP384r1 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.brainpoolp384r1)

/-- `vg_ec_brainpoolp384r1_compress_public_key_umaal`. -/
def compressBrainpoolP384r1U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.brainpoolp384r1With true))

/-- `vg_ec_brainpoolp384r1_decompress_public_key`. -/
def decompressBrainpoolP384r1 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.brainpoolp384r1)

/-- `vg_ec_brainpoolp384r1_decompress_public_key_umaal`. -/
def decompressBrainpoolP384r1U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.brainpoolp384r1With true))

end VG.Impl.EcKey.Arm.Fn
