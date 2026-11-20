module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# brainpoolP512r1 public keys on 32-bit ARM, as emitted

`vg_ec_brainpoolp512r1_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Residue.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ec_brainpoolp512r1_public_key`. -/
def publicKeyBrainpoolP512r1 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyBrainpoolP512r1Comb

/-- `vg_ec_brainpoolp512r1_public_key_umaal`. -/
def publicKeyBrainpoolP512r1U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyBrainpoolP512r1CombU

/-- `vg_ec_brainpoolp512r1_compress_public_key`. -/
def compressBrainpoolP512r1 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.brainpoolp512r1)

/-- `vg_ec_brainpoolp512r1_compress_public_key_umaal`. -/
def compressBrainpoolP512r1U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.brainpoolp512r1With true))

/-- `vg_ec_brainpoolp512r1_decompress_public_key`. -/
def decompressBrainpoolP512r1 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.brainpoolp512r1)

/-- `vg_ec_brainpoolp512r1_decompress_public_key_umaal`. -/
def decompressBrainpoolP512r1U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.brainpoolp512r1With true))

end VG.Impl.EcKey.Arm.Fn
