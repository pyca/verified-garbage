module

public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# P-384 public keys on 32-bit ARM, as emitted

`vg_ec_p384_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP384Comb

/-- `vg_ec_p384_public_key_umaal`. -/
def publicKeyP384U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP384CombU

/-- `vg_ec_p384_compress_public_key`. -/
def compressP384 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.p384)

/-- `vg_ec_p384_compress_public_key_umaal`. -/
def compressP384U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.p384With true))

/-- `vg_ec_p384_decompress_public_key`. -/
def decompressP384 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.p384)

/-- `vg_ec_p384_decompress_public_key_umaal`. -/
def decompressP384U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.p384With true))

end VG.Impl.EcKey.Arm.Fn
