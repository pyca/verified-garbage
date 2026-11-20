module

public import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# P-256 public keys on 32-bit ARM, as emitted

`vg_ec_p256_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Residue.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ec_p256_public_key`. -/
def publicKeyP256 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP256Comb

/-- `vg_ec_p256_public_key_umaal`. -/
def publicKeyP256U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP256CombU

/-- `vg_ec_p256_compress_public_key`. -/
def compressP256 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.p256)

/-- `vg_ec_p256_compress_public_key_umaal`. -/
def compressP256U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.p256With true))

/-- `vg_ec_p256_decompress_public_key`. -/
def decompressP256 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.p256)

/-- `vg_ec_p256_decompress_public_key_umaal`. -/
def decompressP256U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.p256With true))

end VG.Impl.EcKey.Arm.Fn
