module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# secp256k1 public keys on 32-bit ARM, as emitted

`vg_ec_secp256k1_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Residue.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ec_secp256k1_public_key`. -/
def publicKeySecp256k1 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeySecp256k1Comb

/-- `vg_ec_secp256k1_public_key_umaal`. -/
def publicKeySecp256k1U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeySecp256k1CombU

/-- `vg_ec_secp256k1_compress_public_key`. -/
def compressSecp256k1 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.secp256k1)

/-- `vg_ec_secp256k1_compress_public_key_umaal`. -/
def compressSecp256k1U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.secp256k1With true))

/-- `vg_ec_secp256k1_decompress_public_key`. -/
def decompressSecp256k1 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.secp256k1)

/-- `vg_ec_secp256k1_decompress_public_key_umaal`. -/
def decompressSecp256k1U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.secp256k1With true))

end VG.Impl.EcKey.Arm.Fn
