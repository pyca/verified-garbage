module

public import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# P-224 public keys on 32-bit ARM, as emitted

`vg_ec_p224_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ec_p224_public_key`. -/
def publicKeyP224 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP224Comb

/-- `vg_ec_p224_public_key_umaal`. -/
def publicKeyP224U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP224CombU

/-- `vg_ec_p224_compress_public_key`. -/
def compressP224 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.p224)

/-- `vg_ec_p224_compress_public_key_umaal`. -/
def compressP224U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.p224With true))

/-- `vg_ec_p224_decompress_public_key`. -/
def decompressP224 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.p224)

/-- `vg_ec_p224_decompress_public_key_umaal`. -/
def decompressP224U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.p224With true))

end VG.Impl.EcKey.Arm.Fn
