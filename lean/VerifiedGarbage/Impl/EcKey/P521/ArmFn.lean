module

public import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# P-521 public keys on 32-bit ARM, as emitted

`vg_ec_p521_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ec_p521_public_key`. -/
def publicKeyP521 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP521Comb

/-- `vg_ec_p521_public_key_umaal`. -/
def publicKeyP521U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP521CombU

/-- `vg_ec_p521_compress_public_key`. -/
def compressP521 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.p521)

/-- `vg_ec_p521_compress_public_key_umaal`. -/
def compressP521U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.p521With true))

/-- `vg_ec_p521_decompress_public_key`. -/
def decompressP521 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.p521)

/-- `vg_ec_p521_decompress_public_key_umaal`. -/
def decompressP521U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.p521With true))

end VG.Impl.EcKey.Arm.Fn
