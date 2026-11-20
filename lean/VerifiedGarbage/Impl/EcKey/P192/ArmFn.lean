module

public import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# P-192 public keys on 32-bit ARM, as emitted

`vg_ec_p192_public_key`, `_compress_public_key` and `_decompress_public_key`,
with and without `umaal`: each one's code, which has no frames, then the
instructions that set the registers a callee may change, but the result, and
the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.EcKey.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ec_p192_public_key`. -/
def publicKeyP192 : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP192Comb

/-- `vg_ec_p192_public_key_umaal`. -/
def publicKeyP192U : Prog isa := scrub 32 Impl.Ecdsa.Arm.publicKeyP192CombU

/-- `vg_ec_p192_compress_public_key`. -/
def compressP192 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.compress Impl.Ecdsa.Arm.p192)

/-- `vg_ec_p192_compress_public_key_umaal`. -/
def compressP192U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.compress (Impl.Ecdsa.Arm.p192With true))

/-- `vg_ec_p192_decompress_public_key`. -/
def decompressP192 : Prog isa := scrub 32 (Impl.EcKey.Compressed.Arm.decompress Impl.Ecdsa.Arm.p192)

/-- `vg_ec_p192_decompress_public_key_umaal`. -/
def decompressP192U : Prog isa :=
  scrub 32 (Impl.EcKey.Compressed.Arm.decompress (Impl.Ecdsa.Arm.p192With true))

end VG.Impl.EcKey.Arm.Fn
