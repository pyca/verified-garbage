module

public import VerifiedGarbage.Impl.EcKey.P256.AArch64
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.EcKey.P192.AArch64
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192Decompress
public meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256Decompress
public meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256Decompress
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueBound
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueBound
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Decompressing a public key on AArch64 returns without secret residue

`cleared c` is the decompression `c`, then what it leaves secret cleared: the
registers that held the field elements, and the flags, from `x2`. Its result
is `and x0, x3, x1` after `movz x1, #1`, a bit of a mask the analysis
cannot show is public: it fits in one bit, which is less than the 32 bits of
the result (`RTaintB.noResidue_of_verified`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.Residue

open VG VG.AArch64

/-- The decompression `c`, then the clears of `rs` and `vs`, what it
leaves, and of the flags. -/
abbrev cleared (rs : List Reg) (vs : List VReg) (c : Prog isa) : Prog isa :=
  Impl.Scrub.AArch64.withClears (.x2 :: .x3 :: .x4 :: .x8 :: .x9 :: .x10 :: .x11 :: .x12 :: .x13 :: rs) vs
    (some .x2) c

namespace P192

theorem verified (hL : Proof.Weierstrass.Law Spec.P192.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target (cleared [.x16, .x17] [] P192Decompress.code)
      (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) :=
  Clears.Verified.withClears (P192Decompress.verified hL hI) (by decide)

theorem noResidue (hL : Proof.Weierstrass.Law Spec.P192.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    NoResidue (cleared [.x16, .x17] [] P192Decompress.code)
      (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) 32 :=
  RTaintB.noResidue_of_verified (verified hL hI) ⟨_, by taint_decide_ct⟩

/-- `vg_ec_p192_decompress_public_key` as it is emitted (`Impl.EcKey.AArch64.Fn.decompressP192`). -/
theorem scrubbed (hL : Proof.Weierstrass.Law Spec.P192.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed target Impl.EcKey.AArch64.Fn.decompressP192
      (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) 32 :=
  ⟨verified hL hI, noResidue hL hI⟩

end P192


namespace P256

theorem verified (hL : Proof.Weierstrass.Law Spec.P256.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target (cleared [.x14, .x15, .x16, .x17] [] P256Decompress.code)
      (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) :=
  Clears.Verified.withClears (P256Decompress.verified hL hI) (by decide)

theorem noResidue (hL : Proof.Weierstrass.Law Spec.P256.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    NoResidue (cleared [.x14, .x15, .x16, .x17] [] P256Decompress.code)
      (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) 32 :=
  RTaintB.noResidue_of_verified (verified hL hI) ⟨_, by taint_decide_ct⟩

/-- `vg_ec_p256_decompress_public_key` as it is emitted (`Impl.EcKey.AArch64.Fn.decompressP256`). -/
theorem scrubbed (hL : Proof.Weierstrass.Law Spec.P256.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed target Impl.EcKey.AArch64.Fn.decompressP256
      (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) 32 :=
  ⟨verified hL hI, noResidue hL hI⟩

end P256



end VG.Proof.EcKey.Compressed.AArch64.Residue
