module

import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
meta import VerifiedGarbage.Impl.EcKey.Compressed.P256.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Contract
public import VerifiedGarbage.Spec.P256

/-!
# SEC 1 point conversion over P-256 on PPC64LE: `Verified`

`compress_verified` and `decompress_verified`: from `compress_correct` and
`decompress_correct` (with the candidate `rhs^((p+1)/4)`, as `p ≡ 3 mod 4`), for P-256's configuration, and
the times depending only on `out`, `public` and `scratch` (`taint_decide` on
the code's literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE.P256

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE

theorem compress_ct : ConstantTime isa (compressContract Spec.P256.curve).pre
    (compressContract Spec.P256.curve).pub Impl.EcKey.Compressed.PPC64LE.compressP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem compress_sat : ∃ s, (Spec.EcKey.P256.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P256.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 32)

theorem compress_verified :
    Verified target Impl.EcKey.Compressed.PPC64LE.compressP256 (Spec.EcKey.P256.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p256 p256_ok) compress_ct (compress_implies _ compress_sat)

theorem decompress_ct : ConstantTime isa
    (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pub
    Impl.EcKey.Compressed.PPC64LE.decompressP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem decompress_sat : ∃ s, (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P256.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 32)

theorem decompress_verified (hL : Proof.Weierstrass.Law Spec.P256.curve) :
    Verified target Impl.EcKey.Compressed.PPC64LE.decompressP256
      (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p256 p256_ok _ (candidateThree_correct p256_ok (by decide +kernel)))
    decompress_ct (decompress_implies _ _ (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel))
      decompress_sat)

end VG.Proof.EcKey.Compressed.PPC64LE.P256
