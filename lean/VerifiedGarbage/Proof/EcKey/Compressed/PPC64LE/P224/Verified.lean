module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Tonelli
import VerifiedGarbage.Proof.P224.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
meta import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224

/-!
# SEC 1 point conversion over P-224 on PPC64LE: `Verified`

`compress_verified` and `decompress_verified`: from `compress_correct` and
`decompress_correct` (with Tonelli and Shanks's root, as `p ≡ 1 mod 4`), for P-224's configuration, and
the times depending only on `out`, `public` and `scratch` (`taint_decide` on
the code's literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE.P224

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE

theorem compress_ct : ConstantTime isa (compressContract Spec.P224.curve).pre
    (compressContract Spec.P224.curve).pub Impl.EcKey.Compressed.PPC64LE.compressP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem compress_sat : ∃ s, (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 28)

theorem compress_verified :
    Verified target Impl.EcKey.Compressed.PPC64LE.compressP224 (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p224 p224_ok) compress_ct (compress_implies _ compress_sat)

/-- P-224's square root: Tonelli and Shanks's, for `p - 1 = q 2⁹⁶` and the
nonresidue 11. -/
abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) : Spec.Weierstrass.Fe Spec.P224.curve :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

theorem decompress_ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub Impl.EcKey.Compressed.PPC64LE.decompressP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem decompress_sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 28)

theorem decompress_verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target Impl.EcKey.Compressed.PPC64LE.decompressP224
      (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p224 p224_ok root
      (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel)))
    decompress_ct (decompress_implies _ _ (Proof.P224.rootFacts hL) decompress_sat)

end VG.Proof.EcKey.Compressed.PPC64LE.P224
