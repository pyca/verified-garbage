module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
meta import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP384r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1

/-!
# SEC 1 point conversion over brainpoolP384r1 on PPC64LE: `Verified`

`compress_verified` and `decompress_verified`: from `compress_correct` and
`decompress_correct` (with the candidate `rhs^((p+1)/4)`, as `p ≡ 3 mod 4`), for brainpoolP384r1's configuration, and
the times depending only on `out`, `public` and `scratch` (`taint_decide` on
the code's literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE

theorem compress_ct : ConstantTime isa (compressContract Spec.BrainpoolP384r1.curve).pre
    (compressContract Spec.BrainpoolP384r1.curve).pub Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP384r1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem compress_sat : ∃ s, (Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.BrainpoolP384r1.curve.len = 48 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP384r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 48)

theorem compress_verified :
    Verified target Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP384r1 (Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct brainpoolp384r1 brainpoolp384r1_ok) compress_ct (compress_implies _ compress_sat)

theorem decompress_ct : ConstantTime isa
    (decompressContract Spec.BrainpoolP384r1.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.BrainpoolP384r1.curve Impl.EcKey.Compressed.rootThreeModFour).pub
    Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP384r1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem decompress_sat : ∃ s, (Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.BrainpoolP384r1.curve.len = 48 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP384r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 48)

theorem decompress_verified (hL : Proof.Weierstrass.Law Spec.BrainpoolP384r1.curve) :
    Verified target Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP384r1
      (Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct brainpoolp384r1 brainpoolp384r1_ok _ (candidateThree_correct brainpoolp384r1_ok (by decide +kernel)))
    decompress_ct (decompress_implies _ _ (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel))
      decompress_sat)

end VG.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1
