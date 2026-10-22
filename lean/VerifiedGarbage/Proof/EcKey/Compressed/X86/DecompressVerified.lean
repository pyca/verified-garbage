module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMain
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Proof.Framework.X86.CallWith

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86

theorem decompress_verified {c : Cfg} (hc : CfgOk c) (I : Spec.EcKey.Instance) (hC : c.C = I.curve)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (hroot : CandidateCorrect c root)
    (facts : RootFacts (hC ▸ root))
    (hsp : SpOk (Impl.EcKey.Compressed.X86.decompress c) 28)
    (hct : ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub
      (Impl.EcKey.Compressed.X86.decompress c))
    (hsig : ∃ s, (I.decompressPublicKeyContract abi 28).pre s) :
    Verified target (Impl.EcKey.Compressed.X86.decompress c) (I.decompressPublicKeyContract abi 28) := by
  have heq : decompressContract c.C root = decompressContract I.curve (hC ▸ root) := by
    rcases I with ⟨C, name, title⟩
    cases hC
    rfl
  have himp := decompress_implies I (hC ▸ root) facts hsig
  have hsat := himp.sat_left
  have localSat : ∃ s, (decompressContract c.C root).pre s := by
    obtain ⟨s, hs⟩ := hsat
    refine ⟨s.withRegions (codecRd (I.curve.len + 1) s) (codecWr (2 * I.curve.len + 1) s), ?_⟩
    rw [heq]
    exact codecWide_pre hs
  have localVerified : Verified target (Impl.EcKey.Compressed.X86.decompress c) (decompressContract I.curve (hC ▸ root)) := by
    rw [← heq]
    exact Verified.of_correct (decompress_correct c hc root hroot hsp) hct (.refl localSat)
  apply Verified.of_implies (Verified.narrowTo localVerified
    (codecRd (I.curve.len + 1)) (codecWr (2 * I.curve.len + 1))
    (fun _ h => codecWide_pre h) ?_ ?_ ?_ ?_ hsat) himp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecRd, codecWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · intro s h a n ⟨r, hr, hcontains⟩
    rw [h.2.1]
    refine ⟨r, ?_, hcontains⟩
    simp only [codecWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [decompressContract, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [decompressContract, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.EcKey.Compressed.X86
