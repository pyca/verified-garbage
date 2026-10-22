module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Main
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Proof.Framework.X86.CallWith

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86

theorem compress_verified {c : Cfg} (hc : CfgOk c) (I : Spec.EcKey.Instance) (hC : c.C = I.curve)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.compress c) 28)
    (hct : ConstantTime isa (compressContract c.C).pre (compressContract c.C).pub
      (Impl.EcKey.Compressed.X86.compress c))
    (hsig : ∃ s, (I.compressPublicKeyContract abi 28).pre s) :
    Verified target (Impl.EcKey.Compressed.X86.compress c) (I.compressPublicKeyContract abi 28) := by
  have himp := compress_implies I hsig
  have hsat := himp.sat_left
  have localSat : ∃ s, (compressContract c.C).pre s := by
    obtain ⟨s, hs⟩ := hsat
    refine ⟨s.withRegions (codecRd (2 * I.curve.len + 1) s) (codecWr (I.curve.len + 1) s), ?_⟩
    rw [hC]
    exact codecWide_pre hs
  have localVerified : Verified target (Impl.EcKey.Compressed.X86.compress c) (compressContract I.curve) := by
    rw [← hC]
    exact Verified.of_correct (compress_correct c hc hsp) hct (.refl localSat)
  apply Verified.of_implies (Verified.narrowTo localVerified
    (codecRd (2 * I.curve.len + 1)) (codecWr (I.curve.len + 1))
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
    simpa only [compressContract, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [compressContract, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.EcKey.Compressed.X86
