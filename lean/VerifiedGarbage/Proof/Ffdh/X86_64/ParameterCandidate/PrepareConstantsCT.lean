module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE

/-! # FFDH parameter generation on x86-64: timing of Montgomery constants -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

private theorem multiply_header (M : Mont) (d : PreparePublic) (s : State) (h : R2Ready d s) :
    WP isa (M.mm aY aR2 aOne) s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk, hi, hn, hone, _, _, hN⟩ := h
  refine WP.mono (M.mm_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128])
    (o := aY) (a := aR2) (b := aOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hi (by rw [hone, hn]; exact hN))
    fun t ⟨ht, _, _, _, k⟩ => ?_
  exact ⟨mi, ht, hd, hz, k.2.2.trans hw, hk⟩

private theorem copy_header (d : PreparePublic) (s : State) (h : HeaderGood d s) :
    WP isa copyR1 s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk⟩ := h
  have hfit : slot d.w aR1 + 8 * (d.w + 2) ≤ d.IZ := by
    simp only [slot, aR1] at hz ⊢; omega
  refine WP.mono (copyToExt_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128])
    (a := aY) (d := aR1) (by decide) (by decide) hfit) fun t ⟨_, hf, k⟩ => ?_
  exact ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.outside hf (by unfold slot; omega)⟩, hd, hz, k.2.2.trans hw, hk⟩

theorem prepareConstants_ct (M : Mont) :
    RelCT isa (Two R2Ready) (prepareConstants M.mm) fun _ _ => True := by
  unfold prepareConstants
  refine RelCT.seq (two_post
    (two_map (fun d : PreparePublic => (⟨d.I, d.IZ, d.w⟩ : Ws)) (fun _ _ h => by
      obtain ⟨mi, hg, hd, _, _, _, _⟩ := h; exact ⟨mi, hg, hd.z⟩)
      (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide))) (multiply_header M)) ?_
  exact RelCT.seq (two_post
    (two_map PreparePublic.inner (fun _ _ h => h.header) inner_copyR1_ct) copy_header)
    (two_map PreparePublic.inner (fun _ _ h => h.header) inner_negateR1_ct)

theorem prepareConstants_header (M : Mont) (d : PreparePublic) (s : State) (h : R2Ready d s) :
    WP isa (prepareConstants M.mm) s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk, hi, hn, hone, hr2, ho, hN⟩ := h
  have hfit : slot d.w aRm1 + 8 * (d.w + 2) ≤ d.IZ := by simp only [slot, aRm1] at hz ⊢; omega
  refine WP.mono (prepareConstants_ok M hg hd.z hfit (by omega_using [hd.w4])
    (by omega_using [hd.w128]) hn hi hone ho hN hr2) fun t ⟨ht, _, _, _, k⟩ => ?_
  exact ⟨mi, ht, hd, hz, k.2.2.trans hw, hk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
