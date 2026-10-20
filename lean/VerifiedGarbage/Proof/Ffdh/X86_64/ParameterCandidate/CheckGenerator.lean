module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: generator policy at the p phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem generatorCheck_state_ok {p : CandidateP} {used : Nat} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords false) mi)
    (hp : PhaseHeader p false s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords false) aN) (p.phaseWords false) = p.P) :
    WP isa (.seq (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax oGen))]) generatorCheck) s
      fun t => CandidateTape p used t ∧
        Good t (off p.B 256) (p.Z - 256) (p.phaseWords false) mi ∧ PhaseHeader p false t ∧
        wv t.mem (off p.B 256) (slot (p.phaseWords false) aN) (p.phaseWords false) = p.P ∧
        t.zf = some (Spec.Ffdh.generationShape p.bits p.gen p.P) ∧
        t.mem = s.mem ∧ Keep mmRegs s t := by
  have hgen := h.base.hdr (oGen, BitVec.ofNat 64 p.gen) (by simp [CandidateP.headers])
  have hrd := h.base.scr.ld (show 8 * oGen + 8 ≤ p.Z by
    change 88 ≤ p.Z
    omega_using [h.base.header_room])
  have hlinkrd := hg.scr.ld (show 8 * sLink + 8 ≤ p.Z - 256 by
    have hz := (h.base.phase_dims false).z
    change 136 ≤ p.Z - 256
    unfold slot hdrBytes at hz
    omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx] (Q := fun u =>
    u.gpr .rdx = BitVec.ofNat 64 p.gen ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hg.rdi, hdrOff, hp.link, hgen, hrd, hlinkrd]) rfl)
    fun u ⟨⟨hdx, hm⟩, ku⟩ => ?_)
  have hgu : Good u (off p.B 256) (p.Z - 256) (p.phaseWords false) mi :=
    ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  have hbit : Spec.RsaKeyGen.bitLength p.P = p.bits :=
    VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_using [h.base.bits1]) _ |>.1
  refine WP.mono (generatorCheck_ok hgu (h.base.phase_dims false).z
    (by omega_using [(h.base.phase_room false).1]) (by omega_using [(h.base.phase_room false).2.1])
    h.base.bits1 h.base.bits2 (by rw [hm, hn]; exact hbit) h.base.gen hdx)
    fun t ⟨hz, hmt, kt⟩ => ?_
  have hmem : t.mem = s.mem := hmt.trans hm
  have kk : Keep mmRegs s t := (ku.trans kt).mono (by decide)
  have hf : CandidateFrame p s.mem t.mem := by rw [hmem]; exact CandidateFrame.refl _ _
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := fun _ _ => by rw [hmem]
  refine ⟨h.keep hf hh kk ((kk.gpr (by decide)).trans h.base.sp),
    ⟨hg.scr.congr kk.2.2, (kk.gpr (by decide)).trans hg.rdi, by rw [hmem]; exact hg.hdr⟩,
    ⟨by rw [hmem]; exact hp.bits, by rw [hmem]; exact hp.len,
      by rw [hmem]; exact hp.checks, by rw [hmem]; exact hp.link⟩, by simpa only [hmem] using hn,
    by simpa only [hm, hn] using hz, hmem, kk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
