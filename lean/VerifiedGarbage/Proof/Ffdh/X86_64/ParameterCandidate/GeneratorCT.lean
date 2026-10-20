module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestQCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: timing of the requested generator policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (sLink ws)
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

private theorem generator_header (d : CandidatePublic) (s : State) (h : PhaseLoaded false d s) :
    WP isa (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax oGen))]) s
      (fun t => InnerHeader (d.inner false) t ∧ t.gpr .rdx = (d.inner false).gen) := by
  obtain ⟨mi, hg, hp, _⟩ := h.2
  have hb := h.1.1.base
  have hgen := hb.hdr (oGen, BitVec.ofNat 64 d.p.gen) (by simp [CandidateP.headers])
  have hrd := hb.scr.ld (show 8 * oGen + 8 ≤ d.p.Z by change 88 ≤ d.p.Z; omega_using [hb.header_room])
  have hlinkrd := hg.scr.ld (show 8 * sLink + 8 ≤ d.p.Z - 256 by
    have hz := (hb.phase_dims false).z
    change 136 ≤ d.p.Z - 256; unfold slot hdrBytes at hz; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 d.p.gen ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hdrOff, hg.rdi, hp.link, hgen, hrd, hlinkrd]) rfl)
    fun t ⟨⟨hdx, hm⟩, k⟩ => ?_
  have hgt : Good t (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords false) mi :=
    ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact ⟨⟨h.1.2.2, good_hp hgt (k.2.2.trans h.1.2.1)⟩, hdx⟩

theorem generatorPolicy_ct : RelCT isa (Two (PhaseLoaded false)) generatorPolicy fun _ _ => True := by
  unfold generatorPolicy
  exact RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.link) generatorHead_ct)
    generator_header) (two_map (fun d : CandidatePublic => d.inner false) (fun _ _ h => h) inner_generator_ct)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
