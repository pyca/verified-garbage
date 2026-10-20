module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: enter either modulus phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem phaseSetup_state_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (q : Bool) :
    WP isa (phaseSetup q) s fun t => ∃ mi,
      CandidateTape p used t ∧ Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧
      PhaseHeader p q t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧
      Keep (.rdi :: mmRegs) s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  have hws : wsWords (p.phaseLen q) = p.phaseWords q := by
    unfold wsWords
    change max 2 (p.phaseWords q) = p.phaseWords q
    exact Nat.max_eq_right (by omega_using [(h.base.phase_room q).1])
  have hbits := h.base.hdr (oBits, BitVec.ofNat 64 p.bits) (by simp [CandidateP.headers])
  refine WP.mono (phaseSetup_ok h.base.scr hdi (by omega_using [h.base.bits1])
    (by omega_using [h.base.bits2]) hbits q (by
      change 256 + slot (wsWords (p.phaseLen q)) 8 ≤ p.Z
      rw [hws]
      omega_using [(h.base.phase_dims q).z, h.base.header_room]))
    fun t ⟨mi, hg, hl, _, hb, hn, hc, hf, k⟩ => ?_
  change Good t (off p.B 256) (p.Z - 256) (wsWords (p.phaseLen q)) mi at hg
  rw [hws] at hg
  have hfit : ∀ r ∈ phaseRanges, r.1 + r.2 ≤ p.Z := by
    intro r hr
    simp only [phaseRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · change 144 ≤ p.Z; omega_using [h.base.header_room]
    · change 168 ≤ p.Z; omega_using [h.base.header_room]
    · change 392 ≤ p.Z; omega_using [h.base.room, h.base.widths.1]
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := by
    intro j hj
    apply hf.word_eq
    · intro r hr
      simp only [phaseRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · left; change 8 * j + 8 ≤ 120; omega
      · left; change 8 * j + 8 ≤ 160; omega
      · left; omega
    · omega
  have hframe : CandidateFrame p s.mem t.mem := CandidateFrame.of_scr (InScr.of_frm hf hfit)
  exact ⟨mi, h.keep hframe hh k ((k.gpr (by decide)).trans h.base.sp), hg,
    ⟨hb, hn, hc, hl⟩, fun j hj => hh j (by omega), hframe, k,
    h.base.output_eq (InScr.of_frm hf hfit)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
