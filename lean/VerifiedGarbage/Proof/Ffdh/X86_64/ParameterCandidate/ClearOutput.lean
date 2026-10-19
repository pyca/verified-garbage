module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ExternalWords

/-! # FFDH parameter generation on x86-64: clear an unsuccessful candidate -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64

theorem clearOutput_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut oOut oLen) s fun t =>
      CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = List.replicate p.k 0 ∧
      (∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j)) ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86_64.zeroOut_ok h.base.scr hdi h.base.header_room
    (by decide : oOut < 32) (by decide : oLen < 32)
    (h.base.hdr (oOut, p.op) (by simp [CandidateP.headers]))
    (h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers]))
    (by omega_using [h.base.widths.1]) (by omega_using [h.base.widths.2]) h.base.out)
    fun t ⟨hv, hf, k⟩ => ?_
  obtain ⟨ht, hs, hfr⟩ := h.after_bytes hf k (by decide)
  refine ⟨ht, (k.gpr (by decide)).trans hdi, ?_, ?_, hs, hfr, k.mono (by decide)⟩
  · refine List.eq_replicate_iff.mpr ⟨bytesAt_length _ _ _, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hv i (List.mem_range.mp hi)
  · intro j hj
    exact words_outside_bytes h.base.size64 hf h.base.out.sep _ (by omega_using [hj, h.base.header_room])

end VG.Proof.Ffdh.X86_64.ParameterCandidate
