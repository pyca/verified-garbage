module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: consume the candidate's initial prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem consumeCandidate_ok {p : CandidateP} {s : State}
    (h : CandidateTape p 0 s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa (.block consumeCandidate) s fun t => CandidateTape p p.k t ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hwr : ∀ j < 32, InRegions s.wr (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.st (by omega_using [hj, h.base.header_room])
  have hlen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hptr : word s.mem p.B (8 * oRandPtr) = p.rp := by simpa [off] using h.ptr
  have hleft : word s.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 p.rand.length := by simpa using h.left
  have hsub : BitVec.ofNat 64 p.rand.length - BitVec.ofNat 64 p.k = BitVec.ofNat 64 (p.rand.length - p.k) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [h.base.widths.2]) havail
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = advanceMem s.mem p.B p.rp p.k p.rand.length 0)
    (by
      xrun [consumeCandidate, advanceMem, State.ea, hdr, hdi, hdrOff, hlen, hptr, hleft,
        hrd oLen (by decide), hrd oRandPtr (by decide), hrd oRandLeft (by decide),
        hwr oRandPtr (by decide), hwr oRandLeft (by decide), hwr oUsed (by decide),
        hdrStore_hdr _ _ _ (i := oRandPtr) (k := oRandLeft) (by decide) (by decide) (by decide), hsub]
      simp only [Nat.zero_add, off]) rfl) fun t ⟨hm, k⟩ => ?_
  have hf : Frm p.B [(8 * oRandPtr, 24)] s.mem t.mem := by rw [hm]; exact advanceMem_frame _ _ _ _ _ _
  have hscr : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    change 120 ≤ p.Z
    omega_using [h.base.header_room])
  have hs : CandidateSaved p s.mem t.mem := by
    intro j hj
    exact hf.word_eq (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      left
      change 8 * j + 8 ≤ 96
      omega) (by omega)
  have hbase := h.base.keep (CandidateFrame.of_scr hscr) hs k ((k.gpr (by decide)).trans h.base.sp)
  refine ⟨⟨hbase, havail, ?_, ?_, ?_⟩, hs, CandidateFrame.of_scr hscr, k.mono (by decide), h.base.output_eq hscr⟩
  · rw [hm]; exact advanceMem_ptr _ _ _ _ _ _
  · rw [hm]; exact advanceMem_left _ _ _ _ _ _
  · rw [hm]; simpa only [Nat.zero_add] using advanceMem_used s.mem p.B p.rp p.k p.rand.length 0

end VG.Proof.Ffdh.X86_64.ParameterCandidate
