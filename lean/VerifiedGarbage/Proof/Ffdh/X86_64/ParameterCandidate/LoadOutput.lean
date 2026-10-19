module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH parameter generation on x86-64: load either modulus from the output -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem loadOutput_ok {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q s)
    (hv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.phaseValue q) :
    WP isa loadOutput s fun t => CandidateTape p used t ∧
      Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧ PhaseHeader p q t ∧
      wv t.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  let bs := Spec.Rsa.bytesAt s.mem p.op p.k
  have hlen : bs.length = p.k := bytesAt_length _ _ _
  have hout := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hk := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hlinkrd := hg.scr.ld (show 8 * VG.Impl.Rsa.X86_64.Crt.sLink + 8 ≤ p.Z - 256 by
    have hz := (h.base.phase_dims q).z
    change 136 ≤ p.Z - 256
    unfold slot hdrBytes at hz
    omega)
  unfold loadOutput
  refine WP.seq (WP.mono (WP.keep [.rax, .rsi, .rcx] (Q := fun u =>
    u.gpr .rsi = p.op ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hg.rdi, hdrOff, hp.link, hout, hk, hlinkrd,
      hrd oOut (by decide), hrd oLen (by decide)]) rfl)
    fun u ⟨⟨hsi, hcx, hm⟩, ku⟩ => ?_)
  have hgu : Good u (off p.B 256) (p.Z - 256) (p.phaseWords q) mi :=
    ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  have hfit : slot (p.phaseWords q) aN + 8 * ((p.k + 7) / 8) ≤ p.Z - 256 := by
    have hs := slot_le (w := p.phaseWords q) (show aN < 8 by decide)
    have hz := (h.base.phase_dims q).z
    have hw := (h.base.phase_load_widths q).2.1
    unfold slot aN at *
    omega
  refine WP.mono (loadCandidate_ok (bs := bs) hgu (h.base.phase_dims q).z hsi
    (by rw [hlen]; exact hcx)
    (by omega_using [hlen, h.base.widths.1]) (by omega_using [hlen, h.base.widths.2])
    (by rw [hlen]; exact (h.base.phase_load_widths q).1)
    (by rw [hlen]; exact (h.base.phase_load_widths q).2.1)
    (by rw [show Spec.Rsa.os2ip bs = p.phaseValue q from hv]; exact (h.base.phase_wordshape q).2)
    (fun i hi => by
      rw [ku.2.1, ku.2.2]
      obtain ⟨r, hr, hc⟩ := h.base.out.wr i (by omega_using [hlen, hi])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun i hi => by rw [hm]; exact bytesAt_read _ _ (by omega_using [hlen, hi] : i < p.k))
    (fun i hi => Or.inr (by
      have ho := h.base.out.sep i (by omega_using [hlen, hi])
      change p.Z ≤ ofs p.B (off p.op i) at ho
      rw [hlen]
      rcases ofs_rebase p.B (off p.op i) (o := 256) (by decide) with ⟨_, he⟩ | ⟨_, he⟩
      · have hx : ofs p.B (off p.op i) - 256 = ofs (off p.B 256) (off p.op i) := he.symm
        omega_using [hx, ho, hfit]
      · omega_using [he, hfit, h.base.size64]))) fun t ⟨htv, hgt, hf, kt⟩ => ?_
  have hf' : Frm (off p.B 256) [(slot (p.phaseWords q) aN, 8 * ((p.k + 7) / 8))] s.mem t.mem := by
    rw [← hm]
    exact Frm.of_outside (by simpa only [hlen] using hf) (by simp)
  have hrs : ∀ r ∈ [(slot (p.phaseWords q) aN, 8 * ((p.k + 7) / 8))], r.1 + r.2 ≤ p.Z - 256 := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hfit
  have kk : Keep mmRegs s t := (ku.trans kt).mono (by decide)
  refine ⟨h.keep_inner hf' hrs kk (by decide), hgt,
    hp.of_inner h.base hf' hrs ?_, htv.trans hv,
    fun j hj => h.base.inner_header hf' hrs j (by omega),
    CandidateFrame.of_scr (h.base.inner_changes hf' hrs), kk,
    h.base.output_eq (h.base.inner_changes hf' hrs)⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  left
  change 136 ≤ slot (p.phaseWords q) aN
  unfold slot hdrBytes aN
  omega

end VG.Proof.Ffdh.X86_64.ParameterCandidate
