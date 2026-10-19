module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Bignum.ExternalWords

/-! # FFDH parameter generation on x86-64: reconstruct p from the original prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem shapeOriginal_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa shapeOriginal s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j)) := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hOut := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hRand := h.base.hdr (oRandStart, p.rp) (by simp [CandidateP.headers])
  have hLen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hBits := h.base.hdr (oBits, BitVec.ofNat 64 p.bits) (by simp [CandidateP.headers])
  have hprefix : p.prefix.length = p.k := by simp only [CandidateP.prefix, List.length_take, Nat.min_eq_left havail]
  unfold shapeOriginal
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbp, .rax, .rsi, .rcx, .rdx, .rdi] (Q := fun u =>
    u.gpr .rbp = p.B ∧ u.gpr .rdi = p.op ∧ u.gpr .rsi = p.rp ∧
    u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.gpr .rdx = BitVec.ofNat 64 p.bits ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hOut, hRand, hLen, hBits,
      hrd oOut (by decide), hrd oRandStart (by decide), hrd oLen (by decide), hrd oBits (by decide)]) rfl)
    fun u ⟨⟨hbp, hop, hrp, hcx, hdx, hm⟩, k⟩ => ?_)
  have hsrc : Src u p.B p.Z p.rp p.prefix := source_take
    (h.base.rand.congrK (by rw [hm]; exact InScr.refl _ _ _) k) p.k
  refine WP.seq (WP.mono (shape_ok (Nat.le_trans (by decide) h.base.bits1) h.base.bits2 (hprefix.trans h.base.len) hrp hop
    (by rw [hprefix]; exact hcx) hdx hsrc.rd
    (fun i hi => by rw [k.2.2]; exact h.base.out.wr i (by omega_using [hprefix, hi]))
    (fun i hi => by
      rw [hsrc.val i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])
    (fun i hi j hj he => h.base.outRand j (by omega_using [hprefix, hj]) i
      (by omega_using [hprefix, havail, hi]) he.symm))
    fun v ⟨_, hv, hf, kv⟩ => ?_)
  have hbpv : v.gpr .rbp = p.B := (kv.gpr (by decide)).trans hbp
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = p.B ∧ t.mem = v.mem)
    (by xrun [hbpv]) rfl) fun t ⟨⟨hdt, hmt⟩, kt⟩ => ?_
  have kk : Keep (.rdi :: mmRegs) s t := ((k.trans kv).trans kt).mono (by decide)
  have kk' := keep_modulus kk (hdt.trans hdi.symm)
  have hframe : ∀ a, (∀ i < p.k, a ≠ off p.op i) → t.mem a = s.mem a := by
    intro a ha
    rw [hmt, hf a (by simpa only [hprefix] using ha), hm]
  obtain ⟨ht, hs, hfr⟩ := h.after_bytes hframe kk' (by decide)
  refine ⟨ht, hdt, ?_, hs, hfr, kk', ?_⟩
  · rw [hmt]
    simpa only [hprefix, CandidateP.P] using hv
  · intro j hj
    exact words_outside_bytes h.base.size64 hframe h.base.out.sep _
      (by omega_using [hj, h.base.header_room])

end VG.Proof.Ffdh.X86_64.ParameterCandidate
