module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Halve
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH parameter generation on x86-64: derive q in the output buffer -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem halveOutput_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P) :
    WP isa halveOutput s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.Q ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  let bs := Spec.Rsa.bytesAt s.mem p.op p.k
  have hlen : bs.length = p.k := bytesAt_length _ _ _
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hOut := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hLen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  unfold halveOutput
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbp, .rax, .rcx, .rdi] (Q := fun u =>
    u.gpr .rbp = p.B ∧ u.gpr .rdi = p.op ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hOut, hLen, hrd oOut (by decide), hrd oLen (by decide)]) rfl)
    fun u ⟨⟨hbp, hop, hcx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (halve_ok (bs := bs) (by omega_using [hlen, h.base.widths.1])
    (by omega_using [hlen, h.base.widths.2]) hop (by rw [hlen]; exact hcx)
    (fun i hi => by rw [k.2.2]; exact h.base.out.wr i (by omega_using [hlen, hi]))
    (fun i hi => by
      rw [hm]
      have hb := bytesAt_read s.mem p.op (by omega_using [hlen, hi] : i < p.k)
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hb))
    fun v ⟨_, hv, hf, kv⟩ => ?_)
  have hbpv : v.gpr .rbp = p.B := (kv.gpr (by decide)).trans hbp
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = p.B ∧ t.mem = v.mem)
    (by xrun [hbpv]) rfl) fun t ⟨⟨hdt, hmt⟩, kt⟩ => ?_
  have kk : Keep (.rdi :: mmRegs) s t := ((k.trans kv).trans kt).mono (by decide)
  have kk' := keep_modulus kk (hdt.trans hdi.symm)
  have hframe : ∀ a, (∀ i < p.k, a ≠ off p.op i) → t.mem a = s.mem a := by
    intro a ha
    rw [hmt, hf a (by simpa only [hlen] using ha), hm]
  obtain ⟨ht, hs, hfr⟩ := h.after_bytes hframe kk' (by decide)
  have hodd : p.P % 2 = 1 := (VG.Proof.Ffdh.ParameterCandidate.candidate_shape
    (by omega_using [h.base.bits1]) (Spec.Rsa.os2ip p.prefix)).1
  have hhalf : p.P / 2 = p.Q := by unfold CandidateP.Q; omega_using [hodd]
  refine ⟨ht, hdt, ?_, hs, hfr, kk'⟩
  rw [hmt]
  simpa only [hlen, bs, hp, hhalf] using hv

end VG.Proof.Ffdh.X86_64.ParameterCandidate
