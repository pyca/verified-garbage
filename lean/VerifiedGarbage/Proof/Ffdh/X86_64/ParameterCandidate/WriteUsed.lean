module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Bignum.ExternalWords

/-! # FFDH parameter generation on x86-64: write the public consumed count -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem writeWord_frame (m : Mem) (p : Addr) (v : BitVec 64) :
    ∀ a, (∀ i < 8, a ≠ off p i) → (m.writeW p v) a = m a := by
  intro a ha
  have hfar : 8 ≤ ofs p a := by
    by_contra hn
    have he : off p (ofs p a) = a := by
      simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm]
      exact BitVec.sub_add_cancel _ _
    exact ha _ (by omega) he.symm
  have hf := writeW_outside m p (d := 0) v (by decide)
  simpa only [off, BitVec.add_zero] using hf a (Or.inr hfar)

theorem writeUsed_ok {p : CandidateP} {used status : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hs : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 status) (hstatus : status < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr oStatus)), .mov .rdx (.mem (hdr oUsedP)),
      .mov .rcx (.mem (hdr oUsed)), .alu .test .rax (.reg .rax), .cmov .e .rcx (.reg .rax), .store (at0 .rdx) .rcx]) s
      fun t => t.gpr .rax = BitVec.ofNat 64 status ∧ t.gpr .rdi = p.B ∧
        word t.mem p.up 0 = BitVec.ofNat 64 (if status = 0 then 0 else used) ∧
        Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k ∧
        (∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j)) ∧
        Keep [.rax, .rdx, .rcx] s t := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hup := h.base.hdr (oUsedP, p.up) (by simp [CandidateP.headers])
  have hst : InRegions s.wr p.up 8 := by simpa [off] using h.base.used.st (d := 0) (by decide)
  have hzero : (BitVec.ofNat 64 status == 0) = decide (status = 0) := ofNat64_beq_zero hstatus
  have hv : (if decide (status = 0) then BitVec.ofNat 64 status else BitVec.ofNat 64 used) =
      BitVec.ofNat 64 (if status = 0 then 0 else used) := by
    by_cases hz : status = 0 <;> simp [hz]
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 status ∧
    t.mem = s.mem.writeW p.up (BitVec.ofNat 64 (if status = 0 then 0 else used)))
    (by xrun [State.ea, hdr, at0, hdrOff, hdi, hs, hup, h.usedWord,
      hrd oStatus (by decide), hrd oUsedP (by decide), hrd oUsed (by decide), hst,
      BitVec.ofInt_ofNat, BitVec.add_zero, BitVec.and_self, hzero, cmov_reg_value, eval, hv]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ?_
  have hf : ∀ a, (∀ i < 8, a ≠ off p.up i) → t.mem a = s.mem a := by
    rw [hm]; exact writeWord_frame _ _ _
  refine ⟨hax, (k.gpr (by decide)).trans hdi, ?_, ?_, ?_, k⟩
  · rw [hm]; simpa [off] using word_writeW_self s.mem p.up 0 (BitVec.ofNat 64 (if status = 0 then 0 else used))
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf _ (fun j hj he => h.base.outUsed i (List.mem_range.mp hi) j hj he)
  · intro j hj
    exact words_outside_bytes h.base.size64 hf h.base.usedOut.sep _ (by omega_using [hj, h.base.header_room])

end VG.Proof.Ffdh.X86_64.ParameterCandidate
