module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ClearOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.FinishTail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: complete output handling -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem finish_ok {p : CandidateP} {used status : Nat} {s₀ s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B)
    (hs : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 status) (hstatus : status < 2 ^ 64)
    (hsaved : ∀ i < 6, word s.mem p.B (8 * i) = s₀.gpr (saved.getD i .rax)) :
    WP isa finish s fun t => t.gpr .rax = BitVec.ofNat 64 status ∧
      word t.mem p.up 0 = BitVec.ofNat 64 (if status = 0 then 0 else used) ∧
      Spec.Rsa.bytesAt t.mem p.op p.k =
        (if status = 1 then Spec.Rsa.bytesAt s.mem p.op p.k else List.replicate p.k 0) ∧
      (∀ r ∈ saved, t.gpr r = s₀.gpr r) ∧ Keep (.rdi :: mmRegs) s t := by
  have hrd := h.base.scr.ld (show 8 * oStatus + 8 ≤ p.Z by
    change 160 ≤ p.Z; omega_using [h.base.header_room])
  have heq : (BitVec.ofNat 64 status == 1) = decide (status = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstatus]
    rfl
  unfold finish
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
    u.zf = some (decide (status = 1)) ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdrOff, hdi, hs, hrd, sub_beq_zero, heq]) rfl)
    fun u ⟨⟨hz, hm⟩, ku⟩ => ?_)
  obtain ⟨hu, hsu, hfu⟩ := h.same_mem hm ku (by decide)
  have hdu : u.gpr .rdi = p.B := (ku.gpr (by decide)).trans hdi
  have hsu' : word u.mem p.B (8 * oStatus) = BitVec.ofNat 64 status := by rw [hm]; exact hs
  have hsavedu := fun i hi => (show word u.mem p.B (8 * i) = word s.mem p.B (8 * i) by rw [hm]).trans (hsaved i hi)
  refine WP.seq (WP.ite (decide (status = 1)) (by simp [eval, hz]) ?_ ?_)
  · intro hy
    have hy' := of_decide_eq_true hy
    refine WP.block_nil ?_
    refine WP.mono (finishTail_ok hu hdu hsu' hstatus hsavedu)
      fun t ⟨hax, hused, hout, hregs, kt⟩ => ?_
    exact ⟨hax, hused, by simpa only [hy', ite_true, hm] using hout,
      hregs, (ku.trans kt).mono (by decide)⟩
  · intro hn
    have hn' := of_decide_eq_false hn
    refine WP.mono (clearOutput_ok hu hdu) fun v ⟨hv, hdv, hzv, hw, _, _, kv⟩ => ?_
    refine WP.mono (finishTail_ok hv hdv ((hw _ (by decide)).trans hsu') hstatus
      (fun i hi => (hw i (by omega)).trans (hsavedu i hi)))
      fun t ⟨hax, hused, hout, hregs, kt⟩ => ?_
    exact ⟨hax, hused, by simpa only [hn', ite_false] using hout.trans hzv,
      hregs, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
