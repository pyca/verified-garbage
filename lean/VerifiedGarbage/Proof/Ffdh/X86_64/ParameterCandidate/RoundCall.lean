module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: reusable shared primality round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64

theorem witnessRoundRanges_bounds (p : WitnessParams) :
    ∀ r ∈ witnessRoundRanges p.w, 136 ≤ r.1 ∧ r.1 + r.2 ≤ p.IZ := by
  have hz : 256 + 28 * (8 * (p.w + 2)) ≤ p.IZ := by
    have hr : 256 + (256 + 28 * (8 * (p.w + 2))) ≤ p.Z := p.room
    unfold WitnessParams.IZ
    omega_using [hr]
  simp only [witnessRoundRanges, Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    Caller.pad, slot, VG.Impl.Bignum.hdrBytes, aAcc, aTmp, aXm, VG.Impl.RsaKeyGen.X86_64.Candidate.aR1,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_using [hz]

theorem witnessRound_state_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used a : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hx : wv s.mem p.I (slot p.w aXm) p.w = a) :
    WP isa (witnessRound M.mm K.run) s fun t => DrawState p rp used bs t ∧
      word t.mem p.I (8 * VG.Impl.RsaKeyGen.X86_64.Candidate.kFlag) = mask (Spec.Ffdh.mrRound p.N a) ∧
      (∀ j < 32, word t.mem p.O (8 * j) = word s.mem p.O (8 * j)) ∧
      RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  have hrs := witnessRoundRanges_bounds p
  have hfit : ∀ r ∈ witnessRoundRanges p.w, r.1 + r.2 ≤ p.IZ := fun r hr => (hrs r hr).2
  refine WP.mono (witnessRound_ok M K h.ready p.dims (by omega_using [p.room, p.space_bounds.2.2]) hroom.call p.odd p.n3 hx)
    fun t ⟨hrt, hflag, hf, k⟩ => ?_
  have hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O := by
    rw [hf.word_eq (d := 8 * VG.Impl.Rsa.X86_64.Crt.sLink) (fun r hr => Or.inl (hrs r hr).1) p.space_bounds.2.1 h.ready.good.scr.nowrap (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact hroom.call.disjoint)]
    exact h.link
  have hh := round_outer_header hroom hf hfit hz64
  have hframe := RoundFrame.of_inner hf hfit hz64
  exact ⟨h.after_round hroom hrt hl hh hframe k, hflag, hh, hframe, k⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
