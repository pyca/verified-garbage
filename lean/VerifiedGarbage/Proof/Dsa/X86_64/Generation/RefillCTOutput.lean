module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTFinish
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of the refillable-tape search's output and status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

/-- The frame's status word, after the output. -/
def StatusAt (D : DonePublic) (t : State) : Prop :=
  ∃ V W, Lay t D.ctx.geo.F D.ctx.geo.hash ∧ Rep t.mem D.ctx.geo.F D.ctx.geo.hash V W ∧ W 19 = D.status

theorem DonePublic.outputPlan (D : DonePublic) : OutputPlan (D.ctx.withHs D.hs) :=
  ⟨D.ends.out.lengthSlot, D.ends.out.bound, D.ends.out.separate⟩

theorem finishOutput_status {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s) :
    WP isa Impl.Dsa.X86_64.Generation.finishOutput s (StatusAt D) := by
  obtain ⟨⟨W, hm, h19, _⟩, _, _, _, hwr, _⟩ := h
  have o := D.outputPlan
  have pn : 0 < D.ctx.geo.pLen ∧ D.ctx.geo.pLen ≤ 384 := by rcases D.ctx.geo.width with hh | hh | hh <;> omega
  have qn : D.ctx.geo.qLen ≤ 32 := by rcases D.ctx.geo.qWidth with hh | hh <;> omega
  have pn' : 0 < (D.ctx.withHs D.hs).geo.pLen ∧ (D.ctx.withHs D.hs).geo.pLen ≤ 384 := pn
  have qn' : (D.ctx.withHs D.hs).geo.qLen ≤ 32 := qn
  have hw : (⟨(D.ctx.withHs D.hs).saved 6, 2 * D.ctx.geo.pLen + D.ctx.geo.qLen⟩ : Region) ∈ s.wr := by
    rw [hwr]; simpa [GenerationContext.withHs] using D.ends.outIn
  obtain ⟨V, R⟩ := hm.rep
  unfold Impl.Dsa.X86_64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok hm.layout R) fun u ⟨hz, hmu, ku⟩ => ?_)
  have mu := hm.congr hmu ku
  have hwu : (⟨(D.ctx.withHs D.hs).saved 6, 2 * D.ctx.geo.pLen + D.ctx.geo.qLen⟩ : Region) ∈ u.wr := by
    rw [ku.2.2]; exact hw
  obtain ⟨Vu, Ru⟩ := mu.rep
  by_cases e : W 19 = 1
  · refine WP.ite true (by simp only [eval, hz, e, beq_self_eq_true]) (fun _ => ?_)
      (fun impossible => Bool.noConfusion impossible)
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Bignum.bytesAt_length _ _ _) rfl)
      fun u₁ ⟨_, _, f₁, k₁⟩ => ?_
    have R₁ : Rep u₁.mem D.ctx.geo.F D.ctx.geo.hash Vu W := Ru.apart o.apart f₁
    exact ⟨Vu, W, lay_of_rep mu.layout Ru R₁ rfl (k₁.gpr (by decide)) k₁.2.2, R₁, h19⟩
  · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr e])
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    unfold Impl.Dsa.X86_64.Generation.outputZero
    refine WP.seq (WP.mono (zeroArgs_ok mu.layout Ru) fun u₁ ⟨L₁, R₁, _, k₁⟩ => ?_)
    refine WP.mono (zeroOut_ok L₁ R₁ (by simp [upd, h6]) (by simpa [upd] using h7) (by omega) (by omega)
      (by rw [k₁.2.2]; exact hwu) o.bound o.apart) fun u₂ ⟨L₂, _, R₂, _, _, _⟩ => ?_
    exact ⟨_, _, L₂, R₂, by simpa [upd] using h19⟩

def StatusTested (D : DonePublic) (t : State) : Prop :=
  StatusAt D t ∧ isa.eval .e t = some (D.status == 2)

theorem statusAt_pins : Pins StatusAt [.rsp] := by
  intro D s t ⟨_, _, Ls, _⟩ ⟨_, _, Lt, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Ls.rsp.trans Lt.rsp.symm

theorem returnStatus_ct :
    RelCT isa (Two StatusAt) Impl.Dsa.X86_64.Generation.Refill.returnStatus (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.returnStatus
  refine RelCT.seq (two_piece (Ψ := StatusTested) [.rsp] statusAt_pins (by taint_decide) fun D s h => ?_) ?_
  · obtain ⟨V, W, L, R, h19⟩ := h
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (W 19 == 2) ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨⟨z, mt⟩, kt⟩ => ?_
    · xrun [ea_sp, L.rsp, L.ld (d := 152) (by decide), R.slot (d := 152) (k := 19) rfl (by decide) rfl]
      rw [sub_beq_zero]
    have Rt : Rep t.mem D.ctx.geo.F D.ctx.geo.hash V W := mt ▸ R
    exact ⟨⟨V, W, lay_of_rep L R Rt rfl (kt.gpr (by decide)) kt.2.2, Rt, h19⟩, by simp only [eval, z, h19]⟩
  refine two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)
  · exact two_taint [] (by intro _ _ _ _ _ r hr; simp at hr) (by taint_decide)

theorem finish_ct (pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (DoneAt 6 pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.finish pLen) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (results_ct 6 pLen qLen hp) (RelCT.seq (two_post (Ψ := StatusAt) ?_
    fun D s h => finishOutput_status h) returnStatus_ct)
  refine two_map (fun D : DonePublic => (⟨D.ctx.withHs D.hs, D.status == 1, D.ws⟩ : OutputPublic))
    (fun D s h => ?_) (finishOutput_ct 6 (Or.inr (Or.inr rfl)))
  obtain ⟨⟨W, hm, h19, _⟩, _, _, hf, _⟩ := h
  exact ⟨⟨W, hm, by rw [h19]⟩, hf⟩

end VG.Proof.Dsa.X86_64.Generation
