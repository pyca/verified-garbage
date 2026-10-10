import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLastProgress
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone

/-! ## From `ResidentRejParseFive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

private theorem afterFirst {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => rowResult σ k 0 168 []) s) :
    Rows v 5 σ (fun k => prefixRow σ k 504) s := h.congr (fun _ _ => rfl)

private theorem afterSecond {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => rowResult σ k 504 112 (prefixRow σ k 504)) s) :
    Rows v 5 σ (fun k => prefixRow σ k 840) s :=
  h.congr (fun k _ => rowResult_prefix σ k 504 112 (by decide))

theorem parseFiveFour_ok {σ s : State} (hp : Pre 4 σ) (h : FirstBlocks 4 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 0 168)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 504 112)) s
      (Rows 4 5 σ (fun k => prefixRow σ k 840)) := by
  apply WP.seq
  refine WP.mono (batchFour_ok hp h.rows (by decide : 0+3*168≤168*5) (by decide) 0)
    fun _ ht => ?_
  exact WP.mono (batchFour_ok hp (afterFirst ht) (by decide : 504+3*112≤168*5) (by decide) 0)
    fun _ hu => afterSecond hu

theorem parseFiveTwo_ok {σ s : State} (hp : Pre 2 σ) (h : FirstBlocks 2 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 0 168)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 504 112)) s
      (Rows 2 5 σ (fun k => prefixRow σ k 840)) := by
  apply WP.seq
  refine WP.mono (batchTwo_ok hp h.rows (by decide : 0+3*168≤168*5) (by decide) 0)
    fun _ ht => ?_
  exact WP.mono (batchTwo_ok hp (afterFirst ht) (by decide : 504+3*112≤168*5) (by decide) 0)
    fun _ hu => afterSecond hu

theorem parseSixthFour_ok {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 6 σ (fun k => prefixRow σ k 840) s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56) s
      (Rows 4 6 σ (fun k => prefixRow σ k 1008)) := by
  refine WP.mono (batchFour_ok hp h (by decide : 840+3*56≤168*6) (by decide) 0) fun _ ht => ?_
  exact ht.congr (fun k _ => rowResult_prefix σ k 840 56 (by decide))

theorem parseSixthTwo_ok {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 6 σ (fun k => prefixRow σ k 840) s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56) s
      (Rows 2 6 σ (fun k => prefixRow σ k 1008)) := by
  refine WP.mono (batchTwo_ok hp h (by decide : 840+3*56≤168*6) (by decide) 0) fun _ ht => ?_
  exact ht.congr (fun k _ => rowResult_prefix σ k 840 56 (by decide))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejLastStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (RegKeep)
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Spec.MlDsa (Zq)

theorem lastProgress_ok {v p : Nat} {σ s : State} {L : Nat → List Zq} {rp ra rb : Reg}
    (hp : Pre v σ) (h : LastProgress v σ L p s) (hpv : 2*p+1<v)
    (hr : FiveRegisters rp ra rb) (hreg : CallRegs rp ra rb) (hrp : s.gpr rp=stateP σ p)
    (ha : s.gpr ra=lastPtr σ (2*p)) (hb : s.gpr rb=lastPtr σ (2*p+1)) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.pair rp ra rb) s fun t =>
      LastProgress v σ L (p+1) t ∧ RegKeep blockRegs s t := by
  refine WP.mono (lastPair_ok hp h.env hpv hr hreg
    (by simpa only [Nat.lt_irrefl,ite_false] using h.pairs p hpv) hrp ha hb)
    fun t ⟨he,hs,oa,ob,hf,hg⟩ => ⟨h.next hp hpv he hf hs oa ob,hg⟩

theorem lastAdvance_ok {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 6 σ L s) (h28 : s.gpr .x28=1) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.advance) s fun t =>
      Rows v 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.advance_ok s)
    fun t ⟨ht,_,hcount⟩ => ⟨h.of_control ht ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [eval_nonzero,hcount,h28]
    rfl

theorem lastFour_step_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 5 σ L s)
    (h22 : s.gpr .x22=stateP σ 0) (h23 : s.gpr .x23=stateP σ 1)
    (h24 : s.gpr .x24=lastPtr σ 0) (h25 : s.gpr .x25=lastPtr σ 1)
    (h26 : s.gpr .x26=lastPtr σ 2) (h27 : s.gpr .x27=lastPtr σ 3)
    (h28 : s.gpr .x28=1) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.step s fun t =>
      Rows 4 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.step
  apply WP.seq
  refine WP.mono (lastProgress_ok hp h.lastProgress (by decide : 2*0+1<4)
    fiveRegisters0 callRegs0 h22 h24 h25) fun a ⟨ha,hga⟩ => ?_
  apply WP.seq
  refine WP.mono (lastProgress_ok hp ha (by decide : 2*1+1<4) fiveRegisters1 callRegs1
    (by rw [hga.gpr .x23 (by decide)]; exact h23)
    (by rw [hga.gpr .x26 (by decide)]; exact h26)
    (by rw [hga.gpr .x27 (by decide)]; exact h27)) fun b ⟨hb,hgb⟩ => ?_
  exact lastAdvance_ok (hb.rows (by decide)) (by
    rw [hgb.gpr .x28 (by decide),
      hga.gpr .x28 (by decide),h28])

theorem lastTwo_step_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 5 σ L s)
    (h22 : s.gpr .x22=stateP σ 0)
    (h24 : s.gpr .x24=lastPtr σ 0) (h25 : s.gpr .x25=lastPtr σ 1)
    (h28 : s.gpr .x28=1) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step s fun t =>
      Rows 2 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step
  apply WP.seq
  refine WP.mono (lastProgress_ok hp h.lastProgress (by decide : 2*0+1<2)
    fiveRegisters0 callRegs0 h22 h24 h25) fun a ⟨ha,hga⟩ => ?_
  exact lastAdvance_ok (ha.rows (by decide)) (by
    rw [hga.gpr .x28 (by decide),h28])

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSixthSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_addImm wp_movz)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Four (squeezeSetup)

def sixthOffsets : List Instr :=
  [.addImm .x .x24 .x24 840,.addImm .x .x25 .x25 840,
   .addImm .x .x26 .x26 840,.addImm .x .x27 .x27 840,.movz .x .x28 1 0]

theorem sixthOffsets_ok (s : State) : WP isa (.block sixthOffsets) s fun t =>
    Only [.x24,.x25,.x26,.x27,.x28] s t ∧
      (∀k<4,t.gpr (bReg k)=s.gpr (bReg k)+840) ∧ t.gpr .x28=1 := by
  unfold sixthOffsets
  refine wp_addImm (by decide) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun c hc ec => wp_addImm (by decide) fun d hd ed =>
      wp_movz fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((((ha.trans hb).trans hc).trans hd).trans ht).mono (by simp)
  · intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24=s.gpr .x24+840
      rw [ht.get .x24,hd.get .x24,hc.get .x24,hb.get .x24,ea]; rfl
    · change t.gpr .x25=s.gpr .x25+840
      rw [ht.get .x25,hd.get .x25,hc.get .x25,eb,ha.get .x25]; rfl
    · change t.gpr .x26=s.gpr .x26+840
      rw [ht.get .x26,hd.get .x26,ec,hb.get .x26,ha.get .x26]; rfl
    · change t.gpr .x27=s.gpr .x27+840
      rw [ht.get .x27,ed,hc.get .x27,hb.get .x27,ha.get .x27]; rfl
  · rw [et]; rfl

theorem sixthSetup_ok (s : State) : WP isa (.block (squeezeSetup 840 1)) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t ∧
      t.gpr .x22=s.gpr .x19 ∧ t.gpr .x23=s.gpr .x19+400 ∧
      (∀k<4,t.gpr (bReg k)=s.gpr .x19+BitVec.ofNat 64 (840+1008*k+840)) ∧
      t.gpr .x28=1 := by
  rw [show squeezeSetup 840 1=(squeezeSetup 0 0).take 6++sixthOffsets from rfl,
    WP.block_append_iff]
  refine WP.mono (squeezePointers_ok s) fun a ⟨ha,h22,h23,hbuf⟩ => ?_
  refine WP.mono (sixthOffsets_ok a) fun t ⟨ht,hptr,h28⟩ => ?_
  refine ⟨(ha.trans ht).mono (by simp),?_,?_,?_,h28⟩
  · rw [ht.get .x22,h22]
  · rw [ht.get .x23,h23]; rfl
  · intro k hk
    rw [hptr k hk,hbuf k hk]
    change (s.gpr .x19+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 840=_
    rw [Offset.add_add]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSixth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)

private theorem sixthSetup_rows {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 5 σ L s) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeSetup 840 1)) s fun t =>
      Rows v 5 σ L t ∧ t.gpr .x22=stateP σ 0 ∧ t.gpr .x23=stateP σ 1 ∧
      (∀k<4,t.gpr (bReg k)=lastPtr σ k) ∧ t.gpr .x28=1 := by
  refine WP.mono (sixthSetup_ok s) fun t ⟨ht,h22,h23,hbuf,h28⟩ => ?_
  refine ⟨h.of_control ht ?_,?_,?_,?_,h28⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [h22,h.env.x19]
    change scr σ=scr σ+BitVec.ofNat 64 0
    simp
  · rw [h23,h.env.x19]; rfl
  · intro k hk
    rw [hbuf k hk,h.env.x19,lastPtr_eq]
    congr 2
    omega

theorem sixthFour_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 5 σ L s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
      Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1) s (Rows 4 6 σ L) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
  apply WP.seq
  refine WP.mono (sixthSetup_rows h) fun a ⟨ha,h22,h23,hbuf,h28⟩ => ?_
  obtain ⟨tr,t,he,ht,hc⟩ := lastFour_step_ok hp ha h22 h23
    (hbuf 0 (by decide)) (hbuf 1 (by decide)) (hbuf 2 (by decide)) (hbuf 3 (by decide)) h28
  exact ⟨_,t,.loopExit he hc,ht⟩

theorem sixthTwo_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 5 σ L s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1) s (Rows 2 6 σ L) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
  apply WP.seq
  refine WP.mono (sixthSetup_rows h) fun a ⟨ha,h22,_,hbuf,h28⟩ => ?_
  obtain ⟨tr,t,he,ht,hc⟩ := lastTwo_step_ok hp ha h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)) h28
  exact ⟨_,t,.loopExit he hc,ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejAdaptive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

/-- The selected adaptive branch either has all rows already full or consumes exactly one final rate block. -/
theorem adaptiveFour_ok {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 4 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56) (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.flags)))) s (Done 4 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil (h.early_done hf hz)
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthFour_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthFour_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ => ht.done hft

/-- The selected adaptive branch either has all rows already full or consumes exactly one final rate block. -/
theorem adaptiveTwo_ok {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 2 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56) (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.flags)))) s (Done 2 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil (h.early_done hf hz)
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthTwo_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthTwo_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ => ht.done hft

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
