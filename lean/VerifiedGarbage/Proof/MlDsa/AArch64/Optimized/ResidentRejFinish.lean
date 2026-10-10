import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi

/-! ## From `ResidentRejCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- Full selected four-stream front end, parameterized only by its final cleanup and ABI return. -/
theorem four_of_finish {σ : State} {Q : State → Prop} (hp : Pre 4 σ)
    (hfinish : ∀s,Done 4 σ s → WP isa
      (.seq Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) s Q) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.code σ Q := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.code
  apply WP.seq
  refine WP.mono (startFour_ok hp) fun a ⟨ha,hpairs,hcounts⟩ => ?_
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env ha) fun b ⟨hb,hm,h22,h23,hbuf⟩ => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (firstFour_ok hp hb (by simpa only [hm] using hpairs)
    (by simpa only [hm] using hcounts) h22 h23 hbuf) fun c hc => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (parseFiveFour_ok hp hc) fun d hd => ?_
  apply WP.seq
  refine WP.mono (flagsSemantic_ok hp hd) fun e ⟨he,hf⟩ => ?_
  apply WP.seq
  exact WP.mono (adaptiveFour_ok hp he hf) hfinish

/-- The two-stream front end has its own seed/output footprint and otherwise the same exact algorithm. -/
theorem two_of_finish {σ : State} {Q : State → Prop} (hp : Pre 2 σ)
    (hfinish : ∀s,Done 2 σ s → WP isa
      (.seq Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) s Q) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code σ Q := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
  apply WP.seq
  refine WP.mono (startTwo_ok hp) fun a ⟨ha,hpairs,hcounts⟩ => ?_
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env ha) fun b ⟨hb,hm,h22,_,hbuf⟩ => ?_
  apply WP.seq
  refine WP.mono (firstTwo_ok hp hb (by simpa only [hm] using hpairs)
    (by simpa only [hm] using hcounts) h22 (fun k hk => hbuf k (by omega))) fun c hc => ?_
  apply WP.assoc
  apply WP.seq
  refine WP.mono (parseFiveTwo_ok hp hc) fun d hd => ?_
  apply WP.seq
  refine WP.mono (flagsSemantic_ok hp hd) fun e ⟨he,hf⟩ => ?_
  apply WP.seq
  exact WP.mono (adaptiveTwo_ok hp he hf) hfinish

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample

structure Result (v : Nat) (σ t : State) : Prop where
  abi : abiPreserved σ t
  frame : Frame [aR v σ,scrR σ] σ.mem t.mem
  rd : t.rd=σ.rd
  wr : t.wr=σ.wr
  stored : ∀k<v,Stored t.mem (polyP σ k) (prefixRow σ k 1008)
  status : t.gpr .x0=if (∀k<v,(prefixRow σ k 1008).length=256) then 1#64 else 0#64

 theorem finish_ok {v : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s) :
    WP isa (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) s (Result v σ) := by
  refine wp_subImm (by decide) fun a ha ea => wp_lsr (by decide) fun b hb eb => ?_
  have he : Env v σ b := h.env.lowStep (rs := [])
    (by rw [hb.mem,ha.mem]; exact Frame.refl _ _) (by simp)
    (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.sp.trans ha.sp)
    (fun r hr => by
      have hn : r∉[Reg.x27] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [hb.get r hn,ha.get r hn])
  have eflag : b.gpr .x27=if (∀k<v,(prefixRow σ k 1008).length=256) then 1#64 else 0#64 := by
    rw [eb,ea,smallFlag_status _ h.flags.bound]
    by_cases hz : s.gpr .x27=0#64
    · simp only [ite_eq_left hz,ite_eq_left (h.flags.zero.mp hz)]
    · simp only [ite_eq_right hz,ite_eq_right (fun he => hz (h.flags.zero.mpr he))]
  refine WP.mono (epi_with he (fun d n hn => in_scr_rd hp he.wr hn)) fun t ht => ?_
  exact ⟨ht.1,by rw [ht.2.1]; exact he.frame,ht.2.2.2.1.trans he.rd,
    ht.2.2.2.2.trans he.wr,by simpa only [ht.2.1,hb.mem,ha.mem] using h.stored,
    ht.2.2.1.trans eflag⟩

theorem four_ok {σ : State} (hp : Pre 4 σ) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.code σ (Result 4 σ) := by
  apply four_of_finish hp
  intro s hs
  apply WP.seq
  exact WP.mono (tailZerosFour_ok hp hs) fun t ht => finish_ok hp ht

theorem two_ok {σ : State} (hp : Pre 2 σ) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code σ (Result 2 σ) := by
  apply two_of_finish hp
  intro s hs
  apply WP.seq
  exact WP.mono (tailZerosTwo_ok hp hs) fun t ht => finish_ok hp ht

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
