module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
meta import VerifiedGarbage.Proof.MlKem.PolyContract
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue

/-! ### `MlDsa.AArch64.Optimized.ResidentRejOutcome`, which this module and modules that import it used -/

section

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResidentRejFinish.lean`, which only this module imported.
section

/-! ## From `ResidentRejCore.lean` -/

@[expose] public section

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
    (by simpa only [hm] using hcounts) h22 (fun k hk => hbuf k (by omega_using [hk]))) fun c hc => ?_
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
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

def Outcome (v : Nat) (σ t : State) : Prop :=
  let r := (t.gpr .x0).setWidth 32
  (r=1 → ∀k<v,Proof.MlDsa.Reduced t.mem (Proof.MlDsa.poly4 (aP σ) k)) ∧
    ((r=1 ∧ ∀k<v,∃b : Spec.MlDsa.Bounds,Spec.MlDsa.rejNTTPoly b.rejNTT
      (Proof.MlDsa.seed4 σ.mem (seedP σ) k)=some (Proof.MlDsa.polyAt t.mem (Proof.MlDsa.poly4 (aP σ) k))) ∨
     (r=0 ∧ ∃k<v,Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
      (Proof.MlDsa.seed4 σ.mem (seedP σ) k)=none))

theorem prefixRow_spec (σ : State) (k : Nat) :
    prefixRow σ k 1008=rnFold [] (Spec.MlDsa.G (Proof.MlDsa.seed4 σ.mem (seedP σ) k) 1008) := by
  unfold prefixRow
  rw [streamBytes_full]

theorem Result.outcome {v : Nat} {σ t : State} (h : Result v σ t) : Outcome v σ t := by
  unfold Outcome
  by_cases hall : ∀k<v,(prefixRow σ k 1008).length=256
  · have hr : (t.gpr .x0).setWidth 32=1 := by rw [h.status,ite_eq_left hall]; rfl
    have hp : ∀k<v,Proof.MlDsa.PolyIs t.mem (polyP σ k) (toPoly (prefixRow σ k 1008)) :=
      fun k hk => stored_polyIs (h.stored k hk) (hall k hk)
    refine ⟨fun _ k hk => (hp k hk).1,.inl ⟨hr,fun k hk =>
      ⟨{Spec.MlDsa.minBounds with rejNTT := 1008},?_⟩⟩⟩
    have hs := hall k hk
    rw [prefixRow_spec] at hs
    rw [rejNTT_some hs]
    exact congrArg some (by
      rw [← prefixRow_spec]
      exact (hp k hk).2.symm)
  · have hr : (t.gpr .x0).setWidth 32=0 := by rw [h.status,ite_eq_right hall]; rfl
    refine ⟨fun hh => absurd (hr.symm.trans hh) (by decide),.inr ⟨hr,?_⟩⟩
    simp only [Classical.not_forall] at hall
    obtain ⟨k,hk,hbad⟩ := hall
    refine ⟨k,hk,rejNTT_none (B := 1008) (by decide) (by decide) ?_⟩
    simpa only [prefixRow_spec] using hbad

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

/-! ## From `ResidentRejTimingBlocks.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- Split a straight-line prefix while retaining its continuation. -/
theorem blockPrefix {P Q : State → State → Prop} {a b : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block a) (.seq (.block b) c)) Q) :
    RelCT isa P (.seq (.block (a++b)) c) Q := by
  intro s t tr ur s' t' hp es et
  cases es with
  | seq ea ec =>
    cases et with
    | seq eb ed =>
      rw [Exec.block_iff,execBlock_append] at ea eb
      obtain ⟨⟨sa,ta⟩,ha,hb⟩ := Option.bind_eq_some_iff.mp ea
      obtain ⟨⟨sb,tb⟩,hc,hd⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨⟨ua,va⟩,he,hf⟩ := Option.bind_eq_some_iff.mp eb
      obtain ⟨⟨ub,vb⟩,hg,hh⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at hd hh
      obtain ⟨rfl,rfl⟩ := hd
      obtain ⟨rfl,rfl⟩ := hh
      obtain ⟨hl,hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha) (.seq (.block hc) ec))
        (.seq (.block he) (.seq (.block hg) ed))
      exact ⟨by simpa only [List.append_assoc] using hl,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailReadValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok)

/-- Masking makes the legacy cleanup decision depend on exactly the final
three candidate bytes, independently of the fourth byte read by LDR. -/
theorem tailRead_value {s : State} {k : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailRead k)) s fun t => Only [.x6,.x7] s t ∧
      (t.gpr .x6).toNat=candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) ∧
      (t.gpr .x7).toNat=8380417 := by
  unfold tailRead
  simp only [List.cons_append,List.nil_append]
  refine wp_addImm (by omega_arith) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_ldrw (a := s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) (by decide)
      (by rw [ptr_zero,eb,ea,Offset.add_add])
      (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hr) fun c hc ec =>
    wp_movz fun d hd ed => wp_movk1 fun e he ee =>
    wp_and fun f hf ef => movQ_ok fun t ht et => wp_nil ?_
  refine ⟨((((((ha.trans hb).trans hc).trans hd).trans he).trans hf).trans ht).mono (by decide),?_,et⟩
  have h7 : e.gpr .x7=0x7fffff := by rw [ee,ed]; rfl
  rw [ht.get .x6,ef,h7,he.get .x6,hd.get .x6,ec,hb.mem,ha.mem]
  exact scalar_candidate _ _

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailOutput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem zeroTail_frame_ok {v k : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s)
    (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (fun t => Done v σ t ∧ Frame [aR v σ] s.mem t.mem) := by
  have hk4 : k<4 := by have := hp.streams; omega_arith
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail
  apply WP.seq
  refine wp_ldrx (a := countP σ k) (by
    unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega_arith)
    (by rw [h.env.x19]; rfl) (in_scr_rd hp h.env.wr (by
      unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega_arith)) fun a ha ea => wp_nil ?_
  have hd : Done v σ a := h.of_control ha (by decide)
  have hc : (a.gpr .x4).toNat=256-(prefixRow σ k 1008).length := by
    rw [ea]; exact h.counts k hk
  by_cases hz : a.gpr .x4=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨hd,by rw [ha.mem]; exact Frame.refl _ _⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (a.gpr .x4==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    have hl : (prefixRow σ k 1008).length<256 := by
      have := h.length k hk
      have hn : (a.gpr .x4).toNat≠0 := by intro e; exact hz (BitVec.eq_of_toNat_eq e)
      omega_arith
    change WP isa (.block (tailCursor k++tailRead k++tailAdjust)) a _
    refine WP.mono (tailSetup_ok hp hd.env hk hl hc) fun b hb => ?_
    have hdb : Done v σ b := hd.of_control hb.1 (by decide)
    obtain ⟨skip,hskip,hptr,hcount,hzero⟩ := hb.2
    by_cases hz' : b.gpr .x4=0#64
    · refine WP.ite true (by rw [eval_zero,hz']; rfl) (fun _ => ?_) (by simp)
      exact WP.block_nil ⟨hdb,by rw [hb.1.mem,ha.mem]; exact Frame.refl _ _⟩
    · refine WP.ite false (by
        rw [eval_zero]
        have he : (b.gpr .x4==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz'
        rw [he]) (by simp) (fun _ => ?_)
      have hn : 0<256-((prefixRow σ k 1008).length+skip) := by
        have hn' : (b.gpr .x4).toNat≠0 := by intro e; exact hz' (BitVec.eq_of_toNat_eq e)
        omega_arith
      refine WP.mono (tailLoop_ok hn (by omega_arith) hptr hcount ?_) fun t ht => ?_
      · intro i hi
        rw [hdb.env.wr]
        refine ⟨aR v σ,by simp [hp.wr],?_⟩
        change (aR v σ).Contains (((aP σ+BitVec.ofNat 64 (1024*k))+
          BitVec.ofNat 64 (4*((prefixRow σ k 1008).length+skip)))+BitVec.ofNat 64 (4*i)) 4
        rw [Offset.add_add,Offset.add_add]
        exact Offset.contains_base (aP σ) (by omega_arith) (by have := hp.streams; omega_arith)
      · refine ⟨hdb.tailKeep hp hk (by omega_arith) (by omega_arith) ht.1 ht.2,?_⟩
        have hf : Frame [aR v σ] b.mem t.mem := ht.2.sub (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨aR v σ,by simp,fun x hx => poly_sub hk x (tailRange_sub (by omega_arith) x hx)⟩)
        rw [hb.1.mem,ha.mem] at hf
        exact hf


end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailBuffers.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

abbrev TailReady (v : Nat) (σ s : State) := Done v σ s ∧
  ∀k<v,∀j<1008,s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j

theorem zeroTail_ready {v k : Nat} {σ s : State} (hp : Pre v σ)
    (h : TailReady v σ s) (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (TailReady v σ) := by
  refine WP.mono (zeroTail_frame_ok hp h.1 hk) fun t ⟨ht,hf⟩ => ⟨ht,?_⟩
  intro j hj d hd
  have hb : (scrR σ).Contains (bufP σ j+BitVec.ofNat 64 d) 1 := by
    change (scrR σ).Contains ((scr σ+BitVec.ofNat 64 (840+1008*j))+BitVec.ofNat 64 d) 1
    rw [Offset.add_add]
    exact Offset.contains_base (scr σ) (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith)
  rw [hf (bufP σ j+BitVec.ofNat 64 d) (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.a_scr.symm _ hb)]
  exact h.2 j hj d hd

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailInspect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem tailInspect_ok {s : State} {k len : Nat} (hk : k<4) (hl : len≤256)
    (hc : (s.gpr .x4).toNat=256-len)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailCursor k++tailRead k)) s fun t =>
      Only [.x3,.x6,.x7] s t ∧
      t.gpr .x3=coeffAddr (s.gpr .x21+BitVec.ofNat 64 (1024*k)) len ∧
      (t.gpr .x6).toNat=candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) ∧
      (t.gpr .x7).toNat=8380417 := by
  rw [WP.block_append_iff]
  refine WP.mono (tailCursor_ok hk hl hc) fun a ⟨ha,h3⟩ => ?_
  refine WP.mono (tailRead_value hk (by rw [ha.rd,ha.wr,ha.get .x19]; exact hr))
    fun t ⟨ht,h6,h7⟩ => ?_
  refine ⟨(ha.trans ht).mono (by decide),?_,?_,h7⟩
  · rw [ht.get .x3]; exact h3
  · rw [ha.mem,ha.get .x19] at h6
    exact h6

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure TailChecks (k : Nat) where
  countHint : VG.Taint.Hint VG.AArch64.Taint.T
  inspectHint : VG.Taint.Hint VG.AArch64.Taint.T
  count : (taint.check (Taint.ofRegs [.x19])
    (.block [.ldr .x .x4 .x19 (counts+8*k)]) countHint).isSome=true
  inspect : (taint.check (Taint.ofRegs [.x4,.x19,.x21])
    (.block (tailCursor k++tailRead k)) inspectHint).isSome=true

private theorem countLoad_ok {s : State} {k len : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (countAddress s k) 8)
    (hc : (s.mem.readW (countAddress s k) 64).toNat=256-len) :
    WP isa (.block [.ldr .x .x4 .x19 (counts+8*k)]) s fun t =>
      Only [.x4] s t ∧ (t.gpr .x4).toNat=256-len := by
  refine wp_ldrx (a := countAddress s k) (by unfold counts; omega_arith) (by rfl) hr
    fun t ht et => wp_nil ⟨ht,?_⟩
  rw [et]; exact hc

/-- Cleanup's sole data-dependent decision is the masked final candidate;
its ignored overread byte is deliberately absent from this relation. -/
theorem zeroTailRaw_relCT {k len : Nat} {σ τ : State}
    (hk : k<4) (hl : len≤256) (checks : TailChecks k)
    (hsp : σ.sp=τ.sp) (h19 : σ.gpr .x19=τ.gpr .x19) (h21 : σ.gpr .x21=τ.gpr .x21)
    (crs : InRegions (σ.rd++σ.wr) (countAddress σ k) 8)
    (crt : InRegions (τ.rd++τ.wr) (countAddress τ k) 8)
    (cs : (σ.mem.readW (countAddress σ k) 64).toNat=256-len)
    (ct : (τ.mem.readW (countAddress τ k) 64).toNat=256-len)
    (rs : InRegions (σ.rd++σ.wr) (σ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4)
    (rt : InRegions (τ.rd++τ.wr) (τ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4)
    (hm : candidate σ.mem (σ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))=
      candidate τ.mem (τ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (Four.zeroTail k) (fun _ _ => True) := by
  have loadCT : RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block [.ldr .x .x4 .x19 (counts+8*k)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,h19]⟩)
      checks.count
  unfold Four.zeroTail
  refine RelCT.seq (loadCT.wp (fun _ _ h => by
    rcases h with ⟨rfl,rfl⟩
    exact ⟨countLoad_ok hk crs cs,countLoad_ok hk crt ct⟩)) ?_
  apply RelCT.ite
  · intro s t h
    have he : s.gpr .x4=t.gpr .x4 := BitVec.eq_of_toNat_eq (h.2.1.2.trans h.2.2.2.symm)
    rw [eval_zero,eval_zero,he]
  · exact RelCT.block_nil (fun _ _ _ => True.intro)
  · intro s t tr ur s' t' h es et
    have ha := h.1.2.1.1
    have hb := h.1.2.2.1
    have hc := h.1.2.1.2
    have hd := h.1.2.2.2
    have sp : s.sp=t.sp := ha.sp.trans (hsp.trans hb.sp.symm)
    have e19 : s.gpr .x19=t.gpr .x19 := by rw [ha.get .x19,hb.get .x19]; exact h19
    have e21 : s.gpr .x21=t.gpr .x21 := by rw [ha.get .x21,hb.get .x21]; exact h21
    have e4 : s.gpr .x4=t.gpr .x4 := BitVec.eq_of_toNat_eq (hc.trans hd.symm)
    have wpS := tailInspect_ok hk hl hc (by rw [ha.rd,ha.wr,ha.get .x19]; exact rs)
    have wpT := tailInspect_ok hk hl hd (by rw [hb.rd,hb.wr,hb.get .x19]; exact rt)
    have inspectCT : RelCT isa (fun a b => a=s ∧ b=t)
        (.block (tailCursor k++tailRead k)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x4,.x19,.x21])
        (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨sp,by simp [Taint.ofRegs,RegSet.mem_ofList,e4,e19,e21]⟩)
        checks.inspect
    have result : RelCT isa (fun a b => a=s ∧ b=t)
        (.seq (.block (tailCursor k++tailRead k++tailAdjust))
          (.ite (.zero .x .x4) (.block [])
            (.loop (.block [.str .w .x9 .x3 0,.addImm .x .x3 .x3 4,.subImm .x .x4 .x4 1])
              (.nonzero .x .x4)))) (fun _ _ => True) := by
      apply blockPrefix
      refine RelCT.seq (inspectCT.wp (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)) ?_
      exact RelCT.taint (A := taint) (Taint.ofRegs [.x3,.x4,.x6,.x7])
        (fun a b hh => by
          obtain ⟨_,⟨ka,a3,a6,a7⟩,⟨kb,b3,b6,b7⟩⟩ := hh
          refine ⟨ka.sp.trans (sp.trans kb.sp.symm),?_⟩
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false]
          intro r hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [a3,b3,e21]
          · rw [ka.get .x4,kb.get .x4,e4]
          · apply BitVec.eq_of_toNat_eq
            rw [a6,b6,ha.mem,hb.mem,ha.get .x19,hb.get .x19]
            exact hm
          · exact BitVec.eq_of_toNat_eq (a7.trans b7.symm)) (by taint_decide)
    exact result _ _ _ _ _ _ ⟨rfl,rfl⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailReadyTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 def tailChecks (k : Nat) (hk : k<4) : TailChecks k := by
  by_cases h0 : k=0
  · subst k; constructor <;> taint_decide
  by_cases h1 : k=1
  · subst k; constructor <;> taint_decide
  by_cases h2 : k=2
  · subst k; constructor <;> taint_decide
  have h3 : k=3 := by omega_arith
  subst k
  constructor <;> taint_decide

private theorem tail_candidate_eq {v k : Nat} {σ τ s t : State}
    (pub : Pub v σ τ) (hs : TailReady v σ s) (ht : TailReady v τ t) (hk : k<v) :
    candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))=
      candidate t.mem (t.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) := by
  rw [hs.1.env.x19,ht.1.env.x19]
  rw [←Offset.add_add (scr σ) (840+1008*k) 1005,
    ←Offset.add_add (scr τ) (840+1008*k) 1005]
  change candidate s.mem (bufP σ k+BitVec.ofNat 64 1005)=
    candidate t.mem (bufP τ k+BitVec.ofNat 64 1005)
  unfold candidate
  have hb (j : Nat) (hj : j<1008) :
      s.mem (bufP σ k+BitVec.ofNat 64 j)=t.mem (bufP τ k+BitVec.ofNat 64 j) := by
    rw [hs.2 k hk j hj,ht.2 k hk j hj,pub.byte hk j]
  rw [hb 1005 (by decide)]
  have h1 : ∀p : Addr,(p+BitVec.ofNat 64 1005)+1=p+BitVec.ofNat 64 1006 := by
    intro p; exact Offset.add_add p 1005 1
  have h2 : ∀p : Addr,(p+BitVec.ofNat 64 1005)+2=p+BitVec.ofNat 64 1007 := by
    intro p; exact Offset.add_add p 1005 2
  rw [h1,h1,h2,h2,hb 1006 (by decide),hb 1007 (by decide)]

theorem zeroTail_relCT {v k : Nat} {σ τ : State}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v) :
    RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t) (Four.zeroTail k)
      (fun s t => TailReady v σ s ∧ TailReady v τ t) := by
  have h4 : k<4 := by have:=hp.streams; omega_arith
  have ct : RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t) (Four.zeroTail k)
      (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hs := h.1.1.env
    have ht := h.2.1.env
    exact zeroTailRaw_relCT h4 (h.1.1.length k hk) (tailChecks k h4)
      (hs.sp.trans (pub.2.2.2.1.trans ht.sp.symm))
      (by rw [hs.x19,ht.x19,pub.2.2.1]) (by rw [hs.x21,ht.x21,pub.2.1])
      (by rw [segment_count_eq hs]; exact in_scr_rd hp hs.wr (by unfold counts; omega_arith))
      (by rw [segment_count_eq ht]; exact in_scr_rd hq ht.wr (by unfold counts; omega_arith))
      (by rw [segment_count_eq hs]; exact h.1.1.counts k hk)
      (by rw [segment_count_eq ht,pub.prefix hk 1008]; exact h.2.1.counts k hk)
      (by rw [hs.x19]; exact in_scr_rd hp hs.wr (by omega_arith))
      (by rw [ht.x19]; exact in_scr_rd hq ht.wr (by omega_arith))
      (tail_candidate_eq pub h.1 h.2 hk) _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  exact (ct.wp (fun _ _ h => ⟨zeroTail_ready hp h.1 hk,zeroTail_ready hq h.2 hk⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem tailRows_relCT {v : Nat} {σ τ : State}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ)
    (ks : List Nat) (hks : ∀k∈ks,k<v) :
    RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t)
      (ks.foldr (fun k rest => .seq (Four.zeroTail k) rest) (.block []))
      (fun s t => TailReady v σ s ∧ TailReady v τ t) := by
  induction ks with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons k ks ih =>
    exact RelCT.seq (zeroTail_relCT hp hq pub (hks k (by simp)))
      (ih (fun j hj => hks j (by simp [hj])))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
