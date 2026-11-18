module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
public import VerifiedGarbage.Proof.MlDsa.RejNTT2Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlKem.Bits
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
meta import VerifiedGarbage.Proof.MlDsa.RejNTT2Contract
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import Std.Tactic.BVDecide.Normalize.BitVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
meta import Std.Tactic.BVDecide.Normalize.BitVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone

/-! ### `MlDsa.AArch64.Optimized.ResidentRejTimingDone`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

/-- A failing adaptive parse retains the complete public XOF buffer used by
legacy tail cleanup; successful early completion needs no sixth block. -/
structure TimingDone (v : Nat) (σ s : State) : Prop where
  done : Done v σ s
  bytes : s.gpr .x27≠0#64 → ∀k<v,∀j<1008,
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j

theorem adaptiveFour_timingDone {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 4 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
        Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56)
          (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.flags)))) s (TimingDone 4 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨h.early_done hf hz,fun hn => False.elim (hn hz)⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthFour_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthFour_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ =>
      ⟨ht.done hft,fun _ k hk j hj => ht.bytes k hk j hj⟩

theorem adaptiveTwo_timingDone {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 2 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
        Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56)
          (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.flags)))) s (TimingDone 2 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨h.early_done hf hz,fun hn => False.elim (hn hz)⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthTwo_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthTwo_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ =>
      ⟨ht.done hft,fun _ k hk j hj => ht.bytes k hk j hj⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

/-! ### `MlDsa.AArch64.Optimized.ResidentRejBatchTiming`, which only this module used -/

section

/-! ## From `ResidentRejScalarTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Extraction may overread ignored bytes.  Its trace depends only on the input
and output cursors; candidate equality is re-established from the functional
three-byte extraction theorem before the next loop decision. -/
theorem scalarStep_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x2,.x3]))
    (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr))) :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- Both executions take the same scalar iteration from equal meaningful input,
even when their original output buffers and ignored overread bytes differ. -/
theorem scalarLoopStep_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => ParseInv σ b p n L (d+1) s ∧ ParseInv τ b p n L (d+1) t ∧
        s.gpr .x16=t.gpr .x16 ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5 ∧
        t.gpr .x16=t.gpr .x4*t.gpr .x5) := by
  intro s t tr ur s' t' hp es et
  have he := hp.1.publicRegs hm hsp hp.2
  have ht' := scalarStep_ct s t tr ur s' t' trivial trivial
    ⟨he.1,fun r hr => he.2 r (by
      simp only [VG.AArch64.Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp)⟩ es et
  obtain ⟨_,u,eu,hu⟩ := scalarLoopStep_ok hs hp.1 hd hc
  obtain ⟨_,v,ev,hv⟩ := scalarLoopStep_ok ht hp.2 hd (by rw [← parsed_eq hm (by omega_arith) L]; exact hc)
  obtain ⟨_,rfl⟩ := Exec.det es eu
  obtain ⟨_,rfl⟩ := Exec.det et ev
  have hg := hu.1.publicRegs hm hsp hv.1
  exact ⟨ht',hu.1,hv.1,(by rw [hu.2,hv.2,hg.2 .x4 (by simp),hg.2 .x5 (by simp)]),hu.2,hv.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWidePhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def WideReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=16 ∧
    s.gpr .x16=(if 16≤(s.gpr .x4).toNat ∧ 16≤(s.gpr .x5).toNat then 16 else 0)

theorem widePhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ j%4=d%4) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1,rfl⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4,hp.1.1.1.x5] at hg
    have hgood : 16≤256-(parsed σ b L d).length ∧ 16≤n-d := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    exact wideLoop_relCT hs ht hm hsp (by omega_arith) (by omega_arith) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejFourPhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def FourReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=4 ∧
    s.gpr .x16=(if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0)

theorem fourPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop vectorBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t  ) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4] at hg
    have hcap : 4≤256-(parsed σ b L d).length := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    have hcount : n-d≠0 := by
      intro hn
      have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq (hp.1.1.1.x5.trans hn)
      have he := hp.2
      rw [eval_zero,hg,ite_eq_left hcap,hx] at he
      contradiction
    have hb := hp.1.1.1.bound
    exact fourLoop_relCT hs ht hm hsp (by omega_arith) hmod (by omega_arith) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejScalarLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem guard_nonzero {s : State} (he : isa.eval (.nonzero .x .x16) s=some true)
    (hg : s.gpr .x16=s.gpr .x4*s.gpr .x5) :
    (s.gpr .x4).toNat≠0 ∧ (s.gpr .x5).toNat≠0 := by
  have hn : s.gpr .x16≠0#64 := by
    intro hz
    rw [eval_nonzero,hz] at he
    contradiction
  constructor
  · intro hz
    have hx : s.gpr .x4=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.zero_mul]
  · intro hz
    have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.mul_zero]

theorem scalarLoop_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.loop (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
        (.nonzero .x .x16)) (fun _ _ => True) := by
  let I := fun m s t => ∃j,j<n ∧ (parsed σ b L j).length<256 ∧ n-j=m ∧
    ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t
  have hstep : ∀m,RelCT isa (I m)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => isa.eval (.nonzero .x .x16) s=isa.eval (.nonzero .x .x16) t ∧
        (isa.eval (.nonzero .x .x16) s=some false → True) ∧
        (isa.eval (.nonzero .x .x16) s=some true → ∃m'<m,I m' s t)) := by
    intro m s t tr ur s' t' hp es et
    obtain ⟨j,hj,hc',rfl,hp⟩ := hp
    obtain ⟨htrace,ha,hb,heq,hga,hgb⟩ := scalarLoopStep_relCT hs ht hm hsp hj hc' _ _ _ _ _ _ hp es et
    refine ⟨htrace,by rw [eval_nonzero,eval_nonzero,heq],fun _ => trivial,?_⟩
    intro hcontinue
    obtain ⟨h4,h5⟩ := guard_nonzero hcontinue hga
    rw [ha.x4] at h4
    rw [ha.x5] at h5
    have hj' : j+1<n := by have := ha.bound; omega_arith
    have hc'' : (parsed σ b L (j+1)).length<256 := by omega_arith
    exact ⟨n-(j+1),by omega_arith,j+1,hj',hc'',rfl,ha,hb⟩
  exact (RelCT.loop I hstep (n-d)).mono
    (fun _ _ hp => ⟨d,hd,hc,rfl,hp⟩) (fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejScalarPhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def ScalarReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5

theorem scalarBranch_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) scalarLoop) (fun _ _ => True) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2,hp.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ _ => trivial)
  · intro s t tr ur s' t' hp es et
    have hnonzero : s.gpr .x16≠0#64 := by
      intro hz
      have hh := hp.2
      rw [eval_zero,hz] at hh
      contradiction
    have h4 : (s.gpr .x4).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x4=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.zero_mul]
    have h5 : (s.gpr .x5).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x5=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.mul_zero]
    rw [hp.1.1.1.x4] at h4
    rw [hp.1.1.1.x5] at h5
    have hb := hp.1.1.1.bound
    exact scalarLoop_relCT hs ht hm hsp (by omega_arith) (by omega_arith) _ _ _ _ _ _ ⟨hp.1.1.1,hp.1.2.1⟩ es et

private theorem scalarSetup_ok {σ s : State} {b p : Addr} {n d : Nat} {L : List VG.Spec.MlDsa.Zq}
    (h : ParseInv σ b p n L d s) :
    WP isa (.block [.mul .x .x16 .x4 .x5]) s (ScalarReady σ b p n d L) := by
  have hw : WP isa (.block [.mul .x .x16 .x4 .x5]) s fun t =>
      Only [.x16] s t ∧ t.gpr .x16=s.gpr .x4*s.gpr .x5 :=
    wp_mul fun t ht et => wp_nil ⟨ht,et⟩
  refine WP.mono (WP.keepV (by decide) hw) fun t ⟨⟨ht,hg⟩,hv⟩ => ?_
  exact ⟨h.of_control (ht.mono (by decide)) hv,by rw [ht.get .x4,ht.get .x5]; exact hg⟩

theorem scalarPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.seq (.block [.mul .x .x16 .x4 .x5])
        (.ite (.zero .x .x16) (.block []) scalarLoop)) (fun _ _ => True) := by
  apply RelCT.seq (R := fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.publicRegs hm hsp hp.2
    have hct : RelCT isa (fun s t => s.sp=t.sp)
        (.block [.mul .x .x16 .x4 .x5]) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)
    obtain ⟨_,a,ea,ha⟩ := scalarSetup_ok hp.1
    obtain ⟨_,b,eb,hb⟩ := scalarSetup_ok hp.2
    obtain ⟨_,rfl⟩ := Exec.det es ea
    obtain ⟨_,rfl⟩ := Exec.det et eb
    exact ⟨(hct _ _ _ _ _ _ hg.1 es et).1,ha,hb⟩
  · exact scalarBranch_relCT hs ht hm hsp

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejControlTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem control_pair {P Q R S : State → Prop} {c : Prog isa}
    (hsp : ∀s t,P s → Q t → s.sp=t.sp)
    (hl : ∀s,P s → WP isa c s R) (hr : ∀s,Q s → WP isa c s S)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hc : (taint.check (Taint.ofRegs []) c hint).isSome=true) :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => R s ∧ S t) := by
  have hh : RelCT isa (fun s t => P s ∧ Q t) c (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨hsp _ _ h.1 h.2,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) hc
  exact (hh.wp (fun _ _ h => ⟨hl _ h.1,hr _ h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem fourSetup_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (vectorSetup++guard))
      (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => fourSetup_ok h) (fun _ h => fourSetup_ok h) (by taint_decide)

theorem wideControl_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (([.movz .x .x17 16 0] : List Instr)++wideGuard))
      (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => wideControl_ok h) (fun _ h => wideControl_ok h) (by taint_decide)

theorem parseFour_relCT (v : Nat) {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (parse4 v) (fun _ _ => True) := by
  unfold parse4
  apply RelCT.seq (fourSetup_relCT hsp)
  apply RelCT.seq (fourPhase_relCT hs ht hm hsp hmod)
  exact RelCT.exists_ (fun j => scalarPhase_relCT hs ht hm hsp (d := j))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejParseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def Start (s : State) (b p : Addr) (n : Nat) (L : List Zq) : Prop :=
  s.gpr .x2=b ∧ s.gpr .x3=coeffAddr p L.length ∧ (s.gpr .x4).toNat=256-L.length ∧
    (s.gpr .x5).toNat=n ∧ (s.gpr .x9).toNat=q ∧ Stored s.mem p L

theorem vectorSetup_start {σ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (h : Start σ b p n L) : WP isa (.block vectorSetup) σ (ParseInv σ b p n L 0) := by
  refine WP.mono (vectorSetup_ok (s := σ) h.2.2.2.2.1) fun a ⟨ha,hc,_,h0,h10⟩ => ?_
  refine ⟨ha.only.keep.mono (by decide),by rw [ha.only.mem]; exact Frame.refl _ _,hc,
    Nat.zero_le _,?_,?_,?_,?_,h10,h0,?_⟩
  · rw [ha.only.get .x2,h.1]; exact (ptr_zero b).symm
  · rw [ha.only.get .x3]; exact h.2.1
  · rw [ha.only.get .x4]; exact h.2.2.1
  · rw [ha.only.get .x5]; exact h.2.2.2.1
  · rw [ha.only.mem]; exact h.2.2.2.2.2

theorem parse_relCT (v : Nat) {σ τ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (ss : Start σ b p n L) (st : Start τ b p n L)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : n%4=0) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (parse v) (fun _ _ => True) := by
  unfold parse
  apply RelCT.seq (R := fun s t => WideReady σ b p n 0 L s ∧ WideReady τ b p n 0 L t)
  · rw [List.append_assoc]
    apply RelCT.block_append
    apply RelCT.seq (R := fun s t => ParseInv σ b p n L 0 s ∧ ParseInv τ b p n L 0 t)
    · exact control_pair (fun _ _ h1 h2 => by subst h1; subst h2; exact hsp)
        (fun s h => by subst s; exact vectorSetup_start ss)
        (fun t h => by subst t; exact vectorSetup_start st) (by taint_decide)
    · exact wideControl_relCT hsp
  · apply RelCT.seq (widePhase_relCT hs ht hm hsp)
    intro s t tr ur s' t' hp es et
    obtain ⟨j,hj,hk,hjm⟩ := hp
    exact parseFour_relCT v hs ht hm hsp (by rw [hjm,hmod]) _ _ _ _ _ _ ⟨hj,hk⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegmentTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem layout_only {s t : State} {b p : Addr} {n : Nat} {rs : List Reg}
    (h : StreamLayout s b p n) (ht : Only rs s t) : StreamLayout t b p n := by
  refine ⟨h.bound,?_,?_,?_,?_,h.disjoint⟩
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read16 j hj
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read4 j hj
  · intro j hj; rw [ht.wr]; exact h.write4 j hj
  · intro j hj; rw [ht.wr]; exact h.write16 j hj

/-- Segment timing needs equality only for the consumed candidate bytes, not
for preexisting output bytes or the ignored fourth byte of scalar loads. -/
theorem segment_relCT (v n : Nat) (hn : n<65536)
    {hintSetup hintNext : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x26]) (.block (setup n)) hintSetup).isSome=true)
    (checkNext : (taint.check (Taint.ofRegs [.x26]) (.block segmentNext) hintNext).isSome=true)
    {σ τ : State} {b p c : Addr} {L : List Zq} (hL : L.length≤256) (hmod : n%4=0)
    (hsp : σ.sp=τ.sp)
    (s24 : σ.gpr .x24=b) (s25 : σ.gpr .x25=p) (s26 : σ.gpr .x26=c)
    (t24 : τ.gpr .x24=b) (t25 : τ.gpr .x25=p) (t26 : τ.gpr .x26=c)
    (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hrs : InRegions (σ.rd++σ.wr) c 8) (hrt : InRegions (τ.rd++τ.wr) c 8)
    (hcs : (σ.mem.readW c 64).toNat=256-L.length)
    (hct : (τ.mem.readW c 64).toNat=256-L.length)
    (hss : Stored σ.mem p L) (hst : Stored τ.mem p L)
    (hm : InputEq σ τ b n) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (segment v n) (fun _ _ => True) := by
  let P (a : State) (s : State) :=
    Only [.x2,.x3,.x4,.x5,.x6,.x9,.x10] a s ∧ Start s b p n L
  have ws : WP isa (.block (setup n)) σ (P σ) := by
    refine WP.mono (setup_ok n hn hL s24 s25 s26 hrs hcs) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem]; exact hss⟩
  have wt : WP isa (.block (setup n)) τ (P τ) := by
    refine WP.mono (setup_ok n hn hL t24 t25 t26 hrt hct) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem]; exact hst⟩
  unfold segment
  apply RelCT.seq (R := fun s t => P σ s ∧ P τ t)
  · have hc : RelCT isa (fun s t => s=σ ∧ t=τ) (.block (setup n)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x26])
        (fun s t h => by
          rcases h with ⟨rfl,rfl⟩
          exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,s26,t26]⟩) checkSetup
    exact (hc.wp (fun s t h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  · intro s t tr ur s' t' hh es et
    have ls := layout_only hs hh.1.1
    have lt := layout_only ht hh.2.1
    have im : InputEq s t b n := by
      intro i hb
      rw [hh.1.1.mem,hh.2.1.mem]
      exact hm i hb
    have sp : s.sp=t.sp := hh.1.1.sp.trans (hsp.trans hh.2.1.sp.symm)
    have wpS := parse_ok v ls hmod hL hh.1.2.1 hh.1.2.2.1 hh.1.2.2.2.1
      hh.1.2.2.2.2.1 hh.1.2.2.2.2.2.1 hh.1.2.2.2.2.2.2
    have wpT := parse_ok v lt hmod hL hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
      hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2
    have pc := (parse_relCT v ls lt hh.1.2 hh.2.2 im sp hmod).wp
      (fun a b h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)
    apply RelCT.seq pc ?_ s t tr ur s' t' ⟨rfl,rfl⟩ es et
    exact RelCT.taint (A := taint) (Taint.ofRegs [.x26])
      (fun a b h => ⟨h.2.1.1.sp.trans (sp.trans h.2.2.1.sp.symm),by
        simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton]
        intro r hr
        subst r
        rw [h.2.1.1.get .x26,h.2.2.1.get .x26,hh.1.1.get .x26,hh.2.1.get .x26,s26,t26]⟩)
      checkNext

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejRowTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem Pub.rowResult {v k off n : Nat} {σ τ : State} (h : Pub v σ τ)
    (hk : k<v) (L : List Zq) : rowResult σ k off n L=rowResult τ k off n L := by
  have hb : streamBytes σ k off (3*n)=streamBytes τ k off (3*n) := by
    unfold streamBytes
    apply List.map_congr_left
    intro i hi
    exact h.byte hk _
  exact congrArg (VG.Proof.MlDsa.Sample.rnFold L) hb

theorem Pub.ptrs {v off k : Nat} {σ τ : State} (h : Pub v σ τ) :
    bufP σ k+BitVec.ofNat 64 off=bufP τ k+BitVec.ofNat 64 off ∧ polyP σ k=polyP τ k ∧
      countP σ k=countP τ k := by
  refine ⟨by rw [h.buf k],h.poly k,?_⟩
  change scr σ+BitVec.ofNat 64 (counts+8*k)=scr τ+BitVec.ofNat 64 (counts+8*k)
  rw [h.2.2.1]

/-- One stream's segment of the loop, in two runs. -/
theorem segAt_relCT {v blocks off n k : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    {hintSetup hintNext : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x26]) (.block (setup n)) hintSetup).isSome=true)
    (checkNext : (taint.check (Taint.ofRegs [.x26]) (.block segmentNext) hintNext).isSome=true) :
    RelCT isa (fun s t => SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)
      (segment variant n)
      (fun s t => SegAt v blocks off n σ σ L (k+1) s ∧ SegAt v blocks off n τ σ L (k+1) t) := by
  have ct : RelCT isa (fun s t => SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)
      (segment variant n) (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hb : off+3*n≤1008 := by have:=h.1.1.blockBound; omega_arith
    have hs := h.1.1
    have ht := h.2.1
    have hks : (doneRows σ off n k L k).length≤256 := hs.length k hk
    have ls := segment_layout hp hs.env hk hb
    have lt := segment_layout hq ht.env hk hb
    rw [segment_input_eq hs.env,segment_output_eq hs.env] at ls
    rw [segment_input_eq ht.env,segment_output_eq ht.env] at lt
    obtain ⟨pb,pp,pc⟩ := pub.ptrs (off := off) (k := k)
    rw [←pb,←pp] at lt
    have crs : InRegions (s.rd++s.wr) (countP σ k) 8 :=
      in_scr_rd hp hs.env.wr (by unfold counts; have:=hp.streams; omega_arith)
    have crt : InRegions (t.rd++t.wr) (countP σ k) 8 := by
      rw [pc]; exact in_scr_rd hq ht.env.wr (by unfold counts; have:=hq.streams; omega_arith)
    have hm : InputEq s t (bufP σ k+BitVec.ofNat 64 off) n := rows_input_eq pub hs ht hk hn
    exact segment_relCT variant n (by omega_arith) checkSetup checkNext hks hmod
      (hs.env.sp.trans (pub.2.2.2.1.trans ht.env.sp.symm))
      h.1.2.1.1 h.1.2.1.2.1 h.1.2.1.2.2
      (h.2.2.1.1.trans pb.symm) (h.2.2.1.2.1.trans pp.symm) (h.2.2.1.2.2.trans pc.symm)
      ls lt crs crt (hs.counts k hk) (by rw [pc]; exact ht.counts k hk)
      (hs.stored k hk) (by rw [pp]; exact ht.stored k hk)
      hm _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  refine (ct.wp (fun s t h => ⟨segAt_step hp (fun _ _ _ => rfl) hk hn hmod variant h.1,
    segAt_step hq (fun j hj M => (pub.rowResult hj M).symm) hk hn hmod variant h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure SegmentChecks (n : Nat) where
  setupHint : VG.Taint.Hint VG.AArch64.Taint.T
  setup : (taint.check (Taint.ofRegs [.x26]) (.block (setup n)) setupHint).isSome=true

structure InitCheck (off count : Nat) where
  hint : VG.Taint.Hint VG.AArch64.Taint.T
  init : (taint.check (Taint.ofRegs []) (.block (segmentsInit off count)) hint).isSome=true

theorem segmentNext_check : ∃ h : VG.Taint.Hint VG.AArch64.Taint.T,
    (taint.check (Taint.ofRegs [.x26]) (.block segmentNext) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem segments_relCT {v blocks off n count : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hv : count=v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : SegmentChecks n) (init : InitCheck off count) :
    RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
      (segments variant off n count)
      (fun s t => Rows v blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows v blocks τ (fun k => rowResult σ k off n (L k)) t) := by
  have hv4 : v≤4 := by have:=hp.streams; omega_arith
  obtain ⟨_,checkNext⟩ := segmentNext_check
  unfold segments
  apply RelCT.seq (R := fun s t => SegAt v blocks off n σ σ L 0 s ∧ SegAt v blocks off n τ σ L 0 t)
  · have hc : RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
        (.block (segmentsInit off count)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun s t h => ⟨h.1.env.sp.trans (pub.2.2.2.1.trans h.2.env.sp.symm),
          by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) init.init
    exact (hc.wp (fun s t h =>
      ⟨segAt_init n hp h.1 hv (by have:=h.1.blockBound; omega_arith),
       segAt_init n hq h.2 hv (by have:=h.1.blockBound; omega_arith)⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  · refine (RelCT.loop (M := isa) (fun m s t => ∃ k, k<v ∧ m=v-k ∧
        SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)
      (fun m => ?_) v).mono (fun s t h => ⟨0,by have:=hp.streams; omega_arith,by omega_arith,h⟩)
      (fun _ _ h => h)
    apply RelCT.exists_
    intro k
    refine RelCT.mono (P := fun s t => k<v ∧ m=v-k ∧
        (SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)) ?_
      (fun _ _ h => h) (fun _ _ h => h)
    intro s t tr ur s' t' ⟨hk,hm,h⟩ es et
    obtain ⟨htr,h1,h2⟩ := segAt_relCT hp hq pub hk hn hmod variant checks.setup checkNext
      s t tr ur s' t' h es et
    refine ⟨htr,?_,?_,?_⟩
    · rw [segAt_eval h1 (by omega_arith) hv4,segAt_eval h2 (by omega_arith) hv4]
    · intro he
      rw [segAt_eval h1 (by omega_arith) hv4] at he
      have hl : k+1=v := by simp at he; omega_arith
      subst hl
      exact ⟨h1.last,h2.last⟩
    · intro he
      rw [segAt_eval h1 (by omega_arith) hv4] at he
      have hl : k+1<v := by simp at he; omega_arith
      exact ⟨v-(k+1),by omega_arith,k+1,hl,rfl,h1,h2⟩

theorem batchFour_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : SegmentChecks n) (init : InitCheck off 4) :
    RelCT isa (fun s t => Rows 4 blocks σ L s ∧ Rows 4 blocks τ L t)
      (Four.batch variant off n)
      (fun s t => Rows 4 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 4 blocks τ (fun k => rowResult σ k off n (L k)) t) :=
  segments_relCT hp hq pub rfl hn hmod variant checks init

theorem batchTwo_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : SegmentChecks n) (init : InitCheck off 2) :
    RelCT isa (fun s t => Rows 2 blocks σ L s ∧ Rows 2 blocks τ L t)
      (Two.batch variant off n)
      (fun s t => Rows 2 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 2 blocks τ (fun k => rowResult σ k off n (L k)) t) :=
  segments_relCT hp hq pub rfl hn hmod variant checks init

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

end

/-! ## From `ResidentRejContract.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

/-- The resident implementation retains the established bounded sampler result. -/
theorem prefixRow_legacy (σ : State) (k : Nat) :
    prefixRow σ k 1008=VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k := by
  unfold prefixRow
  rw [streamBytes_full]

theorem result_legacy {σ t : State} (h : Result 4 σ t) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.post σ t := by
  constructor
  · rw [h.status]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.mask
    have he : ((List.range 4).all fun k =>
        (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length==256)=true ↔
        ∀k<4,(prefixRow σ k 1008).length=256 := by
      simp only [List.all_eq_true,List.mem_range,beq_iff_eq,prefixRow_legacy]
    by_cases hall : ∀k<4,(prefixRow σ k 1008).length=256
    · rw [ite_eq_left hall,ite_eq_left (he.mpr hall)]
      rfl
    · rw [ite_eq_right hall,ite_eq_right (fun hh => hall (he.mp hh))]
      rfl
  · intro k hk hl
    exact stored_polyIs (by simpa only [prefixRow_legacy,polyP,VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP] using h.stored k hk) hl

theorem pre_four {σ : State} (h : (Proof.MlDsa.rejNTT4Contract AArch64.abi).pre σ) : Pre 4 σ := by
  obtain ⟨hr,hw,hsa,hss,has⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.r4_pre σ h
  exact ⟨Or.inr rfl,hr,hw,hsa,hss,has⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTwoContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

def twoPreProps (s : State) : Prop := s.rd=[seedsR 2 s] ∧ s.wr=[aR 2 s,scrR s] ∧
  (seedsR 2 s).Disjoint (aR 2 s) ∧ (seedsR 2 s).Disjoint (scrR s) ∧
  (aR 2 s).Disjoint (scrR s)

theorem pre_two {σ : State} (h : (Proof.MlDsa.rejNTT2Contract AArch64.abi).pre σ) : Pre 2 σ := by
  have hp : ∀s,(Proof.MlDsa.rejNTT2Contract AArch64.abi).pre s → twoPreProps s := by
    sig_implies_pre [Proof.MlDsa.rejNTT2Contract,Proof.MlDsa.rejNTT2Sig,twoPreProps,
      seedsR,aR,scrR,seedP,aP,scr,AArch64.abi,AArch64.argRegs,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP,VG.Proof.MlDsa.AArch64.Sample.Rej4.aP,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.scr,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR]
  obtain ⟨hr,hw,hsa,hss,has⟩ := hp σ h
  exact ⟨Or.inl rfl,hr,hw,hsa,hss,has⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejInitialTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev Absorbed (v : Nat) (σ s : State) := Env v σ s ∧
  (∀p,2*p+1<v → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) ∧
  ∀k<v,s.mem.readW (countP σ k) 64=256

private theorem initial_relCT {v : Nat} {σ τ : State} {P Q : State → Prop} {c : Prog isa}
    (pub : Pub v σ τ) (hc : PointerCT [.x0,.x1,.x2] c)
    (ws : WP isa c σ P) (wt : WP isa c τ Q) :
    RelCT isa (fun s t => s=σ ∧ t=τ) c (fun s t => P s ∧ Q t) := by
  have ct : RelCT isa (fun s t => s=σ ∧ t=τ) c (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    rcases h with ⟨rfl,rfl⟩
    have ha : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2]) s t := by
      refine ⟨pub.2.2.2.1,?_⟩
      simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false]
      intro r hr
      rcases hr with rfl | rfl | rfl
      · exact pub.1
      · exact pub.2.1
      · exact pub.2.2.1
    exact ⟨hc _ _ _ _ _ _ True.intro True.intro ha es et,True.intro⟩
  exact (ct.wp (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem startFour_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block (Impl.MlDsa.AArch64.Sample.Rej4.init++Four.initCounts))
      (fun s t => Absorbed 4 σ s ∧ Absorbed 4 τ t) :=
  initial_relCT pub startFour_ct (startFour_ok hp) (startFour_ok hq)

theorem startTwo_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block (Impl.MlDsa.AArch64.Sample.Rej4.pro++Impl.MlDsa.AArch64.Sample.Rej4.zeroStates++
        Impl.MlDsa.AArch64.Sample.Rej4.absorbPair 0++Two.initCounts))
      (fun s t => Absorbed 2 σ s ∧ Absorbed 2 τ t) :=
  initial_relCT pub startTwo_ct (startTwo_ok hp) (startTwo_ok hq)

theorem firstFour_left_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => Absorbed 4 σ s ∧ Absorbed 4 τ t)
      (.seq (.seq (.block (Four.squeezeSetup 0 5)) (five .x22 .x24 .x25)) (five .x23 .x26 .x27))
      (fun s t => FirstBlocks 4 σ s ∧ FirstBlocks 4 τ t) :=
  env_relCT pub (fun _ h => h.1) (fun _ h => h.1)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ _ _ h => h) (by taint_decide))
    (fun _ h => WP.assoc' (firstFour_setup_ok hp h.1 h.2.1 h.2.2))
    (fun _ h => WP.assoc' (firstFour_setup_ok hq h.1 h.2.1 h.2.2))

theorem firstTwo_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => Absorbed 2 σ s ∧ Absorbed 2 τ t)
      (.seq (.block (Two.squeezeSetup 0 5)) (five .x22 .x24 .x25))
      (fun s t => FirstBlocks 2 σ s ∧ FirstBlocks 2 τ t) :=
  env_relCT pub (fun _ h => h.1) (fun _ h => h.1) firstTwo_ct
    (fun _ h => firstTwo_setup_ok hp h.1 h.2.1 h.2.2)
    (fun _ h => firstTwo_setup_ok hq h.1 h.2.1 h.2.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejChecks.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

def firstChecks : SegmentChecks 168 := by apply SegmentChecks.mk; taint_decide
def secondChecks : SegmentChecks 112 := by apply SegmentChecks.mk; taint_decide
def lastChecks : SegmentChecks 56 := by apply SegmentChecks.mk; taint_decide

def firstInit4 : InitCheck 0 4 := by apply InitCheck.mk; taint_decide
def secondInit4 : InitCheck 504 4 := by apply InitCheck.mk; taint_decide
def lastInit4 : InitCheck 840 4 := by apply InitCheck.mk; taint_decide
def firstInit2 : InitCheck 0 2 := by apply InitCheck.mk; taint_decide
def secondInit2 : InitCheck 504 2 := by apply InitCheck.mk; taint_decide
def lastInit2 : InitCheck 840 2 := by apply InitCheck.mk; taint_decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejPrefixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev PrefixPair (v blocks n : Nat) (σ τ s t : State) :=
  Rows v blocks σ (fun k => prefixRow σ k n) s ∧
  Rows v blocks τ (fun k => prefixRow τ k n) t

theorem prefixFour_relCT {blocks off n : Nat} {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (ho : off%3=0)
    (checks : SegmentChecks n) (init : InitCheck off 4) :
    RelCT isa (PrefixPair 4 blocks off σ τ) (Four.batch 0 off n)
      (PrefixPair 4 blocks (off+3*n) σ τ) := by
  refine (batchFour_relCT (L := fun k => prefixRow σ k off) hp hq pub hn hmod 0 checks init).mono ?_ ?_
  · intro s t h
    exact ⟨h.1,h.2.congr (fun k hk => (pub.prefix hk off).symm)⟩
  · intro s t h
    exact ⟨h.1.congr (fun k _ => rowResult_prefix σ k off n ho),
      h.2.congr (fun k hk => (rowResult_prefix σ k off n ho).trans (pub.prefix hk _))⟩

theorem prefixTwo_relCT {blocks off n : Nat} {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (ho : off%3=0)
    (checks : SegmentChecks n) (init : InitCheck off 2) :
    RelCT isa (PrefixPair 2 blocks off σ τ) (Two.batch 0 off n)
      (PrefixPair 2 blocks (off+3*n) σ τ) := by
  refine (batchTwo_relCT (L := fun k => prefixRow σ k off) hp hq pub hn hmod 0 checks init).mono ?_ ?_
  · intro s t h
    exact ⟨h.1,h.2.congr (fun k hk => (pub.prefix hk off).symm)⟩
  · intro s t h
    exact ⟨h.1.congr (fun k _ => rowResult_prefix σ k off n ho),
      h.2.congr (fun k hk => (rowResult_prefix σ k off n ho).trans (pub.prefix hk _))⟩

theorem parseFiveFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => FirstBlocks 4 σ s ∧ FirstBlocks 4 τ t)
      (.seq (Four.batch 0 0 168) (Four.batch 0 504 112))
      (PrefixPair 4 5 840 σ τ) := by
  apply RelCT.seq (R := PrefixPair 4 5 504 σ τ)
  · exact (prefixFour_relCT hp hq pub (by decide : 0+3*168≤168*5)
      (by decide) (by decide) firstChecks firstInit4).mono
      (fun _ _ h => ⟨h.1.rows,h.2.rows⟩) (fun _ _ h => h)
  · exact prefixFour_relCT hp hq pub (by decide : 504+3*112≤168*5)
      (by decide) (by decide) secondChecks secondInit4

theorem parseFiveTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => FirstBlocks 2 σ s ∧ FirstBlocks 2 τ t)
      (.seq (Two.batch 0 0 168) (Two.batch 0 504 112))
      (PrefixPair 2 5 840 σ τ) := by
  apply RelCT.seq (R := PrefixPair 2 5 504 σ τ)
  · exact (prefixTwo_relCT hp hq pub (by decide : 0+3*168≤168*5)
      (by decide) (by decide) firstChecks firstInit2).mono
      (fun _ _ h => ⟨h.1.rows,h.2.rows⟩) (fun _ _ h => h)
  · exact prefixTwo_relCT hp hq pub (by decide : 504+3*112≤168*5)
      (by decide) (by decide) secondChecks secondInit2

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejAdaptiveTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev Flagged (v blocks n : Nat) (σ s : State) :=
  Rows v blocks σ (fun k => prefixRow σ k n) s ∧
  Flags v (fun k => prefixRow σ k n) s

theorem flags_zero_eq {v n : Nat} {σ τ s t : State} (pub : Pub v σ τ)
    (hs : Flags v (fun k => prefixRow σ k n) s)
    (ht : Flags v (fun k => prefixRow τ k n) t) :
    (s.gpr .x27==0#64)=(t.gpr .x27==0#64) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,hs.zero,ht.zero]
  constructor
  · intro h k hk; rw [←pub.prefix hk n]; exact h k hk
  · intro h k hk; rw [pub.prefix hk n]; exact h k hk

theorem flagsFour_relCT {blocks n : Nat} {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (PrefixPair 4 blocks n σ τ) (.block Four.flags)
      (fun s t => Flagged 4 blocks n σ s ∧ Flagged 4 blocks n τ t) :=
  env_relCT pub (fun _ h => h.env) (fun _ h => h.env) flagsFour_ct
    (fun _ h => flagsSemantic_ok hp h) (fun _ h => flagsSemantic_ok hq h)

theorem adaptiveFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => Flagged 4 5 840 σ s ∧ Flagged 4 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Four.squeezeN step 840 1)
          (.seq (Four.batch 0 840 56) (.block Four.flags))))
      (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t) := by
  have ct : RelCT isa (fun s t => Flagged 4 5 840 σ s ∧ Flagged 4 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Four.squeezeN step 840 1)
          (.seq (Four.batch 0 840 56) (.block Four.flags))))
      (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      rw [eval_zero,eval_zero]
      exact congrArg some (flags_zero_eq pub h.1.2 h.2.2)
    · exact RelCT.block_nil (fun _ _ _ => True.intro)
    · apply RelCT.seq (R := PrefixPair 4 6 840 σ τ)
      · exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) sixthFour_ct
          (fun _ h => sixthFour_ok hp h) (fun _ h => sixthFour_ok hq h)).mono
          (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)
      · apply RelCT.seq (prefixFour_relCT hp hq pub (by decide : 840+3*56≤168*6)
          (by decide) (by decide) lastChecks lastInit4)
        exact (flagsFour_relCT hp hq pub).mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  exact (ct.wp (fun _ _ h => ⟨adaptiveFour_timingDone hp h.1.1 h.1.2,
    adaptiveFour_timingDone hq h.2.1 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem flagsTwo_relCT {blocks n : Nat} {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (PrefixPair 2 blocks n σ τ) (.block Two.flags)
      (fun s t => Flagged 2 blocks n σ s ∧ Flagged 2 blocks n τ t) :=
  env_relCT pub (fun _ h => h.env) (fun _ h => h.env) flagsTwo_ct
    (fun _ h => flagsSemantic_ok hp h) (fun _ h => flagsSemantic_ok hq h)

theorem adaptiveTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => Flagged 2 5 840 σ s ∧ Flagged 2 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Two.squeezeN Two.step 840 1)
          (.seq (Two.batch 0 840 56) (.block Two.flags))))
      (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t) := by
  have ct : RelCT isa (fun s t => Flagged 2 5 840 σ s ∧ Flagged 2 5 840 τ t)
      (.ite (.zero .x .x27) (.block [])
        (.seq (Two.squeezeN Two.step 840 1)
          (.seq (Two.batch 0 840 56) (.block Two.flags))))
      (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      rw [eval_zero,eval_zero]
      exact congrArg some (flags_zero_eq pub h.1.2 h.2.2)
    · exact RelCT.block_nil (fun _ _ _ => True.intro)
    · apply RelCT.seq (R := PrefixPair 2 6 840 σ τ)
      · exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) sixthTwo_ct
          (fun _ h => sixthTwo_ok hp h) (fun _ h => sixthTwo_ok hq h)).mono
          (fun _ _ h => ⟨h.1.1.1,h.1.2.1⟩) (fun _ _ h => h)
      · apply RelCT.seq (prefixTwo_relCT hp hq pub (by decide : 840+3*56≤168*6)
          (by decide) (by decide) lastChecks lastInit2)
        exact (flagsTwo_relCT hp hq pub).mono (fun _ _ h => h) (fun _ _ _ => True.intro)
  exact (ct.wp (fun _ _ h => ⟨adaptiveTwo_timingDone hp h.1.1 h.1.2,
    adaptiveTwo_timingDone hq h.2.1 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejCleanupTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem failure_ready {v : Nat} {σ τ s t : State} (pub : Pub v σ τ)
    (hs : TimingDone v σ s) (ht : TimingDone v τ t)
    (hz : s.gpr .x27≠0#64) : TailReady v σ s ∧ TailReady v τ t := by
  have hn : t.gpr .x27≠0#64 := by
    intro he
    apply hz
    apply hs.done.flags.zero.mpr
    intro k hk
    rw [pub.prefix hk 1008]
    exact ht.done.flags.zero.mp he k hk
  exact ⟨⟨hs.done,hs.bytes hz⟩,⟨ht.done,ht.bytes hn⟩⟩

private theorem finish_ct : PointerCT [.x19]
    (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem cleanupFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t) Four.tailZeros
      (fun s t => Done 4 σ s ∧ Done 4 τ t) := by
  unfold Four.tailZeros
  apply RelCT.ite
  · intro s t h
    rw [eval_zero,eval_zero]
    exact congrArg some (flags_zero_eq pub h.1.done.flags h.2.done.flags)
  · exact RelCT.block_nil (fun _ _ h => ⟨h.1.1.done,h.1.2.done⟩)
  · refine (tailRows_relCT hp hq pub (List.range 4) (by
      simpa only [List.mem_range] using fun k hk => hk)).mono ?_ (fun _ _ h => ⟨h.1.1,h.2.1⟩)
    intro s t h
    apply failure_ready pub h.1.1 h.1.2
    intro hz
    have he := h.2
    rw [eval_zero,hz] at he
    simp at he

theorem cleanupFinishFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => TimingDone 4 σ s ∧ TimingDone 4 τ t)
      (.seq Four.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) (fun _ _ => True) := by
  apply RelCT.seq (cleanupFour_relCT hp hq pub)
  exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) finish_ct
    (fun _ h => finish_ok hp h) (fun _ h => finish_ok hq h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

theorem cleanupTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t) Two.tailZeros
      (fun s t => Done 2 σ s ∧ Done 2 τ t) := by
  unfold Two.tailZeros
  apply RelCT.ite
  · intro s t h
    rw [eval_zero,eval_zero]
    exact congrArg some (flags_zero_eq pub h.1.done.flags h.2.done.flags)
  · exact RelCT.block_nil (fun _ _ h => ⟨h.1.1.done,h.1.2.done⟩)
  · refine (tailRows_relCT hp hq pub (List.range 2) (by
      simpa only [List.mem_range] using fun k hk => hk)).mono ?_ (fun _ _ h => ⟨h.1.1,h.2.1⟩)
    intro s t h
    apply failure_ready pub h.1.1 h.1.2
    intro hz
    have he := h.2
    rw [eval_zero,hz] at he
    simp at he

theorem cleanupFinishTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => TimingDone 2 σ s ∧ TimingDone 2 τ t)
      (.seq Two.tailZeros
        (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
          Impl.MlDsa.AArch64.Sample.Rej4.epi))) (fun _ _ => True) := by
  apply RelCT.seq (cleanupTwo_relCT hp hq pub)
  exact (env_relCT pub (fun _ h => h.env) (fun _ h => h.env) finish_ct
    (fun _ h => finish_ok hp h) (fun _ h => finish_ok hq h)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- The exact four-stream implementation leaks only public pointers and the
seed bytes already declared by the shared matrix-sampling contract. -/
theorem four_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ) Four.code (fun _ _ => True) := by
  unfold Four.code
  apply RelCT.seq (startFour_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.seq (firstFour_left_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (parseFiveFour_relCT hp hq pub)
  apply RelCT.seq (flagsFour_relCT hp hq pub)
  apply RelCT.seq (adaptiveFour_relCT hp hq pub)
  exact cleanupFinishFour_relCT hp hq pub

/-- The two-stream implementation has the same seed-dependent leakage policy
with its precisely sized two-seed and two-polynomial memory footprint. -/
theorem two_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ) Two.code (fun _ _ => True) := by
  unfold Two.code
  apply RelCT.seq (startTwo_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (firstTwo_relCT hp hq pub)
  apply RelCT.assoc
  apply RelCT.seq (parseFiveTwo_relCT hp hq pub)
  apply RelCT.seq (flagsTwo_relCT hp hq pub)
  apply RelCT.seq (adaptiveTwo_relCT hp hq pub)
  exact cleanupFinishTwo_relCT hp hq pub

theorem four_ct : ConstantTime isa (Pre 4) (Pub 4) Four.code := by
  intro s t tr ur s' t' hp hq pub es et
  exact (four_relCT hp hq pub _ _ _ _ _ _ ⟨rfl,rfl⟩ es et).1

theorem two_ct : ConstantTime isa (Pre 2) (Pub 2) Two.code := by
  intro s t tr ur s' t' hp hq pub es et
  exact (two_relCT hp hq pub _ _ _ _ _ _ ⟨rfl,rfl⟩ es et).1

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem four_verified : Verified target Four.code (Proof.MlDsa.rejNTT4Contract abi) := by
  refine ⟨?_,?_,(VG.Proof.MlDsa.AArch64.Sample.Rej4.verified true).2.2⟩
  · intro s hs
    obtain ⟨tr,t,he,ht⟩ := four_ok (pre_four hs)
    refine ⟨tr,t,he,ht.abi,?_⟩
    sig_post [Proof.MlDsa.rejNTT4Contract,Proof.MlDsa.rejNTT4Sig,abi,argRegs]
    exact ht.outcome
  · intro s t tr ur s' t' hs ht hp es et
    have pub : Pub 4 s t := by
      sig_pub [Proof.MlDsa.rejNTT4Contract,Proof.MlDsa.rejNTT4Sig,abi,argRegs] at hp
      obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
      exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
    exact four_ct _ _ _ _ _ _ (pre_four hs) (pre_four ht) pub es et

 def twoSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,68⟩]
  wr := [⟨0x2000,2048⟩,⟨0x4000,8192⟩]

 theorem two_verified : Verified target Two.code (Proof.MlDsa.rejNTT2Contract abi) := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨tr,t,he,ht⟩ := two_ok (pre_two hs)
    refine ⟨tr,t,he,ht.abi,?_⟩
    sig_post [Proof.MlDsa.rejNTT2Contract,Proof.MlDsa.rejNTT2Sig,abi,argRegs]
    exact ht.outcome
  · intro s t tr ur s' t' hs ht hp es et
    have pub : Pub 2 s t := by
      sig_pub [Proof.MlDsa.rejNTT2Contract,Proof.MlDsa.rejNTT2Sig,abi,argRegs] at hp
      obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
      exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
    exact two_ct _ _ _ _ _ _ (pre_two hs) (pre_two ht) pub es et
  · sig_implies_sat [Proof.MlDsa.rejNTT2Contract,Proof.MlDsa.rejNTT2Sig,abi,argRegs]
      [twoSat] using twoSat

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
