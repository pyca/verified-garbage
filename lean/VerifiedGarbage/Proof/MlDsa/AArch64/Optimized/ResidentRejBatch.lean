module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlKem.Arith

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej (segments segmentsInit)

theorem Rows.congr {v blocks : Nat} {σ s : State} {L R : Nat → List Zq}
    (h : Rows v blocks σ L s) (hr : ∀k<v,L k=R k) : Rows v blocks σ R s := by
  refine ⟨h.env,h.blockBound,h.pairs,h.bytes,?_,?_,?_⟩
  · intro k hk; rw [←hr k hk]; exact h.length k hk
  · intro k hk; rw [←hr k hk]; exact h.counts k hk
  · intro k hk; rw [←hr k hk]; exact h.stored k hk

/-- Writing registers other than the environment's keeps the rows. -/
theorem Rows.only {v blocks : Nat} {σ s t : State} {L : Nat → List Zq} {rs : List Reg}
    (h : Rows v blocks σ L s) (ht : Only rs s t)
    (hg : ∀r∈[Reg.x19,.x20,.x21,.x30],r∉rs) : Rows v blocks σ L t := by
  have hf : Frame [] s.mem t.mem := by rw [ht.mem]; exact Frame.refl _ _
  refine ⟨h.env.frameStep hf (by simp) (by simp) ht.rd ht.wr ht.sp
      (fun r hr => ht.gpr r (hg r hr)),h.blockBound,?_,?_,h.length,?_,?_⟩
  · intro p hp; rw [ht.mem]; exact h.pairs p hp
  · intro k hk j hj; rw [ht.mem]; exact h.bytes k hk j hj
  · intro k hk; rw [ht.mem]; exact h.counts k hk
  · intro k hk; rw [ht.mem]; exact h.stored k hk

/-- The rows after the first `k` streams' segments. -/
def doneRows (σ : State) (off n k : Nat) (L : Nat → List Zq) : Nat → List Zq :=
  fun j => if j<k then rowResult σ j off n (L j) else L j

private theorem ofNat_bne_zero {k : Nat} (h : k<2^64) :
    (BitVec.ofNat 64 k != 0)=decide (k≠0) := by
  by_cases hk : k=0
  · subst hk; rfl
  · have : BitVec.ofNat 64 k≠0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    rw [show (BitVec.ofNat 64 k != 0)=true from bne_iff_ne.mpr this]
    simp [hk]

/-- The segment loop before stream `k`'s segment: the rows of the streams
below `k` are parsed (with the results of `ρ`'s run), the pointers are at
stream `k`, and x27 counts the streams left. -/
def SegAt (v blocks off n : Nat) (σ ρ : State) (L : Nat → List Zq) (k : Nat) (t : State) : Prop :=
  Rows v blocks σ (doneRows ρ off n k L) t ∧ Ptrs σ off k t ∧ t.gpr .x27=BitVec.ofNat 64 (v-k)

theorem segAt_init {v blocks off count : Nat} {σ ρ s : State} {L : Nat → List Zq}
    (n : Nat) (hp : Pre v σ) (h : Rows v blocks σ L s) (hv : count=v) (ho : off≤1008) :
    WP isa (.block (segmentsInit off count)) s (SegAt v blocks off n σ ρ L 0) := by
  have hv4 : v≤4 := by have:=hp.streams; omega
  unfold segmentsInit
  refine wp_addImm (by omega) fun a ha ea => wp_mov fun b hb' eb =>
    wp_addImm (by decide) fun c hc ec => wp_addImm (by decide) fun d hd ed =>
    wp_movz fun e he ee => wp_nil ?_
  have hO : Only [.x24,.x25,.x26,.x27] s e :=
    ((((ha.trans hb').trans hc).trans hd).trans he).mono (by decide)
  have h19 : s.gpr .x19=scr σ := h.env.x19
  have h21 : s.gpr .x21=aP σ := h.env.x21
  refine ⟨(h.only hO (by decide)).congr fun j _ => ?_,⟨?_,?_,?_⟩,?_⟩
  · simp [doneRows]
  · rw [he.get .x24,hd.get .x24,hc.get .x24,hb'.get .x24,ea,h19]
    change scr σ+BitVec.ofNat 64 (840+off)=(scr σ+BitVec.ofNat 64 (840+1008*0))+BitVec.ofNat 64 off
    rw [Offset.add_add]
  · rw [he.get .x25,hd.get .x25,hc.get .x25,eb,ha.get .x21,h21]
    exact (BitVec.add_zero _).symm
  · rw [he.get .x26,ed,ec,hb'.get .x19,ha.get .x19,h19,Offset.add_add]
    change _=scr σ+BitVec.ofNat 64 (Impl.MlDsa.AArch64.Optimized.ResidentRej.counts+8*0)
    exact congrArg (fun d => scr σ+BitVec.ofNat 64 d)
      (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)
  · rw [ee]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.natCast_eq_ofNat,BitVec.toNat_ofNat]
    omega

/-- One stream's segment, with `ρ`'s results equal to `σ`'s. -/
theorem segAt_step {v blocks off n k : Nat} {σ ρ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hr : ∀j<v,∀M,rowResult σ j off n M=rowResult ρ j off n M) (hk : k<v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (h : SegAt v blocks off n σ ρ L k s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.segment variant n) s
      (SegAt v blocks off n σ ρ L (k+1)) := by
  refine WP.mono (rowStep_ok hp h.1 hk h.2.1 hn hmod variant) fun t ⟨ht,hptr,h27⟩ => ?_
  refine ⟨ht.congr fun j _ => ?_,hptr,?_⟩
  · unfold updateRow doneRows
    by_cases hj : j=k
    · subst hj; simp [hr j hk]
    · by_cases hjk : j<k
      · simp [hj,hjk,show j<k+1 by omega]
      · simp [hj,hjk,show ¬j<k+1 by omega]
  · rw [h27,h.2.2,show v-k=(v-(k+1))+1 by omega,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

theorem segAt_eval {v blocks off n k : Nat} {σ ρ s : State} {L : Nat → List Zq}
    (h : SegAt v blocks off n σ ρ L k s) (hk : k≤v) (hv : v≤4) :
    isa.eval (.nonzero .x .x27) s=some (decide (v-k≠0)) := by
  show some (s.read .x .x27 != 0)=_
  have hrd : s.read .x .x27=s.gpr .x27 := rfl
  rw [hrd,h.2.2,ofNat_bne_zero (by omega)]

theorem SegAt.last {v blocks off n : Nat} {σ ρ s : State} {L : Nat → List Zq}
    (h : SegAt v blocks off n σ ρ L v s) :
    Rows v blocks σ (fun k => rowResult ρ k off n (L k)) s :=
  h.1.congr fun j hj => by simp [doneRows,hj]

/-- The segment loop parses the same range of each of the first `count`
streams' buffers. -/
theorem segments_ok {v blocks off n count : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : Rows v blocks σ L s) (hv : count=v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat) :
    WP isa (segments variant off n count) s
      (Rows v blocks σ (fun k => rowResult σ k off n (L k))) := by
  have hv4 : v≤4 := by have:=hp.streams; omega
  have hb := h.blockBound
  unfold segments
  refine WP.seq (WP.mono (segAt_init (ρ := σ) n hp h hv (by omega)) fun e he => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ k, k<v ∧ m=v-k ∧ SegAt v blocks off n σ σ L k t)
    (fun m t ⟨k,hk,hm,ht⟩ => ?_) v e ⟨0,by have:=hp.streams; omega,by omega,he⟩
  subst hm
  refine WP.mono (segAt_step hp (fun _ _ _ => rfl) hk hn hmod variant ht) fun t' ht' => ?_
  rw [segAt_eval ht' (by omega) hv4]
  by_cases hl : k+1=v
  · left
    subst hl
    exact ⟨by simp,ht'.last⟩
  · right
    exact ⟨by simp; omega,v-(k+1),by omega,k+1,by omega,rfl,ht'⟩

theorem batchFour_ok {blocks off n : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 blocks σ L s)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch variant off n) s
      (Rows 4 blocks σ (fun k => rowResult σ k off n (L k))) :=
  segments_ok hp h rfl hn hmod variant

theorem batchTwo_ok {blocks off n : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 blocks σ L s)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch variant off n) s
      (Rows 2 blocks σ (fun k => rowResult σ k off n (L k))) :=
  segments_ok hp h rfl hn hmod variant

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
