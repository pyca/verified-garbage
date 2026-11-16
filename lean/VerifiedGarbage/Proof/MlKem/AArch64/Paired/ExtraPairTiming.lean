module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBoth
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output

/-! ### `MlKem.AArch64.Paired.ResumeTiming`, which only this module used -/

section

/-! ### `MlKem.AArch64.Paired.ZeroTiming`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ZeroReadyW (w16 : Bool) (L : List Zq) (slot : Nat) (aP : Addr) (s : State) : Prop where
  len : L.length≤256
  coeffs : Rej8.Scalar.CoeffsW w16 s.mem aP L
  saved : checkpointW w16 (s.gpr .x19+BitVec.ofNat 64 slot) aP L s.mem
  read0 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 slot) 8
  read1 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8
  writable : ∀i<256,InRegions s.wr (cAddr w16 aP i) 4

theorem zeroExtra_relCT {w16 : Bool} {s u : State} {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    {L : List Zq} {aP : Addr} (ps : ZeroReadyW w16 L slot aP s) (pu : ZeroReadyW w16 L slot aP u)
    (hsp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) :
    RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.zeroExtra slot w16)
      (fun a b=>s.sp=a.sp ∧ u.sp=b.sp) := by
  have start : RelCT isa (fun a b=>a=s ∧ b=u)
      (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)])
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha',hb'⟩
    subst a; subst b
    obtain ⟨ka,_,a3,a4⟩ := exec_post (load_checkpoint s ho ha ps.read0 ps.read1) ea
    obtain ⟨kb,_,b3,b4⟩ := exec_post (load_checkpoint u ho ha pu.read0 pu.read1) eb
    refine ⟨loadCheckpoint_ct slot s u tr ur a' b' trivial trivial
      (agree_of hsp (by intro r hr; rw [List.mem_singleton.mp hr]; exact h19)) ea eb,
      agree_of (ka.sp.trans (hsp.trans kb.sp.symm)) ?_⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (a3.trans ps.saved.1).trans (b3.trans pu.saved.1).symm
    · apply BitVec.eq_of_toNat_eq
      rw [a4,b4]
      have es : s.gpr .x19+BitVec.ofNat 64 (slot+8)=s.gpr .x19+BitVec.ofNat 64 slot+8 := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
      have eu : u.gpr .x19+BitVec.ofNat 64 (slot+8)=u.gpr .x19+BitVec.ofNat 64 slot+8 := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
      rw [es,eu,ps.saved.2,pu.saved.2]
  have trace : RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.zeroExtra slot w16)
      (fun _ _=>True) := by
    refine RelCT.seq start ?_
    intro a b tr ur a' b' h ea eb
    exact ⟨zeroSuffix_ct w16 a b tr ur a' b' trivial trivial h ea eb,trivial⟩
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha',hb'⟩
  subst a; subst b
  have hs := exec_post (zeroExtra_ok s ho ha ps.len ps.coeffs ps.saved ps.read0 ps.read1 ps.writable) ea
  have hu := exec_post (zeroExtra_ok u ho ha pu.len pu.coeffs pu.saved pu.read0 pu.read1 pu.writable) eb
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,hs.1.sp.symm,hu.1.sp.symm⟩

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! # Fourth/fifth-block continuation branches only on the public matrix streams -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ZeroBothTiming.lean`, which only this module imported.
section

/-! # The paired failure cleanup depends only on the public accepted lengths -/
section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem ZeroReadyW.frame {w16 : Bool} {s u : State} {L : List Zq} {p : Addr} {slot : Nat} {rs : List Region}
    (h : ZeroReadyW w16 L slot p s) (hr : u.rd=s.rd) (hw : u.wr=s.wr) (hx : u.gpr .x19=s.gpr .x19)
    (hf : Frame rs s.mem u.mem) (hd : ∀r∈rs,(polyRegion p).Disjoint r)
    (hc : ∀r∈rs,(Region.mk (s.gpr .x19+BitVec.ofNat 64 slot) 16).Disjoint r) : ZeroReadyW w16 L slot p u := by
  refine ⟨h.len,coeffs_frame h.coeffs h.len hf hd,?_,?_,?_,?_⟩
  · rw [hx]; exact checkpoint_frame h.saved hf hc
  · simpa only [hr,hw,hx] using h.read0
  · simpa only [hr,hw,hx] using h.read1
  · simpa only [hw] using h.writable

theorem zeroBoth_relCT {w16 : Bool} {s u : State} {a b : Addr} {L M : List Zq}
    (sa : ZeroReadyW w16 L 1680 a s) (sb : ZeroReadyW w16 M 1696 b s)
    (ua : ZeroReadyW w16 L 1680 a u) (ub : ZeroReadyW w16 M 1696 b u)
    (hab : (polyRegion a).Disjoint (polyRegion b))
    (hcp : (Region.mk (s.gpr .x19+1696) 16).Disjoint (polyRegion a))
    (hsp : s.sp=u.sp) (hx : s.gpr .x19=u.gpr .x19) :
    RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (Impl.MlKem.AArch64.Paired.zeroExtra 1680 w16) (Impl.MlKem.AArch64.Paired.zeroExtra 1696 w16))
      (fun _ _=>True) := by
  let R := fun t v : State=>ZeroReadyW w16 M 1696 b t ∧ ZeroReadyW w16 M 1696 b v ∧
    t.sp=v.sp ∧ t.gpr .x19=v.gpr .x19
  refine RelCT.seq (R:=R) ?_ ?_
  · intro t v tr ur t' v' h et ev
    rcases h with ⟨ht0,hv0⟩
    subst t; subst v
    have ht := exec_post (zeroExtra_ok s (by decide) (by decide) sa.len sa.coeffs sa.saved sa.read0 sa.read1 sa.writable) et
    have hu := exec_post (zeroExtra_ok u (by decide) (by decide) ua.len ua.coeffs ua.saved ua.read0 ua.read1 ua.writable) ev
    refine ⟨(zeroExtra_relCT (by decide) (by decide) sa ua hsp hx s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
      sb.frame ht.1.rd ht.1.wr (ht.1.get .x19) ht.2.1 ?_ ?_,
      ub.frame hu.1.rd hu.1.wr (hu.1.get .x19) hu.2.1 ?_ ?_,
      ht.1.sp.trans (hsp.trans hu.1.sp.symm),?_⟩
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hab.symm
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hcp
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hab.symm
    · intro r hr; rw [List.mem_singleton.mp hr,←hx]; exact hcp
    · rw [ht.1.get .x19,hu.1.get .x19,hx]
  · intro t v tr ur t' v' h et ev
    exact ⟨(zeroExtra_relCT (by decide) (by decide) h.1 h.2.1 h.2.2.1 h.2.2.2
      t v tr ur t' v' ⟨rfl,rfl⟩ et ev).1,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def StepTimingW (sha3 : Bool) (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) : Prop :=
  ∀{s u : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c s → ProgressW w16 A B n p a b c u →
    s.syms "VG_MLKEM_REJ_SHUFFLE"=c → u.syms "VG_MLKEM_REJ_SHUFFLE"=c → s.sp=u.sp →
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraStep sha3 w16) (fun _ _=>True)

theorem retryInit_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.movz .x .x30 1 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem retryCond_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.sub .x .x7 .x6 .x30,.lsr .x .x7 .x7 63,.movz .x .x30 0 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

/-- An iteration of `Paired.retry` from the same count in both runs. -/
theorem retryBody_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u t v : State} {n : Nat}
    (step : StepTimingW sha3 w16 A B p a b c) (it : RetryInv w16 A B p a b c s n t)
    (iv : RetryInv w16 A B p a b c u n v) (sp : t.sp=v.sp) :
    RelCT isa (fun t' v'=>t'=t ∧ v'=v) (.seq (Impl.MlKem.AArch64.Paired.extraStep sha3 w16)
      (.block [.sub .x .x7 .x6 .x30,.lsr .x .x7 .x7 63,.movz .x .x30 0 0])) (fun _ _=>True) := by
  refine RelCT.seq (R:=fun t' v' : State=>t'.sp=v'.sp) ?_ ?_
  · intro t₀ v₀ tr ur t' v' h et ev
    rcases h with ⟨rfl,rfl⟩
    have n34 : 4-n=3 ∨ 4-n=4 := by have := it.le; omega_using [this]
    exact ⟨(step n34 it.progress iv.progress it.syms iv.syms sp t₀ v₀ tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
      (exec_post (advance_ok (sha3 := sha3) it.progress it.syms) et).keep.sp.trans
        (sp.trans (exec_post (advance_ok (sha3 := sha3) iv.progress iv.syms) ev).keep.sp.symm)⟩
  · intro t₀ v₀ tr ur t' v' h et ev
    exact ⟨retryCond_ct t₀ v₀ tr ur t' v' trivial trivial (agree_of h (by simp)) et ev,trivial⟩

theorem bounded_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (step : StepTimingW sha3 w16 A B p a b c) (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.retry sha3 w16)
      (fun t v=>BoundedW w16 A B p a b c s t ∧ BoundedW w16 A B p a b c u v) := by
  let I := fun n t v=>RetryInv w16 A B p a b c s n t ∧ RetryInv w16 A B p a b c u n v
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.retry sha3 w16) (fun _ _=>True) := by
    refine RelCT.seq (R:=I 1) ?_ (RelCT.loop (M:=isa) (Q:=fun _ _=>True) I (fun n => ?_) 1)
    · intro t v tr ur t' v' h et ev
      rcases h with ⟨rfl,rfl⟩
      exact ⟨retryInit_ct t v tr ur t' v' trivial trivial (agree_of sp (by simp)) et ev,
        exec_post (retryInit_ok ps ss) et,exec_post (retryInit_ok pu us) ev⟩
    · intro t v tr ur t' v' h et ev
      rcases h with ⟨it,iv⟩
      have sp' : t.sp=v.sp := it.keep.sp.trans (sp.trans iv.keep.sp.symm)
      have tq := (retryBody_relCT (sha3 := sha3) step it iv sp' t v tr ur t' v' ⟨rfl,rfl⟩ et ev).1
      obtain ⟨et',-,it'⟩ := exec_post (retryStep_ok (sha3 := sha3) (fun _ ht hs=>advance_ok (sha3 := sha3) ht hs) it) et
      obtain ⟨ev',-,iv'⟩ := exec_post (retryStep_ok (sha3 := sha3) (fun _ ht hs=>advance_ok (sha3 := sha3) ht hs) iv) ev
      refine ⟨tq,by rw [et',ev'],fun _=>trivial,fun h=>?_⟩
      have hr : retryAgain A B n=true := by rw [et'] at h; exact Option.some.inj h
      have hn : n=1 := by simp only [retryAgain,decide_eq_true_eq] at hr; exact hr.1
      exact ⟨0,by omega_using [hn],it' hr,iv' hr⟩
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (bounded_ok (sha3 := sha3) (fun _ ht hs=>advance_ok (sha3 := sha3) ht hs) ps ss) et,
    exec_post (bounded_ok (sha3 := sha3) (fun _ ht hs=>advance_ok (sha3 := sha3) ht hs) pu us) ev⟩

structure CleanupW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) (s : State) : Prop where
  context : Context p a b c s
  pointer : s.gpr .x19=p
  left : Rej8.Scalar.CoeffsW w16 s.mem a (accepted A 5)
  right : Rej8.Scalar.CoeffsW w16 s.mem b (accepted B 5)
  saveLeft : checkpointW w16 (p+1680) a (accepted A 5) s.mem
  saveRight : checkpointW w16 (p+1696) b (accepted B 5) s.mem

theorem BoundedW.cleanup {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (h : BoundedW w16 A B p a b c s u) : CleanupW w16 A B p a b c u :=
  ⟨h.context,h.ptr,h.left,h.right,h.saveLeft,h.saveRight⟩

theorem CleanupW.only {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (h : CleanupW w16 A B p a b c s) (k : Only [.x24] s u) : CleanupW w16 A B p a b c u := by
  refine ⟨h.context.frame k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _),?_,?_,?_,?_,?_⟩
  · rw [k.get .x19]; exact h.pointer
  all_goals rw [k.mem]
  · exact h.left
  · exact h.right
  · exact h.saveLeft
  · exact h.saveRight

theorem CleanupW.zeroLeft {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : CleanupW w16 A B p a b c s) : ZeroReadyW w16 (accepted A 5) 1680 a s := by
  refine ⟨accepted_length A 5,h.left,?_,?_,?_,?_⟩
  · rw [h.pointer]; exact h.saveLeft
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · intro i hi; exact Noise.inScratch h.context.outA (cs_store_le w16 hi) (by decide)

theorem CleanupW.zeroRight {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : CleanupW w16 A B p a b c s) : ZeroReadyW w16 (accepted B 5) 1696 b s := by
  refine ⟨accepted_length B 5,h.right,?_,?_,?_,?_⟩
  · rw [h.pointer]; exact h.saveRight
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · intro i hi; exact Noise.inScratch h.context.outB (cs_store_le w16 hi) (by decide)

theorem mask_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.logic .and .x .x24 .x24 .x6]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem resume_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (step : StepTimingW sha3 w16 A B p a b c) (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraPair sha3 w16)
      (fun t v=>ResumePostW w16 A B p a b s t ∧ ResumePostW w16 A B p a b u v) := by
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraPair sha3 w16) (fun _ _=>True) := by
    change RelCT isa _ (.seq (Impl.MlKem.AArch64.Paired.retry sha3 w16) (.seq (.block _) _)) _
    refine RelCT.seq (bounded_relCT (sha3 := sha3) step ps pu ss us sp) ?_
    refine RelCT.seq (R:=fun t v : State=>CleanupW w16 A B p a b c t ∧ CleanupW w16 A B p a b c v ∧ t.sp=v.sp) ?_ ?_
    · intro t v tr ur t' v' h et ev
      have mt : Only [.x24] t t' := (exec_post (wp_and (fun w kw ew=>wp_nil (show Only [.x24] t w from kw))) et)
      have mv : Only [.x24] v v' := (exec_post (wp_and (fun w kw ew=>wp_nil (show Only [.x24] v w from kw))) ev)
      have hv : t.sp=v.sp := h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)
      exact ⟨mask_ct t v tr ur t' v' trivial trivial (agree_of hv (by simp)) et ev,
        h.1.cleanup.only mt,h.2.cleanup.only mv,mt.sp.trans (hv.trans mv.sp.symm)⟩
    · intro t v tr ur t' v' h et ev
      exact zeroBoth_relCT h.1.zeroLeft h.1.zeroRight h.2.1.zeroLeft h.2.1.zeroRight h.1.context.apart
        (by rw [h.1.pointer]; exact h.1.context.farA.sub_left (Offset.sub_base p (by decide)))
        h.2.2 (h.1.pointer.trans h.2.1.pointer.symm) t v tr ur t' v' ⟨rfl,rfl⟩ et ev
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (extraPair_ok (sha3 := sha3) ps ss) et,exec_post (extraPair_ok (sha3 := sha3) pu us) ev⟩

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! ### `MlKem.AArch64.Paired.ExtraStepTiming`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ContinueTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ResumeW (w16 : Bool) (L : List Zq) (B : Nat→Byte) (aP : Addr) (s : State) : Prop where
  env : Rej8.EnvW w16 56 B (s.gpr .x20) aP s
  constants : Rej8.Constants s
  len : L.length≤256
  coeffs : Rej8.Scalar.CoeffsW w16 s.mem aP L
  x3 : s.gpr .x3=cAddr w16 aP L.length
  x4 : (s.gpr .x4).toNat=256-L.length

theorem continue_relCT {w16 : Bool} {s u : State}
    {B : Nat→Byte} {L : List Zq} {aP : Addr} (ps : ResumeW w16 L B aP s) (pu : ResumeW w16 L B aP u)
    (hsp : s.sp=u.sp) (h20 : s.gpr .x20=u.gpr .x20) (h1 : s.gpr .x1=u.gpr .x1)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u)
      (.seq (.block (continueEntry)) (Impl.MlKem.AArch64.Rej8.rejLoop w16))
      (fun a b=>a.sp=b.sp ∧ a.gpr .x1=b.gpr .x1) := by
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block (continueEntry))
      (fun a b=>Rej8.EntryW w16 L 56 B (s.gpr .x20) aP a ∧
        Rej8.EntryW w16 L 56 B (s.gpr .x20) aP b ∧ a.sp=b.sp ∧ a.gpr .x16=b.gpr .x16) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha,hb'⟩
    subst a; subst b
    obtain ⟨ka,ha⟩ := exec_post (continueEntry_ok s ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
    obtain ⟨kb,hb'⟩ := exec_post (continueEntry_ok u pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
    refine ⟨continueEntry_ct s u tr ur a' b' trivial trivial (agree_of hsp (by simp)) ea eb,
      ha,?_,ka.sp.trans (hsp.trans kb.sp.symm),?_⟩
    · simpa only [h20] using hb'
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace := RelCT.seq start (segment_entry_relCT L 56 B _ aP (by decide) (by decide))
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha,hb'⟩
  subst a; subst b
  obtain ⟨ht,hsp'⟩ := trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb
  have hs := exec_post (continue_ok s ps.env ps.constants ps.len ps.coeffs ps.x3 ps.x4) ea
  have hu := exec_post (continue_ok u pu.env pu.constants pu.len pu.coeffs pu.x3 pu.x4) eb
  exact ⟨ht,hsp',by rw [hs.1.get .x1,hu.1.get .x1,h1]⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ExtraTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem load_resume {w16 : Bool} {s : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (h : ReadyW w16 L B (s.gpr .x20) (s.gpr .x1) aP s) (hc : Rej8.Constants s) :
    WP isa (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) s fun t =>
      Only [.x3,.x4] s t ∧ ResumeW w16 L B aP t := by
  have h0 : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 0) 8 := by rw [ptr_zero]; exact h.out0
  refine WP.mono (load_checkpoint s (r:=.x1) (slot:=0) (by decide) (by decide) (in_rd_wr h0)
    (in_rd_wr h.out1)) fun t ⟨kt,hv,t3,t4⟩ => ?_
  refine ⟨kt,?_,?_,h.len,?_,?_,?_⟩
  · rw [kt.get .x20]
    exact h.env.transfer kt.mem kt.rd kt.wr (kt.get .x16)
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · rw [kt.mem]; exact h.coeffs
  · rw [t3,ptr_zero]; exact h.saved.1
  · rw [t4]; exact h.saved.2

theorem extra_relCT {w16 : Bool} {s u : State} {B : Nat→Byte} {L : List Zq} {aP : Addr}
    (ps : ReadyW w16 L B (s.gpr .x20) (s.gpr .x1) aP s) (pu : ReadyW w16 L B (u.gpr .x20) (u.gpr .x1) aP u)
    (cs : Rej8.Constants s) (cu : Rej8.Constants u)
    (hsp : s.sp=u.sp) (h20 : s.gpr .x20=u.gpr .x20) (h1 : s.gpr .x1=u.gpr .x1)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject w16)
      (fun a b=>ExtraPostW w16 L B aP (s.gpr .x1) s a ∧ ExtraPostW w16 L B aP (u.gpr .x1) u b) := by
  let R := fun a b=>ResumeW w16 L B aP a ∧ ResumeW w16 L B aP b ∧
    a.sp=b.sp ∧ a.gpr .x20=b.gpr .x20 ∧ a.gpr .x1=b.gpr .x1 ∧ a.gpr .x16=b.gpr .x16
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) R := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha',hb'⟩
    subst a; subst b
    obtain ⟨ka,pa⟩ := exec_post (load_resume ps cs) ea
    obtain ⟨kb,pb⟩ := exec_post (load_resume pu cu) eb
    refine ⟨cursor_ct s u tr ur a' b' trivial trivial
      (agree_of hsp (by intro r hr; rw [List.mem_singleton.mp hr]; exact h1)) ea eb,
      pa,pb,ka.sp.trans (hsp.trans kb.sp.symm),?_,?_,?_⟩
    · rw [ka.get .x20,kb.get .x20,h20]
    · rw [ka.get .x1,kb.get .x1,h1]
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace : RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject w16) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.ite ?_ ?_ ?_)
    · intro a b h
      have he : a.gpr .x4=b.gpr .x4 := BitVec.eq_of_toNat_eq (h.1.x4.trans h.2.1.x4.symm)
      change some (a.gpr .x4 == 0)=some (b.gpr .x4 == 0)
      rw [he]
    · intro a b tr ur a' b' h ea eb
      have ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
          (.block [.movz .x .x0 1 0]) :=
        VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl
      exact ⟨ct a b tr ur a' b' trivial trivial (agree_of h.1.2.2.1 (by simp)) ea eb,trivial⟩
    · apply RelCT.assoc
      refine RelCT.seq (R:=fun a b : State=>a.sp=b.sp ∧ a.gpr .x1=b.gpr .x1) ?_ ?_
      · intro a b tr ur a' b' h ea eb
        exact continue_relCT h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2
          a b tr ur a' b' ⟨rfl,rfl⟩ ea eb
      · intro a b tr ur a' b' h ea eb
        exact ⟨storeCursor_ct a b tr ur a' b' trivial trivial
          (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) ea eb,trivial⟩
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha',hb'⟩
  subst a; subst b
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,
    exec_post (extra_ok s ps.env cs ps.len ps.coeffs ps.saved ps.out0 ps.out1 ps.apart) ea,
    exec_post (extra_ok u pu.env cu pu.len pu.coeffs pu.saved pu.out0 pu.out1 pu.apart) eb⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ExtraBothTiming.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem bothStart_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,.movz .x .x23 2 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem bothNext_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.logic .and .x .x22 .x22 .x0,.addImm .x .x20 .x20 504,.addImm .x .x1 .x1 16,
      .subImm .x .x23 .x23 1]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem bothEnd_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [Impl.MlKem.AArch64.mov .x6 .x22]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

/-- An iteration of `extraBoth` from a stream ready at the same place in both runs. -/
theorem bothBody_relCT {w16 : Bool} {t v : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (pt : ReadyW w16 L B (t.gpr .x20) (t.gpr .x1) aP t) (pv : ReadyW w16 L B (v.gpr .x20) (v.gpr .x1) aP v)
    (ct : Rej8.Constants t) (cv : Rej8.Constants v) (sp : t.sp=v.sp) (h20 : t.gpr .x20=v.gpr .x20)
    (h1 : t.gpr .x1=v.gpr .x1) (h16 : t.gpr .x16=v.gpr .x16) :
    RelCT isa (fun x y=>x=t ∧ y=v) (bothBody w16) (fun _ _=>True) := by
  refine RelCT.seq (R:=fun x y : State=>x.sp=y.sp) ?_ ?_
  · intro x y tx ty x' y' h ex ey
    have r := extra_relCT pt pv ct cv sp h20 h1 h16 x y tx ty x' y' h ex ey
    exact ⟨r.1,r.2.1.keep.sp.trans (sp.trans r.2.2.keep.sp.symm)⟩
  · intro x y tx ty x' y' h ex ey
    exact ⟨bothNext_ct x y tx ty x' y' trivial trivial (agree_of h (by simp)) ex ey,trivial⟩

theorem extraBoth_relCT {w16 : Bool} {s u : State} {L M : List Zq} {A B : Nat→Byte} {p a b : Addr}
    (hs : BothReadyW w16 L M A B p a b s) (hu : BothReadyW w16 L M A B p a b u)
    (sp : s.sp=u.sp) (table : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun x y=>x=s ∧ y=u) (Impl.MlKem.AArch64.Paired.extraBoth w16) (fun _ _=>True) := by
  let I : Nat → State → State → Prop := fun n t v =>
    (n=2 ∧ BothInv w16 L M A B p a b s 0 t ∧ BothInv w16 L M A B p a b u 0 v) ∨
    (n=1 ∧ BothInv w16 L M A B p a b s 1 t ∧ BothInv w16 L M A B p a b u 1 v)
  have start : RelCT isa (fun x y=>x=s ∧ y=u)
      (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,.movz .x .x23 2 0]) (I 2) := by
    intro x y tx ty x' y' h ex ey
    rcases h with ⟨rfl,rfl⟩
    exact ⟨bothStart_ct x y tx ty x' y' trivial trivial (agree_of sp (by simp)) ex ey,
      .inl ⟨rfl,exec_post (bothStart_ok hs) ex,exec_post (bothStart_ok hu) ey⟩⟩
  have loop : RelCT isa (I 2) (.loop (bothBody w16) (.nonzero .x .x23)) (fun t v=>t.sp=v.sp) := by
    refine RelCT.loop (M:=isa) I (fun n => ?_) 2
    intro t v tt tv t' v' hI et ev
    rcases hI with ⟨rfl,it,iv⟩|⟨rfl,it,iv⟩
    · obtain ⟨kt,_,ct,t20,t1,_,_,ra,_⟩ := id it
      obtain ⟨kv,_,cv,v20,v1,_,_,rb,_⟩ := id iv
      have tq := bothBody_relCT (by rw [t20,t1]; exact ra) (by rw [v20,v1]; exact rb) ct cv
        (kt.sp.trans (sp.trans kv.sp.symm)) (t20.trans v20.symm) (t1.trans v1.symm)
        (by rw [kt.get .x16,kv.get .x16,table]) t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have it' := (exec_post (bothStep0_ok hs it) et).1
      have iv' := (exec_post (bothStep0_ok hu iv) ev).1
      have et23 : isa.eval (.nonzero .x .x23) t'=some true := by rw [eval_nonzero,it'.2.2.2.2.2.1]; rfl
      have ev23 : isa.eval (.nonzero .x .x23) v'=some true := by rw [eval_nonzero,iv'.2.2.2.2.2.1]; rfl
      refine ⟨tq.1,by rw [et23,ev23],fun h => (by rw [et23] at h; cases h),fun _ => ⟨1,by decide,.inr ⟨rfl,it',iv'⟩⟩⟩
    · obtain ⟨kt,_,ct,t20,t1,_,_,_,_,rb⟩ := id it
      obtain ⟨kv,_,cv,v20,v1,_,_,_,_,rb'⟩ := id iv
      have tq := bothBody_relCT (by rw [t20,t1]; exact rb) (by rw [v20,v1]; exact rb') ct cv
        (kt.sp.trans (sp.trans kv.sp.symm)) (t20.trans v20.symm) (t1.trans v1.symm)
        (by rw [kt.get .x16,kv.get .x16,table]) t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have it' := (exec_post (bothStep1_ok hs it) et).1
      have iv' := (exec_post (bothStep1_ok hu iv) ev).1
      have et23 : isa.eval (.nonzero .x .x23) t'=some false := by rw [eval_nonzero,it'.2.2.2.1]; rfl
      have ev23 : isa.eval (.nonzero .x .x23) v'=some false := by rw [eval_nonzero,iv'.2.2.2.1]; rfl
      refine ⟨tq.1,by rw [et23,ev23],fun _ => it'.1.sp.trans (sp.trans iv'.1.sp.symm),
        fun h => by rw [et23] at h; cases h⟩
  refine RelCT.seq start (RelCT.seq loop ?_)
  intro t v tt tv t' v' h et ev
  exact ⟨bothEnd_ct t v tt tv t' v' trivial trivial (agree_of h (by simp)) et ev,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Proof.Sha3.AArch64.Neon

structure StepReadyW (w16 : Bool) (A B : Spec.Sha3.State) (L M : List Zq) (p a b c : Addr) (s : State) : Prop where
 context : Context p a b c s
 pointer : s.gpr .x19=p
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=c
 pair : PairAt s.mem p A B
 lenLeft : L.length≤256
 lenRight : M.length≤256
 left : Rej8.Scalar.CoeffsW w16 s.mem a L
 right : Rej8.Scalar.CoeffsW w16 s.mem b M
 saveLeft : checkpointW w16 (p+1680) a L s.mem
 saveRight : checkpointW w16 (p+1696) b M s.mem

theorem nextBlock_ready {w16 : Bool} {s : State} {A B : Spec.Sha3.State} {L M : List Zq} {p a b c : Addr}
 (h : StepReadyW w16 A B L M p a b c s) :
 WP isa (nextBlock sha3) s fun u=> Keep nextRegs s u ∧ u.gpr .x16=c ∧
   BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
     (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b u := by
 rcases h with ⟨ctx,hp,sym,pair,hl,hm,ca,cb,sa,sb⟩
 refine WP.mono_syms (nextBlock_ok (sha3 := sha3) hp ctx.scratch pair) fun u h hsym => ?_
 rcases h with ⟨ku,fu,precise,up,pu,ra,rb,cs,ut⟩
 have fu' : Frame (stepWrites p a b) s.mem u.mem := fu.mono (by simp [stepWrites])
 have cu := ctx.frame ku.rd ku.wr fu'
 have ux : u.gpr .x16=c := by rw [ut,hsym,sym]
 have ua := coeffs_frame ca hl fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farA.symm)
 have ub := coeffs_frame cb hm fu (by intro r hr; rw [List.mem_singleton.mp hr]; exact ctx.farB.symm)
 have checkpoints {off : Nat} (ho : off=1680 ∨ off=1696) :
     ∀r∈nextWrites p,(Region.mk (p+BitVec.ofNat 64 off) 16).Disjoint r := by
  have hlo : 1680≤off := by omega_using [ho]
  have hhi : off≤1696 := by omega_using [ho]
  intro r hr
  simp only [nextWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact Offset.disjoint_base p (d:=off) (n:=16) (k:=400) (by omega_using [ho]) (by omega_using [ho])
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=400) (k:=168) (by omega_using [ho]) (by omega_using [ho]) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=904) (k:=168) (by omega_using [ho]) (by omega_using [ho]) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=1536) (k:=136) (by omega_using [ho]) (by omega_using [ho]) (by decide)
  · exact Offset.disjoint p (d:=off) (n:=16) (e:=1408) (k:=8) (by omega_using [ho]) (by omega_using [ho]) (by decide)
 have usa := checkpoint_frame sa precise (checkpoints (Or.inl rfl))
 have usb := checkpoint_frame sb precise (checkpoints (Or.inr rfl))
 have ea := cu.envW (w16 := w16) ux (N:=56) (off:=400) (by decide) (by decide) (Or.inl rfl) (fun i hi=>ra.byte hi)
 have eb := cu.envW (w16 := w16) ux (N:=56) (off:=904) (by decide) (by decide) (Or.inr rfl) (fun i hi=>rb.byte hi)
 have iw {o l : Nat} (ho : o+l≤2048) := Noise.inScratch cu.scratch ho (by decide)
 refine ⟨ku,ux,up,cu.scratch,cu.farA,cu.farB,cu.apart,?_,?_,?_,cs⟩
 · exact ⟨ea,hl,ua,usa,iw (o:=1680) (by decide),by rw [BitVec.add_assoc]; exact iw (o:=1688) (by decide),
     cu.farA.symm.sub_right (Offset.sub_base p (by decide))⟩
 · exact ⟨eb,hm,ub,usb,iw (o:=1696) (by decide),by rw [BitVec.add_assoc]; exact iw (o:=1704) (by decide),
     cu.farB.symm.sub_right (Offset.sub_base p (by decide))⟩
 · intro mask hm; rw [ux]; exact cu.tableScratch.sub_left (Rej8.table_sub c hm)
theorem extraStep_relCT {w16 : Bool} {s u : State} {A B : Spec.Sha3.State} {L M : List Zq} {p a b c : Addr}
 (hs : StepReadyW w16 A B L M p a b c s) (hu : StepReadyW w16 A B L M p a b c u)
 (sp : s.sp=u.sp) :
 RelCT isa (fun x y=>x=s ∧ y=u) (Impl.MlKem.AArch64.Paired.extraStep sha3 w16) (fun _ _=>True) := by
 have first : RelCT isa (fun x y=>x=s ∧ y=u) (nextBlock sha3)
     (fun x y=>BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
         (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b x ∧
       BothReadyW w16 L M (Proof.Sha3.byteOf (Spec.Sha3.keccakF A))
         (Proof.Sha3.byteOf (Spec.Sha3.keccakF B)) p a b y ∧ x.sp=y.sp ∧ x.gpr .x16=y.gpr .x16) := by
  intro x y tx ty x' y' h ex ey
  rcases h with ⟨hx,hy⟩
  subst x; subst y
  obtain ⟨kx,tx16,px⟩ := exec_post (nextBlock_ready (sha3 := sha3) hs) ex
  obtain ⟨ky,ty16,py⟩ := exec_post (nextBlock_ready (sha3 := sha3) hu) ey
  exact ⟨nextBlock_ct (sha3 := sha3) s u tx ty x' y' trivial trivial
    (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact hs.pointer.trans hu.pointer.symm)) ex ey,
    px,py,kx.sp.trans (sp.trans ky.sp.symm),tx16.trans ty16.symm⟩
 have grouped : RelCT isa (fun x y=>x=s ∧ y=u) (.seq (nextBlock sha3) (Impl.MlKem.AArch64.Paired.extraBoth w16)) (fun _ _=>True) := by
  refine RelCT.seq first ?_
  intro x y tx ty x' y' h ex ey
  exact extraBoth_relCT h.1 h.2.1 h.2.2.1 h.2.2.2 x y tx ty x' y' ⟨rfl,rfl⟩ ex ey
 intro x y tx ty x' y' h ex ey
 cases ex with
 | seq e1 ex =>
  cases ex with
  | seq e2 ex =>
   cases ex with
   | seq e3 e4 =>
    cases ey with
    | seq f1 ey =>
     cases ey with
     | seq f2 ey =>
      cases ey with
      | seq f3 f4 =>
       obtain ⟨ht,hq⟩ := grouped _ _ _ _ _ _ h
         (.seq (.seq e1 (.seq e2 e3)) e4) (.seq (.seq f1 (.seq f2 f3)) f4)
       exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

end VG.Proof.MlKem.AArch64.Paired

end

end


@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64

theorem stepTiming {w16 : Bool} (A B : Spec.Sha3.State) (p a b c : Addr) : StepTimingW sha3 w16 A B p a b c := by
  intro s u n _ hs hu ss us sp
  exact extraStep_relCT (sha3 := sha3)
    ⟨hs.context,hs.ptr,ss,hs.pair,accepted_length A n,accepted_length B n,hs.left,hs.right,hs.saveLeft,hs.saveRight⟩
    ⟨hu.context,hu.ptr,us,hu.pair,accepted_length A n,accepted_length B n,hu.left,hu.right,hu.saveLeft,hu.saveRight⟩ sp

theorem extraPair_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraPair sha3 w16)
      (fun t v=>ResumePostW w16 A B p a b s t ∧ ResumePostW w16 A B p a b u v) :=
  resume_relCT (sha3 := sha3) (stepTiming (sha3 := sha3) A B p a b c) ps pu ss us sp

end VG.Proof.MlKem.AArch64.Paired
