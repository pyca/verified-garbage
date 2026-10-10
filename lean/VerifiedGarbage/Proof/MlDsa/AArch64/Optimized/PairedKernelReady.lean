import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRestoreLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMiddle
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ## From `PairedFinalReturn.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def finalKernel (hint : Bool) : Prog isa :=
  .seq (.loop (.block (finalCheckCode hint++finalAdvance)) (.nonzero .x .x12))
    (.block (finish (if hint then .h else .z)))

/-- Exact final inverse/check traversal followed by return and ABI restore. -/
theorem finalKernel_ok (hint : Bool) {s₀ s : State} {table work : Addr}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem work s₀.v)
    (hwork : s.gpr .x2=work)
    (hsd : (⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hrs : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr)
      ((work+BitVec.ofNat 64 128)+BitVec.ofNat 64 p.2) 16)
    (ht : PairedTable.Words s.mem table)
    (hd : (⟨table,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hx : s.gpr .x1=table+BitVec.ofNat 64 3840)
    (hcount : s.gpr .x12=8) (hc : CheckReady hint s)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (hw : ∀u<8,∀p:Fin 2,∀j:Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16 ∧
      (hint=true → InRegions (s.rd++s.wr) ((s.gpr .x16+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) ∧
      InRegions s.wr ((s.gpr .x15+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16) :
    WP isa (finalKernel hint) s fun t =>
      let d := finalPassData hint work (s.gpr .x15) (s.gpr .x16) (constantsAt s) (dataAt s) 8
      Keep ((gr++finalGprs)++([.x0,.x9,.x10] : List Reg)) s₀ t ∧
      t.mem=d.mem ∧ t.gpr .x0=dataReturn (if hint then .h else .z) d := by
  unfold finalKernel
  refine loop_finish_ok _ hf hs (vs := finalCheckRegs) (writes := [⟨s.gpr .x15,2048⟩])
    (by simpa only [List.mem_singleton,forall_eq] using hsd) hrs ?_
  refine WP.mono (finalLoop_ok hint ht hd hx hcount hc hrt hr hw)
    fun t ⟨hft,h2,_,_,hdata⟩ => ?_
  refine ⟨hft,by simpa only [hwork,show (128:Addr)=BitVec.ofNat 64 128 by rfl] using h2,by simpa only [hwork] using hdata,?_⟩
  change Frame _ _ (dataAt t).mem
  rw [hdata]
  exact finalPass_frame _ _ _ _ _ _ (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

def init : List Instr :=
  VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++ [.vop (.dup .s4 .v30 .x10)] ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.vc .v31 8380417 ++ [.movz .x .x11 8 0]

theorem initCounter_ok (s : State) : WP isa (.block [.movz .x .x11 8 0]) s fun t =>
    ((t.gpr .x11=8 ∧ t.mem=s.mem) ∧ Keep [.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun

theorem init_ok (s : State) : WP isa (.block init) s fun t =>
    Keep [.x9,.x10,.x11] s t ∧ t.mem=s.mem ∧ t.gpr .x11=8 ∧ ProductConstants t := by
  unfold init
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (productConst_ok s) fun a ⟨hka,hma,h30⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v31 8380417) fun b hb => ?_
  refine WP.mono (initCounter_ok b) fun t ⟨⟨⟨h11,hm⟩,hk⟩,hv⟩ => ?_
  refine ⟨((hka.trans (constKeep_keep hb.1 (by decide))).trans hk).mono,
    hm.trans (hb.1.mem.trans hma),h11,?_⟩
  exact ⟨by rw [hv,hb.2]; rfl,by rw [hv,hb.1.vec .v30 (by decide),h30]; rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedSetupFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

def allVectors : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,
  .v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,
  .v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31]

/-- Scalar preservation can be carried across stages independently of vector
preservation: the final saved-vector restoration discharges the latter. -/
theorem CallFrame.ofKeepWide {gr : List Reg} {s t : State} (h : Keep gr s t) :
    CallFrame gr allVectors s t := by
  refine ⟨fun r hr => h.get r hr,h.rd,h.wr,h.sp,?_⟩
  intro r hr
  exact False.elim (hr ((show ∀r:VReg,r∈allVectors by intro r; cases r <;> decide) r))

theorem setup_callFrame {vr : List VReg} {s t : State} (h : SetupKeep vr s t) :
    CallFrame [.x9] vr s t :=
  ⟨fun r hr => h.gpr r (by simpa only [List.mem_singleton] using hr),h.rd,h.wr,h.sp,h.vec⟩

theorem setup_callFrame_wide {vr : List VReg} {s t : State} (h : SetupKeep vr s t) :
    CallFrame [.x9] allVectors s t := by
  refine (setup_callFrame h).mono (by rfl) ?_
  intro r _
  exact (show ∀r:VReg,r∈allVectors by intro r; cases r <;> decide) r

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedCheckSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_mono)

structure CheckSetup (hint : Bool) (s t : State) : Prop where
  ready : CheckReady hint t
  flags : t.v .v30=0
  count : hint=true → t.v .v14=0
  gamma : hint=true → ∀e<4,vword (t.v .v11) e=(s.gpr .x17).setWidth 32
  lower : ∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1
  width : ∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)

theorem checkConstants_ok (hint : Bool) (g : Nat) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (constants (if hint then .h else .z) g)) s fun t =>
      SetupKeep constantRegs s t ∧ CheckSetup hint s t := by
  cases hint
  · refine WP.mono (zConstants_ok g s hq) fun t ⟨hf,hc,hf0,hl,hw⟩ => ?_
    exact ⟨setup_mono hf (by decide),⟨hc,hf0,by simp,by simp,hl,hw⟩⟩
  · refine WP.mono (hConstants_ok g s hq) fun t ⟨hf,hc,hf0,hn,hg,hl,hw⟩ => ?_
    exact ⟨hf,⟨hc,hf0,fun _ => hn,fun _ => hg,hl,hw⟩⟩

def middleRegs : List Reg := [.x0,.x2,.x9,.x12]

theorem checkMiddle_ok (hint : Bool) (g : Nat) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (middleMoves++constants (if hint then .h else .z) g)) s fun t =>
      CallFrame middleRegs constantRegs s t ∧ t.mem=s.mem ∧
      t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧
      CheckSetup hint s t := by
  rw [WP.block_append_iff]
  refine WP.mono (middleMoves_ok s) fun a ⟨⟨⟨h0,h2,h12,hm⟩,hk⟩,hv⟩ => ?_
  refine WP.mono (checkConstants_ok hint g a (by rw [hv]; exact hq)) fun t ⟨ht,hc⟩ => ?_
  refine ⟨((CallFrame.ofKeep hk hv).trans (setup_callFrame ht)).mono (by decide) (by simp),
    ht.mem.trans hm,(ht.gpr .x0 (by decide)).trans h0,(ht.gpr .x2 (by decide)).trans h2,
    (ht.gpr .x12 (by decide)).trans h12,?_⟩
  refine ⟨hc.ready,hc.flags,hc.count,?_,?_,?_⟩
  · simpa only [hk.get .x17 (by decide)] using hc.gamma
  · simpa only [hk.get .x8 (by decide)] using hc.lower
  · simpa only [hk.get .x8 (by decide)] using hc.width

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirstKernel.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def firstKernel : Prog isa := .seq (.block init)
  (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11))

theorem firstKernel_ok {s : State}
    (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩)
    (hrt : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀i:Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16 ∧
      ∀p:Fin 2,InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*p.val+16*i.val)) 16)
    (hw : ∀u<8,∀p:Fin 2,∀i:Fin 8,InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*p.val+16*i.val)) 16) :
    WP isa firstKernel s fun t =>
      Keep [.x0,.x1,.x9,.x10,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 := by
  unfold firstKernel
  refine WP.seq (WP.mono (init_ok s) fun a ⟨ha,hm,hc,hq⟩ => ?_)
  rw [firstBlock_eq]
  refine WP.mono (firstLoop_ok ?_ ?_ hc hq ?_ ?_ ?_) fun t ⟨hk,hqt,h0,h1,h13,h14,hmem⟩ => ?_
  · simpa only [hm,ha.get .x1 (by decide)] using ht
  · simpa only [ha.get .x1 (by decide),ha.get .x0 (by decide)] using hd
  · simpa only [ha.rd,ha.wr,ha.get .x1 (by decide)] using hrt
  · simpa only [ha.rd,ha.wr,ha.get .x13 (by decide),ha.get .x14 (by decide)] using hr
  · simpa only [ha.wr,ha.get .x0 (by decide)] using hw
  · refine ⟨(ha.trans hk).mono,hqt,?_,?_,?_,?_,?_⟩
    · simpa only [ha.get .x0 (by decide)] using h0
    · simpa only [ha.get .x1 (by decide)] using h1
    · simpa only [ha.get .x13 (by decide)] using h13
    · simpa only [ha.get .x14 (by decide)] using h14
    · simpa only [hm,ha.get .x0 (by decide),ha.get .x13 (by decide),ha.get .x14 (by decide)] using hmem

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedLowSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowSetup (g : Nat) (s t : State) : Prop where
  ready : LowReady g t
  flags : t.v .v30=0
  scale : ∀e<4,vword (t.v .v15) e=BitVec.ofNat 32 (2*g)
  lower : ∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1
  width : ∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)

theorem lowMiddle_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (middleMoves++constants .r0 g)) s fun t =>
      CallFrame middleRegs constantRegs s t ∧ t.mem=s.mem ∧
      t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧
      LowSetup g s t := by
  rw [WP.block_append_iff]
  refine WP.mono (middleMoves_ok s) fun a ⟨⟨⟨h0,h2,h12,hm⟩,hk⟩,hv⟩ => ?_
  refine WP.mono (r0Constants_ok g hg a (by rw [hv]; exact hq)) fun t ⟨ht,hc,hflag,hs,hl,hw⟩ => ?_
  refine ⟨((CallFrame.ofKeep hk hv).trans (setup_callFrame ht)).mono (by decide) (by simp),
    ht.mem.trans hm,(ht.gpr .x0 (by decide)).trans h0,(ht.gpr .x2 (by decide)).trans h2,
    (ht.gpr .x12 (by decide)).trans h12,?_⟩
  refine ⟨hc,hflag,hs,?_,?_⟩
  · simpa only [hk.get .x8 (by decide)] using hl
  · simpa only [hk.get .x8 (by decide)] using hw

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedKernelSplit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Only reassociate the measured blocks; no scheduling or arithmetic changes. -/
theorem checkKernel_wp (hint : Bool) (g : Nat) {s : State} {Q : State→Prop}
    (h : WP isa (.seq firstKernel (.seq
      (.block (middleMoves++constants (if hint then .h else .z) g)) (finalKernel hint))) s Q) :
    WP isa (kernel (if hint then .h else .z) g) s Q := by
  have he : kernel (if hint then .h else .z) g=
      .seq (.block init) (.seq
      (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11))
      (.seq (.block (middleMoves++constants (if hint then .h else .z) g)) (finalKernel hint))) := by
    cases hint
    · rw [show (if false then Kind.h else Kind.z)=Kind.z by rfl]
      simp only [kernel,finalKernel,final_z_eq,init,middleMoves,
        VG.Impl.MlDsa.AArch64.Optimized.Paired.vc,List.append_assoc]
      rfl
    · rw [show (if true then Kind.h else Kind.z)=Kind.h by rfl]
      simp only [kernel,finalKernel,final_h_eq,init,middleMoves,
        VG.Impl.MlDsa.AArch64.Optimized.Paired.vc,List.append_assoc]
      rfl
  rw [he]
  exact WP.assoc h

theorem lowKernel_wp (g : Nat) {s : State} {Q : State→Prop}
    (h : WP isa (.seq firstKernel (.seq (.block (middleMoves++constants .r0 g)) (lowKernel g))) s Q) :
    WP isa (kernelPaired g) s Q := by
  have he : kernelPaired g=.seq (.block init) (.seq
      (.loop (.block VG.Impl.MlDsa.AArch64.Optimized.PairedBase.firstBlock) (.nonzero .x .x11))
      (.seq (.block (middleMoves++constants .r0 g)) (lowKernel g))) := by
    simp only [kernelPaired,lowKernel,final_r0_eq,init,middleMoves,
      VG.Impl.MlDsa.AArch64.Optimized.Paired.vc,List.append_assoc]
    rfl
  rw [he]
  exact WP.assoc h

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedKernelReady.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Buffer permissions at the internal kernel boundary, after argument remapping. -/
structure KernelAccess (s : State) : Prop where
  table : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16
  common : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16
  secret : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16
  workRead : ∀off,off+16≤2176 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16
  workWrite : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16
  dataRead : ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16
  dataWrite : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16

structure Prepared (s u : State) : Prop where
  mem : u.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8
  work : u.gpr .x2=s.gpr .x0
  data : u.gpr .x15=s.gpr .x15
  aux : u.gpr .x16=s.gpr .x16

/-- Exact first-pass setup for either final checker. -/
theorem firstKernel_access_ok {s : State} (ha : KernelAccess s)
    (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩) :
    WP isa firstKernel s fun t =>
      VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x9,.x10,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=firstPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 :=
  firstKernel_ok ht hd ha.table
    (by
      intro u hu i
      constructor
      · rw [BitVec.add_assoc,←BitVec.ofNat_add]
        exact ha.common _ (by omega)
      · intro p
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        exact ha.secret _ (by omega))
    (by
      intro u hu p i
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact ha.workWrite _ (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
