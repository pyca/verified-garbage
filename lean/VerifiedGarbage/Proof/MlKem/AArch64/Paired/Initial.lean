module
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def initialCode (a b : Nat) (w16 : Bool := false) : Prog isa := Paired.rejectBoth a b w16

def initialRegions (p a b : Addr) : List Region :=
 [polyRegion a,polyRegion b,⟨p+BitVec.ofNat 64 1680,16⟩,⟨p+BitVec.ofNat 64 1696,16⟩]

/-- The registers `initialCode` changes. -/
def initialRegs : List Reg :=
 [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x20,.x21,.x22,.x23]

structure InitialPostW (w16 : Bool) (A B : Nat→Byte) (p a b : Addr) (s t : State) : Prop where
  keep : Keep initialRegs s t
  frame : Frame (initialRegions p a b) s.mem t.mem
  first : Rej8.Scalar.CoeffsW w16 t.mem a (sampleAfter [] A 168)
  second : Rej8.Scalar.CoeffsW w16 t.mem b (sampleAfter [] B 168)
  savedA : checkpointW w16 (p+BitVec.ofNat 64 1680) a (sampleAfter [] A 168) t.mem
  savedB : checkpointW w16 (p+BitVec.ofNat 64 1696) b (sampleAfter [] B 168) t.mem
  both : (t.gpr .x6).toNat=if (sampleAfter [] A 168).length=256 ∧ (sampleAfter [] B 168).length=256 then 1 else 0
  constants : Rej8.Constants t

/-! ## One stream -/

/-- The entry of a stream's rejection: its buffer at `x20`, its output at `x21`. -/
def oneEntry : List Instr :=
  [mov .x2 .x20,mov .x3 .x21,.movz .x .x4 256 0,.movz .x .x5 168 0,.movz .x .x9 3329 0,.movz .x .x10 15 0]

/-- The end of an iteration: the flag, the next stream's pointers, and `x6 = 0` after the last. -/
def oneNext : List Instr :=
  [.logic .and .x .x22 .x22 .x0,.addImm .x .x20 .x20 504,mov .x21 .x23,.addImm .x .x1 .x1 16,
    .sub .x .x6 .x1 .x19,.subImm .x .x6 .x6 1712]

/-- The stream's cursor to its slot at `x1`. -/
def oneStore : List Instr := [.str .x .x3 .x1 0,.str .x .x4 .x1 8]

/-- An iteration of `rejectBoth`. -/
def oneBody (w16 : Bool := false) : Prog isa :=
  seqs [.block oneEntry,Rej8.rejLoop w16,.block (oneStore ++ oneNext)]

/-- A stream ready for its first three blocks' rejection: its blocks at `x20`,
its output at `x21`, its cursor slot at `x1`. -/
structure OneReadyR (w16 : Bool) (B : Nat→Byte) (s : State) : Prop where
  env : Rej8.EnvW w16 168 B (s.gpr .x20) (s.gpr .x21) s
  constants : Rej8.Constants s
  out0 : InRegions s.wr (s.gpr .x1) 8
  out1 : InRegions s.wr (s.gpr .x1+8) 8
  apart : (polyRegion (s.gpr .x21)).Disjoint ⟨s.gpr .x1,16⟩

def oneRegs : List Reg :=
 [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x20,.x21,.x22]

/-- 1 when `L` is complete. -/
def doneFlag (L : List Zq) : BitVec 64 := if L.length=256 then 1 else 0

structure OnePostW (w16 : Bool) (B : Nat→Byte) (t u : State) : Prop where
  keep : Keep oneRegs t u
  frame : Frame [polyRegion (t.gpr .x21),⟨t.gpr .x1,16⟩] t.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem (t.gpr .x21) (sampleAfter [] B 168)
  saved : checkpointW w16 (t.gpr .x1) (t.gpr .x21) (sampleAfter [] B 168) u.mem
  flag : u.gpr .x22=t.gpr .x22 &&& doneFlag (sampleAfter [] B 168)
  x20 : u.gpr .x20=t.gpr .x20+BitVec.ofNat 64 504
  x21 : u.gpr .x21=t.gpr .x23
  x1 : u.gpr .x1=t.gpr .x1+BitVec.ofNat 64 16
  x6 : u.gpr .x6=t.gpr .x1+BitVec.ofNat 64 16-t.gpr .x19-BitVec.ofNat 64 1712
  constants : Rej8.Constants u

theorem oneEntry_ok {w16 : Bool} {t : State} {B : Nat→Byte} (h : OneReadyR w16 B t) :
    WP isa (.block oneEntry) t fun u => Only [.x2,.x3,.x4,.x5,.x9,.x10] t u ∧
      Rej8.EntryW w16 [] 168 B (t.gpr .x20) (t.gpr .x21) u := by
  have hw : WP isa (.block oneEntry) t fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] t u ∧ u.gpr .x2=t.gpr .x20 ∧ u.gpr .x3=t.gpr .x21 ∧
      (u.gpr .x4).toNat=256 ∧ (u.gpr .x5).toNat=168 ∧ (u.gpr .x9).toNat=q ∧ (u.gpr .x10).toNat=15 := by
    refine wp_mov fun a ha ea => wp_mov fun b hb eb =>
      wp_movz fun c hc ec => wp_movz fun d hd ed => wp_movz fun e he ee =>
      wp_movz fun u hu eu => wp_nil ?_
    refine ⟨(((((ha.trans hb).trans hc).trans hd).trans he).trans hu).mono,?_,?_,?_,?_,?_,?_⟩
    · rw [hu.get .x2,he.get .x2,hd.get .x2,hc.get .x2,hb.get .x2,ea]
    · rw [hu.get .x3,he.get .x3,hd.get .x3,hc.get .x3,eb,ha.get .x21]
    · rw [hu.get .x4,he.get .x4,hd.get .x4,ec]; rfl
    · rw [hu.get .x5,he.get .x5,ed]; rfl
    · rw [hu.get .x9,ee]; rfl
    · rw [eu]; rfl
  refine WP.mono (WP.keepV (by rfl) hw) fun u ⟨⟨hk,x2,x3,x4,x5,x9,x10⟩,hv⟩ => ⟨hk,?_⟩
  refine ⟨h.env.transfer hk.mem hk.rd hk.wr (hk.get .x16),?_,by simp,
    fun _ h => False.elim (Nat.not_lt_zero _ h),x2,?_,x4,x5,x9,x10⟩
  · exact ⟨by rw [hv]; exact h.constants.index,by rw [hv]; exact h.constants.mask,
      by simpa only [hv] using h.constants.q,by simpa only [hv] using h.constants.weights,
      by simpa only [hv] using h.constants.zero⟩
  · simpa only [List.length_nil,cAddr,Nat.mul_zero,ptr_zero] using x3

theorem oneBody_ok {w16 : Bool} {t : State} {B : Nat→Byte} (h : OneReadyR w16 B t) :
    WP isa (oneBody w16) t (OnePostW w16 B t) := by
  have z0 : ∀ x : Addr, x+BitVec.ofNat 64 0=x := ptr_zero
  change WP isa (.seq (.block oneEntry) (.seq (Rej8.rejLoop w16) (.block (oneStore ++ oneNext)))) t _
  refine WP.seq (WP.mono (oneEntry_ok h) fun a ⟨ha,he⟩ => ?_)
  refine WP.seq (WP.mono (Rej8.WP.constants (Rej8.segment_ok he (by decide) (by decide)) he.constants
    (by cases w16 <;> rfl)) fun b ⟨hb,cb⟩ => ?_)
  have b1 : b.gpr .x1=t.gpr .x1 := (hb.keep.get .x1).trans (ha.get .x1)
  have bw : b.wr=t.wr := hb.acc.wr.trans (ha.wr)
  have h0 : InRegions b.wr (b.gpr .x1+BitVec.ofNat 64 0) 8 := by rw [z0,b1,bw]; exact h.out0
  have h1 : InRegions b.wr (b.gpr .x1+BitVec.ofNat 64 (0+8)) 8 := by rw [b1,bw]; exact h.out1
  have hd : (polyRegion (t.gpr .x21)).Disjoint ⟨b.gpr .x1+BitVec.ofNat 64 0,16⟩ := by rw [z0,b1]; exact h.apart
  refine WP.block_append (WP.mono (Rej8.WP.constants (store_ok b (r:=.x1) (slot:=0) (by decide) (by decide)
    hb.acc.len hb.acc.coeffs hb.acc.x3 hb.acc.x4 h0 h1 hd) cb (by rfl)) fun c ⟨hc,cc⟩ => ?_)
  rw [z0,b1] at hc
  have blk : WP isa (.block oneNext) c fun u => Only ([.x22]++[.x20]++[.x21]++[.x1]++[.x6]++[.x6]) c u ∧
      u.gpr .x22=c.gpr .x22 &&& c.gpr .x0 ∧ u.gpr .x20=c.gpr .x20+BitVec.ofNat 64 504 ∧
      u.gpr .x21=c.gpr .x23 ∧ u.gpr .x1=c.gpr .x1+BitVec.ofNat 64 16 ∧
      u.gpr .x6=c.gpr .x1+BitVec.ofNat 64 16-c.gpr .x19-BitVec.ofNat 64 1712 :=
    wp_and fun u₁ k₁ e₁ => wp_addImm (by decide) fun u₂ k₂ e₂ => wp_mov fun u₃ k₃ e₃ =>
      wp_addImm (by decide) fun u₄ k₄ e₄ => wp_sub fun u₅ k₅ e₅ => wp_subImm (by decide) fun u k₆ e₆ =>
      wp_nil ⟨((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆,
        by rw [k₆.get .x22,k₅.get .x22,k₄.get .x22,k₃.get .x22,k₂.get .x22,e₁],
        by rw [k₆.get .x20,k₅.get .x20,k₄.get .x20,k₃.get .x20,e₂,k₁.get .x20],
        by rw [k₆.get .x21,k₅.get .x21,k₄.get .x21,e₃,k₂.get .x23,k₁.get .x23],
        by rw [k₆.get .x1,k₅.get .x1,e₄,k₃.get .x1,k₂.get .x1,k₁.get .x1],
        by rw [e₆,e₅,e₄,k₄.get .x19,k₃.get .x1,k₃.get .x19,k₂.get .x1,k₂.get .x19,k₁.get .x1,k₁.get .x19]⟩
  refine WP.mono (Rej8.WP.constants blk cc (by rfl)) fun u ⟨⟨ku,e22,e20,e21,e1,e6⟩,cu⟩ => ?_
  have kc : Keep ([.x2,.x3,.x4,.x5,.x9,.x10]++(.x0::Rej8.Scalar.lRegs)++[]) t c :=
    (ha.keep.trans hb.keep).trans hc.keep
  have c0 : c.gpr .x0=doneFlag (sampleAfter [] B 168) := by
    apply BitVec.eq_of_toNat_eq
    rw [hc.keep.get .x0,hb.status,doneFlag]
    split <;> rfl
  have ct : ∀ r, r ∉ [.x2,.x3,.x4,.x5,.x9,.x10]++(.x0::Rej8.Scalar.lRegs)++[] → c.gpr r=t.gpr r :=
    fun r hr => kc.gpr r hr
  have fb : Frame [polyRegion (t.gpr .x21)] t.mem b.mem := by rw [←ha.mem]; exact hb.acc.frame
  refine ⟨(kc.trans ku.keep).mono,?_,?_,?_,?_,?_,?_,?_,?_,cu⟩
  · rw [ku.mem]
    exact (fb.mono (by simp)).trans (hc.frame.mono (by simp))
  · rw [ku.mem]; exact hc.coeffs
  · rw [ku.mem]; exact hc.checkpoint
  · rw [e22,c0,ct .x22 (by decide)]
  · rw [e20,ct .x20 (by decide)]
  · rw [e21,ct .x23 (by decide)]
  · rw [e1,ct .x1 (by decide)]
  · rw [e6,ct .x1 (by decide),ct .x19 (by decide)]

theorem one_and_doneFlag (L : List Zq) : (1 : BitVec 64) &&& doneFlag L=doneFlag L := by
  unfold doneFlag; split <;> rfl

theorem x6_after (p : Addr) (c : Nat) :
    p+BitVec.ofNat 64 c+BitVec.ofNat 64 16-p-BitVec.ofNat 64 1712=BitVec.ofNat 64 (c+16)-BitVec.ofNat 64 1712 := by
  rw [BitVec.add_assoc,VG.Offset.add_sub_cancel_left,←BitVec.ofNat_add]

/-! ## Both streams -/

/-- The state before iteration `k` of `rejectBoth`'s loop, from `s`. -/
def InitialInv (w16 : Bool) (A B : Nat→Byte) (p oA oB : Addr) (s : State) : Nat → State → Prop
  | 0, t => Keep initialRegs s t ∧ Frame (initialRegions p oA oB) s.mem t.mem ∧ Rej8.Constants t ∧
      t.gpr .x20=p+BitVec.ofNat 64 400 ∧ t.gpr .x21=oA ∧ t.gpr .x23=oB ∧
      t.gpr .x1=p+BitVec.ofNat 64 1680 ∧ t.gpr .x22=1 ∧
      Rej8.EnvW w16 168 A (p+BitVec.ofNat 64 400) oA t ∧ Rej8.EnvW w16 168 B (p+BitVec.ofNat 64 904) oB t
  | 1, t => Keep initialRegs s t ∧ Frame (initialRegions p oA oB) s.mem t.mem ∧ Rej8.Constants t ∧
      t.gpr .x20=p+BitVec.ofNat 64 904 ∧ t.gpr .x21=oB ∧
      t.gpr .x1=p+BitVec.ofNat 64 1696 ∧ t.gpr .x22=doneFlag (sampleAfter [] A 168) ∧
      Rej8.Scalar.CoeffsW w16 t.mem oA (sampleAfter [] A 168) ∧
      checkpointW w16 (p+BitVec.ofNat 64 1680) oA (sampleAfter [] A 168) t.mem ∧
      Rej8.EnvW w16 168 B (p+BitVec.ofNat 64 904) oB t
  | _, t => Keep initialRegs s t ∧ Frame (initialRegions p oA oB) s.mem t.mem ∧ Rej8.Constants t ∧
      t.gpr .x22=doneFlag (sampleAfter [] A 168) &&& doneFlag (sampleAfter [] B 168) ∧
      Rej8.Scalar.CoeffsW w16 t.mem oA (sampleAfter [] A 168) ∧
      checkpointW w16 (p+BitVec.ofNat 64 1680) oA (sampleAfter [] A 168) t.mem ∧
      Rej8.Scalar.CoeffsW w16 t.mem oB (sampleAfter [] B 168) ∧
      checkpointW w16 (p+BitVec.ofNat 64 1696) oB (sampleAfter [] B 168) t.mem

/-- What `rejectBoth` needs, beyond the two streams' environments. -/
structure InitialPre (p oA oB : Addr) (s : State) : Prop where
  ptr : s.gpr .x19=p
  scratch : Covers [⟨p,2048⟩] s.wr
  da : (polyRegion oA).Disjoint ⟨p,2048⟩
  db : (polyRegion oB).Disjoint ⟨p,2048⟩
  dab : (polyRegion oA).Disjoint (polyRegion oB)
  dt : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨p,2048⟩

theorem initialStep0_ok {w16 : Bool} {s t : State} {p oA oB : Addr} {A B : Nat→Byte}
    (h : InitialPre p oA oB s) (ht : InitialInv w16 A B p oA oB s 0 t) :
    WP isa (oneBody w16) t fun u => InitialInv w16 A B p oA oB s 1 u ∧ ((u.gpr .x6).toNat≠0 ↔ 0+1≠2) := by
  obtain ⟨kt,ft,ct,t20,t21,t23,t1,t22,ea,eb⟩ := ht
  have sA : Region.Sub ⟨p+BitVec.ofNat 64 1680,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  have tw : t.wr=s.wr := kt.wr
  have t19 : t.gpr .x19=p := (kt.get .x19).trans h.ptr
  have t16 : t.gpr .x16=s.gpr .x16 := kt.get .x16
  have ready : OneReadyR w16 A t :=
    ⟨by rw [t20,t21]; exact ea,ct,by rw [t1,tw]; exact Noise.inScratch h.scratch (by decide) (by decide),
      by rw [t1,tw,BitVec.add_assoc]; exact Noise.inScratch (off:=1688) h.scratch (by decide) (by decide),
      by rw [t1,t21]; exact h.da.sub_right sA⟩
  refine WP.mono (oneBody_ok ready) fun u hu => ?_
  have hf : Frame [polyRegion oA,⟨p+BitVec.ofNat 64 1680,16⟩] t.mem u.mem := by
    have := hu.frame; rw [t1,t21] at this; exact this
  have fu : Frame (initialRegions p oA oB) s.mem u.mem := ft.trans (hf.mono (by simp [initialRegions]))
  have eb' : Rej8.EnvW w16 168 B (p+BitVec.ofNat 64 904) oB u := by
    refine eb.frame hu.keep.rd hu.keep.wr (hu.keep.get .x16) hf ?_ ?_
    · simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨(h.da.sub_right (Offset.sub_base _ (by decide))).symm,
        Offset.disjoint p (d:=904) (n:=508) (e:=1680) (k:=16) (by decide) (by decide) (by decide)⟩
    · intro mask hm
      simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      exact ⟨ea.tableDisj mask hm,by rw [t16]; exact (h.dt mask hm).sub_right sA⟩
  have u6 : u.gpr .x6=BitVec.ofNat 64 (1680+16)-BitVec.ofNat 64 1712 := by
    rw [hu.x6,t1,t19,x6_after]
  refine ⟨⟨(kt.trans hu.keep).mono,fu,hu.constants,by rw [hu.x20,t20,ptr_add],by rw [hu.x21,t23],
    by rw [hu.x1,t1,ptr_add],by rw [hu.flag,t22,one_and_doneFlag],by rw [←t21]; exact hu.coeffs,by rw [←t21,←t1]; exact hu.saved,eb'⟩,?_⟩
  rw [u6]; decide

theorem initialStep1_ok {w16 : Bool} {s t : State} {p oA oB : Addr} {A B : Nat→Byte}
    (h : InitialPre p oA oB s) (ht : InitialInv w16 A B p oA oB s 1 t) :
    WP isa (oneBody w16) t fun u => InitialInv w16 A B p oA oB s 2 u ∧ ((u.gpr .x6).toNat≠0 ↔ 1+1≠2) := by
  obtain ⟨kt,ft,ct,t20,t21,t1,t22,ca,sa,eb⟩ := ht
  have sA : Region.Sub ⟨p+BitVec.ofNat 64 1680,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  have sB : Region.Sub ⟨p+BitVec.ofNat 64 1696,16⟩ ⟨p,2048⟩ := Offset.sub_base p (by decide)
  have tw : t.wr=s.wr := kt.wr
  have t19 : t.gpr .x19=p := (kt.get .x19).trans h.ptr
  have ready : OneReadyR w16 B t :=
    ⟨by rw [t20,t21]; exact eb,ct,by rw [t1,tw]; exact Noise.inScratch h.scratch (by decide) (by decide),
      by rw [t1,tw,BitVec.add_assoc]; exact Noise.inScratch (off:=1704) h.scratch (by decide) (by decide),
      by rw [t1,t21]; exact h.db.sub_right sB⟩
  refine WP.mono (oneBody_ok ready) fun u hu => ?_
  have hf : Frame [polyRegion oB,⟨p+BitVec.ofNat 64 1696,16⟩] t.mem u.mem := by
    have := hu.frame; rw [t1,t21] at this; exact this
  have u6 : u.gpr .x6=BitVec.ofNat 64 (1696+16)-BitVec.ofNat 64 1712 := by
    rw [hu.x6,t1,t19,x6_after]
  refine ⟨⟨(kt.trans hu.keep).mono,ft.trans (hf.mono (by simp [initialRegions])),hu.constants,
    by rw [hu.flag,t22],?_,?_,by rw [←t21]; exact hu.coeffs,by rw [←t21,←t1]; exact hu.saved⟩,?_⟩
  · refine coeffs_frame ca (sampleAfter_length_le (by decide) A 168) hf ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨h.dab,h.da.sub_right sB⟩
  · refine checkpoint_frame sa hf ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨(h.db.sub_right sA).symm,Offset.disjoint p (by decide) (by decide) (by decide)⟩
  · rw [u6]; decide

/-- `rejectBoth`'s start: both outputs, the first stream's pointers and the flag. -/
theorem initialStart_ok {w16 : Bool} {s : State} {a b : Nat} (ha : a<65536) (hb : b<65536)
    {A B : Nat→Byte}
    (pa : Rej8.EnvW w16 168 A (s.gpr .x19+BitVec.ofNat 64 400) (s.gpr .x28+BitVec.ofNat 64 a) s)
    (pb : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 904) (s.gpr .x28+BitVec.ofNat 64 b) s)
    (hc : Rej8.Constants s) :
    WP isa (.block (ptrTo .x21 .x28 a ++ ptrTo .x23 .x28 b ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0] : List Instr))) s
      (InitialInv w16 A B (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x28+BitVec.ofNat 64 b) s 0) := by
  have blk : WP isa (.block (ptrTo .x21 .x28 a ++ ptrTo .x23 .x28 b ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0] : List Instr))) s fun t =>
      Only ([.x21]++[.x23]++[.x20]++[.x1]++[.x22]) s t ∧ t.gpr .x20=s.gpr .x19+BitVec.ofNat 64 400 ∧
        t.gpr .x21=s.gpr .x28+BitVec.ofNat 64 a ∧ t.gpr .x23=s.gpr .x28+BitVec.ofNat 64 b ∧
        t.gpr .x1=s.gpr .x19+BitVec.ofNat 64 1680 ∧ t.gpr .x22=1 := by
    rw [List.append_assoc]
    refine wp_ptrTo (by decide) ha fun t₁ k₁ e₁ => wp_ptrTo (by decide) hb fun t₂ k₂ e₂ =>
      wp_addImm (by decide) fun t₃ k₃ e₃ => wp_addImm (by decide) fun t₄ k₄ e₄ =>
      wp_movz fun t k₅ e₅ => wp_nil ⟨(((k₁.trans k₂).trans k₃).trans k₄).trans k₅,?_,?_,?_,?_,?_⟩
    · rw [k₅.get .x20,k₄.get .x20,e₃,k₂.get .x19,k₁.get .x19]
    · rw [k₅.get .x21,k₄.get .x21,k₃.get .x21,k₂.get .x21,e₁]
    · rw [k₅.get .x23,k₄.get .x23,k₃.get .x23,e₂,k₁.get .x28]
    · rw [k₅.get .x1,e₄,k₃.get .x19,k₂.get .x19,k₁.get .x19]
    · rw [e₅]; rfl
  refine WP.mono (Rej8.WP.constants blk hc (by unfold ptrTo; split <;> split <;> rfl))
    fun t ⟨⟨kt,t20,t21,t23,t1,t22⟩,ct⟩ => ?_
  refine ⟨kt.keep.mono,by rw [kt.mem]; exact Frame.refl _ _,ct,t20,t21,t23,t1,t22,?_,?_⟩
  · exact pa.transfer kt.mem kt.rd kt.wr (kt.get .x16)
  · exact pb.transfer kt.mem kt.rd kt.wr (kt.get .x16)

theorem initial_ok {w16 : Bool} {s : State} {a b : Nat} (ha : a<65536) (hb : b<65536)
    {A B : Nat→Byte}
    (pa : Rej8.EnvW w16 168 A (s.gpr .x19+BitVec.ofNat 64 400) (s.gpr .x28+BitVec.ofNat 64 a) s)
    (pb : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 904) (s.gpr .x28+BitVec.ofNat 64 b) s)
    (hc : Rej8.Constants s) (hs : Covers [⟨s.gpr .x19,2048⟩] s.wr)
    (da : (polyRegion (s.gpr .x28+BitVec.ofNat 64 a)).Disjoint ⟨s.gpr .x19,2048⟩)
    (db : (polyRegion (s.gpr .x28+BitVec.ofNat 64 b)).Disjoint ⟨s.gpr .x19,2048⟩)
    (dab : (polyRegion (s.gpr .x28+BitVec.ofNat 64 a)).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 b)))
    (dt : ∀mask<256,(Region.mk (s.gpr .x16+BitVec.ofNat 64 (16*mask)) 16).Disjoint ⟨s.gpr .x19,2048⟩) :
    WP isa (initialCode a b w16) s
      (InitialPostW w16 A B (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x28+BitVec.ofNat 64 b) s) := by
  have pre : InitialPre (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x28+BitVec.ofNat 64 b) s :=
    ⟨rfl,hs,da,db,dab,dt⟩
  refine WP.seq (WP.mono (initialStart_ok ha hb pa pb hc) fun t i0 => ?_)
  refine WP.seq (WP.mono (count_loop (n:=2) (cr:=.x6) (body:=oneBody w16) (by decide)
    (InitialInv w16 A B (s.gpr .x19) (s.gpr .x28+BitVec.ofNat 64 a) (s.gpr .x28+BitVec.ofNat 64 b) s)
    (fun k hk v hv => ?_) i0) fun u hu => ?_)
  · rcases (show k=0 ∨ k=1 by omega) with rfl|rfl
    · exact initialStep0_ok pre hv
    · exact initialStep1_ok pre hv
  obtain ⟨ku,fu,cu,u22,ca,sa,cb,sb⟩ := hu
  have fin : WP isa (.block [mov .x6 .x22]) u fun v => Only [.x6] u v ∧ v.gpr .x6=u.gpr .x22 :=
    wp_mov fun v kv ev => wp_nil ⟨kv,ev⟩
  refine WP.mono (Rej8.WP.constants fin cu (by rfl)) fun v ⟨⟨kv,ev⟩,cv⟩ => ?_
  refine ⟨(ku.trans kv.keep).mono,by rw [kv.mem]; exact fu,by rw [kv.mem]; exact ca,
    by rw [kv.mem]; exact cb,by rw [kv.mem]; exact sa,by rw [kv.mem]; exact sb,?_,cv⟩
  rw [ev,u22]; unfold doneFlag; (repeat' split) <;> simp_all

end VG.Proof.MlKem.AArch64.Paired
