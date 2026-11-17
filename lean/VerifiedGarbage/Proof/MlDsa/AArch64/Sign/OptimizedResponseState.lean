module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductInit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductFullTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
public import VerifiedGarbage.Proof.MlDsa.RawInverseContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK

/-! ### `MlDsa.AArch64.Optimized.ProductCallTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductSat`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductCore`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ProductFirstLoop`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)

def productAdvance : List Instr :=
  [.addImm .x .x13 .x13 128,.addImm .x .x14 .x14 128] ++ firstAdvance

theorem productAdvance_ok (s : State) :
    WP isa (.block productAdvance) s fun t =>
      ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧
        t.gpr .x13=s.gpr .x13+128 ∧ t.gpr .x14=s.gpr .x14+128 ∧
        t.gpr .x11=s.gpr .x11-1 ∧ t.mem=s.mem) ∧
        Keep [.x0,.x1,.x11,.x13,.x14] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold productAdvance firstAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem productBlock_eq : VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.firstBlock=
    productFiveCode++productAdvance := by kernel_rfl

theorem productFirstLoop_ok {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x13)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x14)).Disjoint (outputRegion (s.gpr .x0)))
    (hc : s.gpr .x11=8) (hq : ProductConstants s)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀ u<8, ∀ i : Fin 8,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (productFiveCode++productAdvance)) (.nonzero .x .x11)) s fun t =>
      Keep [.x0,.x1,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=productPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 := by
  let I := fun u t => Keep [.x0,.x1,.x11,.x13,.x14] s t ∧ ProductConstants t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.gpr .x13=s.gpr .x13+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x14=s.gpr .x14+BitVec.ofNat 64 (128*u) ∧
    t.mem=productPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hp13,hp14,hm⟩
    have hf : Frame [outputRegion (s.gpr .x0)] s.mem t.mem := by
      rw [hm]; exact productPass_frame (by omega_using [hu])
    have ht' : InverseTable.Words t.mem (s.gpr .x1) :=
      tableWords_frame ht hf (by simpa only [List.mem_singleton,forall_eq,tableRegion] using hd)
    have hrt' : ∀ off, off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    have hqword : ∀ e<4, vword (t.v .v31) e=8380417#32 := by
      intro e he
      rw [hqt.qv,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
      have heq : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega_using [he]
      rcases heq with rfl | rfl | rfl | rfl <;> rfl
    refine productFive_ok u (fun j e he => productValues_input hu hf ha hb hp13 hp14 j he) hqt
      (packed_tableRoots hu ht' hrt' hp1 hqword) (local_tableRoots hu ht' hrt' hp1 hqword)
      ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro j hj
      simpa only [hk.rd,hk.wr,hp13,hp14] using hr u hu ⟨j,hj⟩
    · intro i
      simpa only [hk.wr,hp0] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (productAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hp₄,hp₅,hc₂,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_,?_,?_⟩,?_⟩
      · exact ⟨by rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]; exact hqt.qv,
          by rw [hvec₂,hv₁.v,hv.get .v30 (by decide)]; exact hqt.qiv⟩
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₄,hk₁.get .x13,hp13]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₅,hk₁.get .x14,hp14]
        rw [show 128*(u+1)=128*u+128 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hm₂,hv₁.mem]
        simp only [hm,hp0,productPassMem]
      · rw [hc₂,hk₁.get .x11]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)

def productCoreRegs : List Reg := coreRegs ++ [.x10,.x13,.x14]
def productFinalMem (raw : Bool) (m : Mem) (p : Addr) : Mem :=
  if raw then rawFinalPassMem m p 8 else finalPassMem m p (HighPack.repeatedWord 8380417) 8
def multiplyInverseMem (raw : Bool) (m : Mem) (p a b : Addr) : Mem :=
  productFinalMem raw (productPassMem m p a b 8) p

theorem productFinal_ok (raw : Bool) {s : State} (hf : FinalRoots s) (hs : ScaleRoots s)
    (hc : s.gpr .x12=8)
    (hr : ∀ u<8, ∀ i : Fin 8, InRegions (s.rd++s.wr)
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ u<8, ∀ i : Fin 8, InRegions s.wr
      ((s.gpr .x2+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    WP isa (.loop (.block (if raw then VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.rawFinalBody
      else VG.Impl.MlDsa.AArch64.Optimized.Inverse.finalBody)) (.nonzero .x .x12)) s fun t =>
      Keep [.x2,.x12] s t ∧ t.mem=productFinalMem raw s.mem (s.gpr .x2) := by
  cases raw with
  | false =>
    simp only [Bool.false_eq_true,ite_false,finalBody_eq]
    refine WP.mono (finalLoop_ok hf hs hc hr hw) fun t ⟨hk,_,_,hm⟩ => ?_
    exact ⟨hk,by simpa only [productFinalMem,Bool.false_eq_true,ite_false,qVector_eq hf.q] using hm⟩
  | true =>
    simp only [ite_true,rawFinalBody_eq]
    exact WP.mono (rawFinalLoop_ok hf hs hc hr hw) fun t h => ⟨h.1,h.2.2.2⟩

theorem productCore_eq (raw : Bool) : VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.core raw=
    .seq (.block productInit) (.seq
      (.loop (.block (productFiveCode++productAdvance)) (.nonzero .x .x11))
      (.seq (.block middleCode) (.loop (.block (if raw then VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.rawFinalBody
        else VG.Impl.MlDsa.AArch64.Optimized.Inverse.finalBody)) (.nonzero .x .x12)))) := by
  rw [← productBlock_eq]
  rfl

theorem productCore_ok (raw : Bool) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x13)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x14)).Disjoint (outputRegion (s.gpr .x0)))
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hra : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16)
    (hrb : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    (hr : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀ off, off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.core raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) := by
  rw [productCore_eq]
  apply WP.seq
  refine WP.mono (productInit_ok s) fun a ⟨hka,hma,h11,hqa⟩ => ?_
  have ha0 : a.gpr .x0=s.gpr .x0 := hka.get .x0 (by decide)
  have ha1 : a.gpr .x1=s.gpr .x1 := hka.get .x1 (by decide)
  have ha13 : a.gpr .x13=s.gpr .x13 := hka.get .x13 (by decide)
  have ha14 : a.gpr .x14=s.gpr .x14 := hka.get .x14 (by decide)
  apply WP.seq
  refine WP.mono (productFirstLoop_ok (s := a) ?_ ?_ ?_ ?_ h11 hqa ?_ ?_ ?_)
    fun b ⟨hkb,hqb,hb0,hb1,_,_,hmb⟩ => ?_
  · simpa only [hma,ha1] using ht
  · simpa only [ha0,ha1] using hd
  · simpa only [ha0,ha13] using ha
  · simpa only [ha0,ha14] using hb
  · simpa only [hka.rd,hka.wr,ha1] using hrt
  · intro u hu i
    simp only [hka.rd,hka.wr,ha13,ha14,BitVec.add_assoc,← BitVec.ofNat_add]
    exact ⟨hra _ (by omega_using [hu]),hrb _ (by omega_using [hu])⟩
  · intro u hu i
    simp only [hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hw _ (by omega_using [hu])
  · have hb0' : b.gpr .x0=s.gpr .x0+1024 := by simpa only [ha0] using hb0
    have hb1' : b.gpr .x1=s.gpr .x1+3840 := by simpa only [ha1] using hb1
    have hmb' : b.mem=productPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) 8 := by
      simpa only [hma,ha0,ha13,ha14] using hmb
    have htb : InverseTable.Words b.mem (s.gpr .x1) := by
      rw [hmb']
      exact tableWords_frame ht (productPass_frame (by decide)) (by
        simpa only [List.mem_singleton,forall_eq,tableRegion] using hd)
    have hqword : ∀ e<4, vword (b.v .v31) e=8380417#32 := by
      intro e he
      rw [hqb.qv]
      exact HighPack.repeatedWord_lane _ he
    apply WP.seq
    refine WP.mono (middle_ok (s := b) htb hb1' ?_ hqword) fun c ⟨hkc,hmc,hc0,hc2,hc12,hfc,hsc⟩ => ?_
    · intro off hoff
      simp only [hkb.rd,hkb.wr,hka.rd,hka.wr,hb1']
      change InRegions (s.rd++s.wr) ((s.gpr .x1+BitVec.ofNat 64 3840)+BitVec.ofNat 64 off) 16
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      apply hrt
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
      omega_using [hoff]
    · have hc0' : c.gpr .x0=s.gpr .x0 := by rw [hc0,hb0']; bv_omega_arith
      have hc2' : c.gpr .x2=s.gpr .x0 := by rw [hc2,hb0']; bv_omega_arith
      refine WP.mono (productFinal_ok raw hfc hsc hc12 ?_ ?_) fun t ⟨hkt,hmt⟩ => ?_
      · intro u hu i
        simp only [hkc.rd,hkc.wr,hkb.rd,hkb.wr,hka.rd,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hr _ (by omega_using [hu])
      · intro u hu i
        simp only [hkc.wr,hkb.wr,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hw _ (by omega_using [hu])
      · refine ⟨(((hka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
        · rw [hkt.get .x0 (by decide),hc0']
        · simpa only [multiplyInverseMem,hmc,hmb',hc2'] using hmt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


/-! ## From `ProductStatic.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlKem.AArch64 (mov)

theorem multiplyInverseMem_frame (raw : Bool) (m : Mem) (p a b : Addr) :
    Frame [outputRegion p] m (multiplyInverseMem raw m p a b) := by
  apply (productPass_frame (m := m) (p := p) (a := a) (b := b) (u := 8) (by decide)).trans
  cases raw with
  | false => exact finalPass_frame (by decide)
  | true => exact rawFinalPass_frame (by decide)

theorem productCore_words_ok (raw : Bool) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (htr : tableRegion (s.gpr .x1)∈s.rd++s.wr)
    (har : polyRegion (s.gpr .x13)∈s.rd++s.wr)
    (hbr : polyRegion (s.gpr .x14)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x13)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x14)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.core raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) := by
  refine WP.mono (productCore_ok raw ht hsep ha hb ?_ ?_ ?_ ?_ ?_) fun t ⟨hk,hp,hm⟩ => ?_
  · intro off ho; exact ⟨_,htr,Offset.contains_base _ ho (by omega_using [ho])⟩
  · intro off ho; exact ⟨_,har,Offset.contains_base _ ho (by omega_using [ho])⟩
  · intro off ho; exact ⟨_,hbr,Offset.contains_base _ ho (by omega_using [ho])⟩
  · intro off ho; exact ⟨_,List.mem_append_right _ hw,Offset.contains_base _ ho (by omega_using [ho])⟩
  · intro off ho; exact ⟨_,hw,Offset.contains_base _ ho (by omega_using [ho])⟩
  · exact ⟨hk,hp,by rw [hm]; exact multiplyInverseMem_frame _ _ _ _ _,hm⟩

theorem productStaticInit_ok (s : State) :
    WP isa (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) s fun t =>
      (t.gpr .x13=s.gpr .x1 ∧ t.gpr .x14=s.gpr .x2 ∧
        t.gpr .x1=s.syms "VG_MLDSA_INV_FOLDED" ∧ t.mem=s.mem) ∧ Keep [.x1,.x13,.x14] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold mov
  arun [exec_adrSym]
  rfl

theorem productStatic_words_ok (raw : Bool) {s : State}
    (ht : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED"))
    (htr : tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr)
    (har : polyRegion (s.gpr .x1)∈s.rd++s.wr)
    (hbr : polyRegion (s.gpr .x2)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x2)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode
  refine WP.seq (WP.mono (productStaticInit_ok s) fun a ⟨⟨h13,h14,h1,hm⟩,hk⟩ => ?_)
  have ht' : InverseTable.Words a.mem (a.gpr .x1) := by simpa only [h1,hm] using ht.words
  have h0 : a.gpr .x0=s.gpr .x0 := hk.get .x0 (by decide)
  refine WP.mono (productCore_words_ok raw ht' ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hpt,hft,hmt⟩ => ?_
  · simpa only [h1,hk.rd,hk.wr] using htr
  · simpa only [h13,hk.rd,hk.wr] using har
  · simpa only [h14,hk.rd,hk.wr] using hbr
  · simpa only [h0,hk.wr] using hw
  · simpa only [h1,h0] using hsep
  · simpa only [h13,h0] using ha
  · simpa only [h14,h0] using hb
  · exact ⟨(hk.trans hkt).mono,hpt.trans h0,
      by simpa only [hm,h0] using hft,
      by simpa only [hm,h0,h13,h14] using hmt⟩

theorem productCoreKeep_abi {s t : State} (h : Keep productCoreRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def productRawK : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    polyRegion (s.gpr .x1)∈s.rd++s.wr ∧ polyRegion (s.gpr .x2)∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x2)).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧
    PositiveReduced s.mem (s.gpr .x1) ∧ PositiveReduced s.mem (s.gpr .x2)
  post s t := RawPolyIs t.mem (s.gpr .x0)
    (nttInv (multiplyNTT (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2))))
  pub s t := (∀ r∈[Reg.x0,.x1,.x2], s.gpr r=t.gpr r) ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem productRaw_pre {s : State}
    (h : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre s) : productRawK.pre s := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,
    inverseConsts_eq,Abi.withConsts,Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,_,ht,hw,hoa,hob,_,_,_,_,_,_,_,hpa,hpb⟩ := h
  have hrd : s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2),tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hrd]; simp,by rw [hrd]; simp,
    by rw [hw]; simp [outputRegion],?_,hoa.symm,hob.symm,?_,hpa,hpb⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))

theorem productRaw_ct : ConstantTime isa productRawK.pre productRawK.pub
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply productStatic_ct true s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 hp.1,?_⟩
  intro name hn
  have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
  subst name; exact hp.2.2

theorem productRaw_pub {s t : State}
    (h : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pub s t) : productRawK.pub s t := by
  sig_pub [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  refine ⟨?_,h.1,h.2.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def productSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 8192 else if r=.x1 ∨ r=.x2 then 4096 else if r=.x3 then 12288 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨4096,1024⟩,⟨65536,3904⟩]
  wr := [⟨8192,1024⟩,⟨12288,1024⟩]

theorem reduced_positive {m : Mem} {p : Addr} (h : Reduced m p) : PositiveReduced m p := by
  intro i hi
  exact Nat.lt_trans (h i hi) (by decide : q<3*q)

theorem inverseSat_positive : PositiveReduced inverseSat.mem (4096 : Addr) := by
  apply reduced_positive
  exact inverseSat_reduced

theorem productRaw_spec_pre {s : State}
    (hrd : s.rd=[⟨s.gpr .x1,1024⟩,⟨s.gpr .x2,1024⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩])
    (hwr : s.wr=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x3,1024⟩])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈s.wr, (⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩ : Region).Disjoint r)
    (hal : (s.syms "VG_MLDSA_INV_FOLDED").toNat%64=0)
    (h01 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x1,1024⟩)
    (h02 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x2,1024⟩)
    (h03 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (h13 : (⟨s.gpr .x1,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (h23 : (⟨s.gpr .x2,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (hf0 : (s.gpr .x0).toNat+1024≤2^64) (hf1 : (s.gpr .x1).toNat+1024≤2^64)
    (hf2 : (s.gpr .x2).toNat+1024≤2^64) (hf3 : (s.gpr .x3).toNat+1024≤2^64)
    (ha : PositiveReduced s.mem (s.gpr .x1)) (hb : PositiveReduced s.mem (s.gpr .x2)) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre s := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,
    inverseConsts_eq,Abi.withConsts,Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  exact ⟨by rw [hrd]; rfl,held,hfit,hsep,hal,by rw [hrd]; rfl,hwr,h01,h02,h03,h13,h23,hf0,hf1,hf2,hf3,ha,hb⟩

theorem productSatWith_pre (m : Mem)
    (held : ∀ i<488,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hpos : PositiveReduced m 4096) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre (productSatWith m) := by
  apply productRaw_spec_pre (s := productSatWith m) rfl rfl held (by dsimp only [productSatWith]; decide) ?_
    (by dsimp only [productSatWith]; decide)
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide))
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide))
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide)
    hpos hpos
  intro r hr
  change r∈[⟨8192,1024⟩,⟨12288,1024⟩] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)

def productSat : State := productSatWith inverseSat.mem

theorem productRaw_sat : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre productSat :=
  productSatWith_pre inverseSat.mem inverseSat_held inverseSat_positive

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem productRaw_correct (s : State) (hp : productRawK.pre s) :
    ∃ trace t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) s trace t ∧
      abiPreserved s t ∧ productRawK.post s t := by
  obtain ⟨htr,har,hbr,hw,hsep,ha,hb,ht,hpa,hpb⟩ := hp
  obtain ⟨tr,t,he,hk,_,_,hm⟩ := productStatic_words_ok true ht htr har hbr hw hsep ha hb
  have hv := productRawInverse_contract_field (p := s.gpr .x0) hpa hpb
  change RawPolyIs (multiplyInverseMem true s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)) _ _ at hv
  rw [← hm] at hv
  exact ⟨tr,t,he,productCoreKeep_abi hk,hv⟩

/-- Exact measured raw helper, with explicit signed bounds and secret coefficients. -/
theorem productRaw_verified : Verified target
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
    (multiplyInverseRawContract (abi.withConsts inverseConsts)) := by
  refine Verified.of_correct productRaw_correct productRaw_ct
    { pre := fun _ h => productRaw_pre h,post := ?_,pub := ?_,sat := ⟨productSat,productRaw_sat⟩ }
  · intro s t _ h
    sig_post [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    exact h
  · intro s t _ _ h
    exact productRaw_pub h

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end


/-! ## From `ProductCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts expandedWords)

theorem productRaw_callee (S : Nat) :
    CalleeOk S (staticCode true) (multiplyInverseRawContract (abi.withConsts inverseConsts)) := by
  refine CalleeOk.of_ct (productRaw_verified).1 (productRaw_verified).2.1 (by lit_decide) (fun _ _ h => h) ?_
  change 0≤S
  exact Nat.zero_le _

abbrev productArgs (out a b scratch : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.ptr scratch)]

structure ProductCallReady (out a b scratch : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  scratchFit : (pa s scratch).toNat+1024≤2^64
  held : ∀i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64
  tableApart : ∀r∈[outputRegion (pa s out),outputRegion (pa s scratch)],
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r
  outA : (outputRegion (pa s out)).Disjoint (outputRegion (pa s a))
  outB : (outputRegion (pa s out)).Disjoint (outputRegion (pa s b))
  outScratch : (outputRegion (pa s out)).Disjoint (outputRegion (pa s scratch))
  aScratch : (outputRegion (pa s a)).Disjoint (outputRegion (pa s scratch))
  bScratch : (outputRegion (pa s b)).Disjoint (outputRegion (pa s scratch))
  positiveA : PositiveReduced s.mem (pa s a)
  positiveB : PositiveReduced s.mem (pa s b)
  readable : Covers ([outputRegion (pa s a),outputRegion (pa s b),
    tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]++[outputRegion (pa s out),outputRegion (pa s scratch)]) (s.rd++s.wr)
  writable : Covers [outputRegion (pa s out),outputRegion (pa s scratch)] s.wr
  tableAligned : (s.syms "VG_MLDSA_INV_FOLDED").toNat%64=0

theorem productAt_pre {s s1 : State} {out a b scratch : Ptr}
    (h : ProductCallReady out a b scratch s) (h1 : Args (productArgs out a b scratch) s s1)
    (hy : s1.syms=s.syms) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre
      (s1.callEntry.withRegions [outputRegion (pa s a),outputRegion (pa s b),
        tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
        [outputRegion (pa s out),outputRegion (pa s scratch)]) := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,
    Args.mem h1,Arg.val]
  exact ⟨rfl,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableAligned,rfl,rfl,h.outA,h.outB,h.outScratch,h.aScratch,
    h.bScratch,h.outFit,h.aFit,h.bFit,h.scratchFit,h.positiveA,h.positiveB⟩

theorem productArgs_ok {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok) :
    ∀x∈productArgs out a b scratch,x.2.Ok ∧ x.1∈argRegs := by
  simp only [productArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨hs,by simp⟩

theorem productAt_ok {S : Nat} (hS : S<2^64)
    {nm : String} {s : State} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    (h : ProductCallReady out a b scratch s) :
    WP isa (callAt nm (staticCode true) (productArgs out a b scratch)) s fun t =>
      Post S s t [outputRegion (pa s out),outputRegion (pa s scratch)] ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT
        (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b)))) := by
  refine WP.mono (callAtSyms_ok hS (productRaw_callee S) (productArgs_ok ho ha hb hs) (by simp)
    (fun s1 h1 hy => productAt_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse

/-- Product coefficient values remain secret across the complete call. -/
theorem productAt_tr {S : Nat}
    {nm : String} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → ProductCallReady out a b scratch x ∧ ProductCallReady out a b scratch y ∧
      pa x out=pa y out ∧ pa x a=pa y a ∧ pa x b=pa y b ∧ pa x scratch=pa y scratch ∧
      x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (callAt nm (staticCode true) (productArgs out a b scratch)) fun _ _ => True := by
  refine callAtSyms_tr (productRaw_callee S) (productArgs_ok ho ha hb hs) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,eo,ea,eb,es,esp,et⟩ := hQ x y hp
  refine ⟨[outputRegion (pa x a),outputRegion (pa x b),
    tableRegion (x.syms "VG_MLDSA_INV_FOLDED")],[outputRegion (pa x out),outputRegion (pa x scratch)],
    productAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb,es,et]
    exact productAt_pre ry h2 hy2
  · sig_pub [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,eo,ea,eb,es⟩
  · rw [eo,ea,eb,es,et]; exact ry.readable
  · rw [eo,es]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


/-! ## From `OptimizedProduct.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response-product call uses two positive NTT inputs and writes only
its result and the existing scratch slot. Static roots stay explicit. -/
theorem productReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (hwo : inB wbs out 1024=true) (hws : inB wbs scratch 1024=true)
    (hoa : sepB rbs wbs out 1024 a 1024=true)
    (hob : sepB rbs wbs out 1024 b 1024=true)
    (hos : sepB rbs wbs out 1024 scratch 1024=true)
    (has : sepB rbs wbs a 1024 scratch 1024=true)
    (hbs : sepB rbs wbs b 1024 scratch 1024=true)
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=
      VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈[Inverse.outputRegion (pa s out),Inverse.outputRegion (pa s scratch)],
      (Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r)
    (ht : Covers [Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] (s.rd++s.wr))
    (hpa : PositiveReduced s.mem (pa s a)) (hpb : PositiveReduced s.mem (pa s b))
    (hal : (s.syms "VG_MLDSA_INV_FOLDED").toNat%64=0) :
    Inverse.ProductCallReady out a b scratch s := by
  refine ⟨L.nwp ho,L.nwp ha,L.nwp hb,L.nwp hs,held,hfit,hsep,
    L.disj hoa,L.disj hob,L.disj hos,L.disj has,L.disj hbs,hpa,hpb,?_,?_,hal⟩
  · exact Covers.cons (L.cR ha) (Covers.cons (L.cR hb)
      (Covers.cons ht (Covers.cons (L.cR ho) (L.cR hs))))
  · exact Covers.cons (L.cW hwo) (L.cW hws)

/-- Fused challenge multiplication and inverse transform for z/r0/h. The
signed result is intentionally not coerced to the canonical PolyIs contract. -/
theorem productAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.ProductCallReady out a b scratch s) :
    WP isa (callAt "vg_mldsa_multiply_inverse_raw"
      (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
      (Inverse.productArgs out a b scratch)) s fun t =>
      PPostB S s t [(out,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b)))) := by
  refine WP.mono (Inverse.productAt_ok L.s64 (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs ha))
    (ptr_ok (L.ptrBs hb)) (ptr_ok (L.ptrBs hs)) h) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩

/-- Field-valued response boundary for a transformed challenge and secret. -/
theorem productAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr} {f g : Poly}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.ProductCallReady out a b scratch s)
    (hf : PosPolyIs s.mem (pa s a) f) (hg : PosPolyIs s.mem (pa s b) g) :
    WP isa (callAt "vg_mldsa_multiply_inverse_raw"
      (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
      (Inverse.productArgs out a b scratch)) s fun t =>
      PPostB S s t [(out,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT f g)) := by
  refine WP.mono (productAt_layout L ho ha hb hs h) fun t ⟨hp,h24,hv⟩ => ?_
  exact ⟨hp,h24,by simpa only [hf.value,hg.value] using hv⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedResponseProduct.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def responseProductChk (p : Params) (out secret : Ptr) : Bool :=
  inB (sgB p) out 1024 && inB (sgB p) cP 1024 && inB (sgB p) secret 1024 &&
  inB (sgB p) (sc oPS) 1024 && inB (sgW p) out 1024 && inB (sgW p) (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) out 1024 cP 1024 && sepB (sgR p) (sgW p) out 1024 secret 1024 &&
  sepB (sgR p) (sgW p) out 1024 (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) cP 1024 (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) secret 1024 (sc oPS) 1024

theorem responseProductChk_z {p : Params} (hp : Ok3 p) :
    ∀r<p.ℓ,responseProductChk p t1P (s1P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_r0 {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t1P (s2P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProduct_ok {p : Params} {S : Nat} {σ s : State} {out secret : Ptr} {f g : Poly}
    (hs : RootedSt p S σ s) (hc : responseProductChk p out secret=true)
    (hf : PosPolyIs s.mem (pa s cP) f) (hg : PosPolyIs s.mem (pa s secret) g) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.responseProduct out secret) s fun t =>
      PPostB S s t [(out,1024),(sc oPS,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT f g)) := by
  simp only [responseProductChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho,ha⟩,hb⟩,hsc⟩,hwo⟩,hws⟩,hoa⟩,hob⟩,hos⟩,has⟩,hbs⟩ := hc
  refine productAt_field_layout hs.1.lay ho ha hb hsc ?_ hf hg
  refine productReady_layout hs.1.lay ho ha hb hsc hwo hws hoa hob hos has hbs
    hs.2.inverse.held hs.2.inverse.fit ?_ hs.2.inverse.readable hf.bound hg.bound hs.2.inverse.aligned
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hwo)
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hws)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedResponseState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

/-- Signed response storage remains explicit until accepted output. -/
def SignedFam (s : State) (b m : Nat) (f : Nat → Poly) (lo hi : Int) : Prop :=
  ∀j<m,SignedPl s (b+j) (f j) lo hi

theorem SignedFam.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s u : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (hP : PPostB S s u ws) (hc : famChk rbs wbs ws b m=true)
    (h : SignedFam s b m f lo hi) : SignedFam u b m f lo hi :=
  fun j hj => keepSignedPoly L hP (famChk_one hc hj) (h j hj)

theorem SignedFam.snoc {s : State} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (h : SignedFam s b m f lo hi) (ht : SignedPl s (b+m) (f m) lo hi) :
    SignedFam s b (m+1) f lo hi := by
  intro j hj
  rcases (by omega_using [hj] : j<m ∨ j=m) with hj | rfl
  · exact h j hj
  · exact ht

structure PositiveKB (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : PositiveIL p S σ t s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ (p.ℓ*t)
  c : PosPl s 0 (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t)))
  sampled : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome

theorem PositiveKB.step {p : Params} {S : Nat} {σ s u : State} {t : Nat}
    (h : PositiveKB p S σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : kbChk p ws=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveKB p S σ t u := by
  simp only [kbChk,Bool.and_eq_true] at hc
  exact ⟨h.l.step hP hy hc.1.1 hw,(h.l.st.lay.keepBytes hP hc.1.2).trans h.ct,
    h.c.keep h.l.st.lay hP hc.2,h.sampled⟩

structure PositiveIZb (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : PositiveKB p S σ t s
  z : SignedFam s (yBase p) r (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1)
  y : Fam s (yBase p+r) (p.ℓ-r) fun j => Yv p σ (p.ℓ*t) (r+j)
  w : Fam s (wBase p) p.k (Wv p σ (p.ℓ*t))
  ones : s.mem.readW (pa s (sc oONES)) 64=0

def PositiveIZ (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  PositiveIZb p S σ t r s ∧
    s.gpr .x24=bit (∀j<r,normRq [Zv p σ (p.ℓ*t) j]<p.γ₁-p.β)

theorem PositiveIZb.step {p : Params} {S : Nat} {σ s u : State} {t r : Nat}
    (h : PositiveIZb p S σ t r s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : zfam p ws r=true)
    (hys : famChk (sgR p) (sgW p) ws (yBase p+r) (p.ℓ-r)=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIZb p S σ t r u := by
  simp only [zfam,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP hy h1 hw,h.z.keep L hP h2,h.y.keep L hP hys,h.w.keep L hP h3,
    (L.keepW hP h4).trans h.ones⟩

end VG.Proof.MlDsa.AArch64.Sign

end
