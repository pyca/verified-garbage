import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalLoop

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
    exact ⟨hra _ (by omega),hrb _ (by omega)⟩
  · intro u hu i
    simp only [hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hw _ (by omega)
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
      omega
    · have hc0' : c.gpr .x0=s.gpr .x0 := by rw [hc0,hb0']; bv_omega
      have hc2' : c.gpr .x2=s.gpr .x0 := by rw [hc2,hb0']; bv_omega
      refine WP.mono (productFinal_ok raw hfc hsc hc12 ?_ ?_) fun t ⟨hkt,hmt⟩ => ?_
      · intro u hu i
        simp only [hkc.rd,hkc.wr,hkb.rd,hkb.wr,hka.rd,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hr _ (by omega)
      · intro u hu i
        simp only [hkc.wr,hkb.wr,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hw _ (by omega)
      · refine ⟨(((hka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
        · rw [hkt.get .x0 (by decide),hc0']
        · simpa only [multiplyInverseMem,hmc,hmb',hc2'] using hmt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
