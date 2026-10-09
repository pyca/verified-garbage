import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMiddle
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def dotCoreRegs : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11,.x12,.x13,.x14]

def dotInverseMem (m : Mem) (p a b : Addr) (count : Nat) : Mem :=
  finalPassMem (dotPassMem m p a b count 8) p (HighPack.repeatedWord 8380417) 8

theorem dotCore_eq (count : Nat) : VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count=
    .seq (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) (.seq
      (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count)) (.nonzero .x .x11))
      (.seq (.block middleCode) (.loop (.block (finalSliceCode++finalAdvance)) (.nonzero .x .x12)))) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core
  rw [finalBody_eq]
  rfl

/-- The standalone inverse executes the selected two-pass memory transform.
Only table and buffer accessibility are required at this machine boundary. -/
theorem dotCore_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hrt : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hra : ∀ off, off+16≤1024*count → InRegions (s.rd++s.wr) (s.gpr .x13+BitVec.ofNat 64 off) 16)
    (hrb : ∀ off, off+16≤1024*count → InRegions (s.rd++s.wr) (s.gpr .x14+BitVec.ofNat 64 off) 16)
    (hr : ∀ off, off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀ off, off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.core count) s fun t =>
      Keep dotCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧ t.mem=dotInverseMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count := by
  rw [dotCore_eq]
  apply WP.seq
  refine WP.mono (dotSetup_ok s) fun a ⟨hka,hma,h11,hqa⟩ => ?_
  have ha0 : a.gpr .x0=s.gpr .x0 := hka.get .x0 (by decide)
  have ha1 : a.gpr .x1=s.gpr .x1 := hka.get .x1 (by decide)
  have ha13 : a.gpr .x13=s.gpr .x13 := hka.get .x13 (by decide)
  have ha14 : a.gpr .x14=s.gpr .x14 := hka.get .x14 (by decide)
  apply WP.seq
  refine WP.mono (dotLoop_ok hn hn7 (s := a) ?_ ?_ h11 hqa ?_ ?_ ?_) fun b ⟨hkb,hqb,hb0,hb1,_,_,hmb⟩ => ?_
  · simpa only [hma,ha1] using ht
  · simpa only [ha0,ha1] using hd
  · simpa only [hka.rd,hka.wr,ha1] using hrt
  · intro u hu j hj k hk
    simp only [hka.rd,hka.wr,ha13,ha14,BitVec.add_assoc,← BitVec.ofNat_add]
    exact ⟨hra _ (by omega),hrb _ (by omega)⟩
  · intro u hu i
    simp only [hka.wr,ha0,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hw _ (by omega)
  · have hb0' : b.gpr .x0=s.gpr .x0+1024 := by simpa only [ha0] using hb0
    have hb1' : b.gpr .x1=s.gpr .x1+3840 := by simpa only [ha1] using hb1
    have hmb' : b.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count 8 := by simpa only [hma,ha0,ha13,ha14] using hmb
    have htb : InverseTable.Words b.mem (s.gpr .x1) := by
      rw [hmb']
      exact tableWords_frame ht (dotPass_frame (by decide)) (by
        intro r hr
        have he := List.mem_singleton.mp hr
        subst r
        exact hd)
    have hqbLane : ∀e<4,vword (b.v .v31) e=8380417#32 := by
      intro e he
      rw [hqb.qv]
      exact HighPack.repeatedWord_lane _ he
    apply WP.seq
    refine WP.mono (middle_ok (s := b) htb hb1' ?_ hqbLane) fun c ⟨hkc,hmc,hc0,hc2,hc12,hfc,hsc⟩ => ?_
    · intro off hoff
      simp only [hkb.rd,hkb.wr,hka.rd,hka.wr,hb1']
      change InRegions (s.rd++s.wr) ((s.gpr .x1+BitVec.ofNat 64 3840)+BitVec.ofNat 64 off) 16
      rw [BitVec.add_assoc,← BitVec.ofNat_add]
      apply hrt
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
      omega
    · have hc0' : c.gpr .x0=s.gpr .x0 := by rw [hc0,hb0']; bv_omega
      have hc2' : c.gpr .x2=s.gpr .x0 := by rw [hc2,hb0']; bv_omega
      have hqv : c.v .v31=HighPack.repeatedWord 8380417 := (by apply VG.AArch64.vec_ext; intro e he; rw [hfc.q e he,HighPack.repeatedWord_lane _ he])
      refine WP.mono (finalLoop_ok hfc hsc hc12 ?_ ?_) fun t ⟨hkt,_,_,hmt⟩ => ?_
      · intro u hu i
        simp only [hkc.rd,hkc.wr,hkb.rd,hkb.wr,hka.rd,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hr _ (by omega)
      · intro u hu i
        simp only [hkc.wr,hkb.wr,hka.wr,hc2',BitVec.add_assoc,← BitVec.ofNat_add]
        exact hw _ (by omega)
      · refine ⟨(((hka.trans hkb).trans hkc).trans hkt).mono,?_,?_⟩
        · rw [hkt.get .x0 (by decide),hc0']
        · simpa only [dotInverseMem,hmc,hmb',hc2',hqv] using hmt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
