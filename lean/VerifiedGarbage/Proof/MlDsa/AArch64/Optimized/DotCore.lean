import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMiddle
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop

/-! ## From `DotLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized (DotInverse.firstAdvance)

def dotLoopRegs : List Reg := [.x0,.x1,.x11,.x13,.x14]

theorem dotAdvance_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance) s fun t =>
      ((t.gpr .x0=s.gpr .x0+128 ∧ t.gpr .x1=s.gpr .x1+480 ∧ t.gpr .x11=s.gpr .x11-1 ∧
        t.gpr .x13=s.gpr .x13+128 ∧ t.gpr .x14=s.gpr .x14+128 ∧ t.mem=s.mem) ∧
        Keep dotLoopRegs s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dotFirstBlock_eq (count : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count=
      dotFiveCode count++VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstAdvance := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock,dotFirstArithmetic_eq,
    dotFiveCode,List.append_assoc]

/-- The complete first pass, retaining exact input/output cursors. -/
theorem dotLoop_ok {count : Nat} (hn : 0<count) (hn7 : count≤7) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (hd : (⟨s.gpr .x1,3904⟩ : Region).Disjoint ⟨s.gpr .x0,1024⟩)
    (hc : s.gpr .x11=8) (hq : ProductConstants s)
    (hrt : ∀off,off+16≤3904 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hr : ∀u<8,∀j<8,∀k<count,
      InRegions (s.rd++s.wr) ((s.gpr .x13+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*k+16*j)) 16 ∧
      InRegions (s.rd++s.wr) ((s.gpr .x14+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*k+16*j)) 16)
    (hw : ∀u<8,∀i : Fin 8,InRegions s.wr
      ((s.gpr .x0+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.DotInverse.firstBlock count)) (.nonzero .x .x11)) s fun t =>
      Keep dotLoopRegs s t ∧ ProductConstants t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+3840 ∧
      t.gpr .x13=s.gpr .x13+1024 ∧ t.gpr .x14=s.gpr .x14+1024 ∧
      t.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count 8 := by
  rw [dotFirstBlock_eq]
  let I := fun u t => Keep dotLoopRegs s t ∧ ProductConstants t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (480*u) ∧
    t.gpr .x13=s.gpr .x13+BitVec.ofNat 64 (128*u) ∧
    t.gpr .x14=s.gpr .x14+BitVec.ofNat 64 (128*u) ∧
    t.mem=dotPassMem s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) count u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N:=8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t hi _
    rcases hi with ⟨hk,hqt,hp0,hp1,hp13,hp14,hm⟩
    have ht' : InverseTable.Words t.mem (s.gpr .x1) := by
      rw [hm]
      exact tableWords_frame ht (dotPass_frame (by omega)) (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hd)
    have hrt' : ∀off,off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    have hqv : ∀e<4,vword (t.v .v31) e=8380417#32 := by
      intro e he; rw [hqt.qv,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
      rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    refine dotFive_ok hn hn7 u (v:=dotBankValues t count) (fun j e he => dotBankValues_word t count j he)
      hqt (packed_tableRoots hu ht' hrt' hp1 hqv) (local_tableRoots hu ht' hrt' hp1 hqv)
      ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro j hj k hkc; simpa only [hk.rd,hk.wr,hp13,hp14] using hr u hu j hj k hkc
    · intro i; simpa only [hk.wr,hp0] using hw u hu i
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      refine WP.mono (dotAdvance_ok t₁) fun t₂ ⟨⟨⟨hp₂,hp₃,hc₂,hp₁₃,hp₁₄,hm₂⟩,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_,?_,?_⟩,?_⟩
      · constructor
        · rw [hvec₂,hv₁.v,hv.get .v31 (by decide)]; exact hqt.qv
        · rw [hvec₂,hv₁.v,hv.get .v30 (by decide)]; exact hqt.qiv
      · rw [hp₂,hk₁.get .x0,hp0]
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₁₃,hk₁.get .x13,hp13]
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₁₄,hk₁.get .x14,hp14]
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hm₂,hv₁.mem,← dotMemoryBank_eq]
        simp only [hm,hp0,hp13,hp14,dotPassMem]
      · rw [hc₂,hk₁.get .x11]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)

def dotInitRegs : List Reg := [.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11]

theorem dotSetup_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.DotInverse.setup) s fun t =>
      Keep dotInitRegs s t ∧ t.mem=s.mem ∧ t.gpr .x11=8 ∧ ProductConstants t := by
  change WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.movW .x10 4236238847 ++
    Instr.vop (.dup .s4 .v30 .x10)::
      (VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v31 8380417++firstSetup))) s _
  refine wp_scalar (by rfl) (VG.Proof.MlDsa.AArch64.Arith.movW_ok .x10 _ s)
    fun a ⟨⟨ha,hm⟩,hk⟩ hv => ?_
  refine wp_vop (d:=.v30) rfl fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v31 8380417) fun c hc => ?_
  refine WP.mono (firstSetup_ok c) fun t ⟨⟨⟨h11,htm⟩,htk⟩,htv⟩ => ?_
  refine ⟨(((hk.trans hb.chg.keep).trans (constKeep_keep hc.1 (by decide))).trans htk).mono,
    htm.trans (hc.1.mem.trans (hb.mem.trans hm)),h11,?_,?_⟩
  · rw [htv,hc.2]; rfl
  · rw [htv,hc.1.vec .v30 (by decide),hb.v,ha]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotCore.lean` -/

section

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

end
