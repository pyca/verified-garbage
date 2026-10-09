import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotFive

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
