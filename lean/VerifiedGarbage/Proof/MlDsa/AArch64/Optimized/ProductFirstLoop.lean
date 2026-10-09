import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductPassMemory
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MultiplyInverse

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
    productFiveCode++productAdvance := by decide +kernel

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
      rw [hm]; exact productPass_frame (by omega)
    have ht' : InverseTable.Words t.mem (s.gpr .x1) :=
      tableWords_frame ht hf (by simpa only [List.mem_singleton,forall_eq,tableRegion] using hd)
    have hrt' : ∀ off, off+16≤3904 → InRegions (t.rd++t.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
      simpa only [hk.rd,hk.wr] using hrt
    have hqword : ∀ e<4, vword (t.v .v31) e=8380417#32 := by
      intro e he
      rw [hqt.qv,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
      have heq : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
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
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₃,hk₁.get .x1,hp1]
        rw [show 480*(u+1)=480*u+480 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₄,hk₁.get .x13,hp13]
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hp₅,hk₁.get .x14,hp14]
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hm₂,hv₁.mem]
        simp only [hm,hp0,productPassMem]
      · rw [hc₂,hk₁.get .x11]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,by simp,by simp,by simp,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
