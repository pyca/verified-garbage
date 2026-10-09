import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep VChg)

def canonicalizeBody : List Instr := [0,16,32,48].flatMap canonicalizeGroup

theorem canonicalizeBody_ok {s : State} {m : Mem} {p : Addr} {done : Nat}
    (hd : done+16≤256) (hp : CanonicalizePrefix m s.mem p done)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (haddr : ∀i<4,s.gpr .x0+BitVec.ofNat 64 (16*i)=coeffAddr p (done+4*i))
    (hr : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block canonicalizeBody) s fun t =>
      StepKeep [.v0,.v7] s t ∧ CanonicalizePrefix m t.mem p (done+16) := by
  let I := fun i t => StepKeep [.v0,.v7] s t ∧ CanonicalizePrefix m t.mem p (done+4*i)
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),by simpa using hp⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (canonicalizeGroup (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hprefix⟩
    have hrt : InRegions (t.rd++t.wr) (t.gpr .x0+BitVec.ofNat 64 (16*i)) 16 := by
      simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using hr i hi
    have hwt : InRegions t.wr (t.gpr .x0+BitVec.ofNat 64 (16*i)) 16 := by
      simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    have hqt : ∀e<4,vword (t.v .v16) e=8380417#32 := by
      rw [hk.vec .v16 (by decide)]; exact hq
    have hg := canonicalizeGroup_ok (off := 16*i) (by omega) hrt hwt hqt
      (rest := []) (Q := I (i+1))
    simp only [List.append_nil] at hg
    apply hg
    intro v hv hm
    apply WP.block_nil_iff.mpr
    refine ⟨(hk.trans hv).mono (by decide),?_⟩
    rw [hm,hk.keep.get .x0,haddr i hi]
    have hs := canonicalizePrefix_step (by omega : done+4*i+4≤256) hprefix
    simpa only [show done+4*(i+1)=done+4*i+4 by omega] using hs
  exact fourGroups_ok canonicalizeGroup I hinit hstep

theorem canonicalizeAdvance_ok (s : State) : WP isa (.block (advance [.x0])) s fun t =>
    ((t.gpr .x0=s.gpr .x0+64 ∧ t.gpr .x10=s.gpr .x10-1 ∧ t.mem=s.mem) ∧
      Keep [.x0,.x10] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  arun [List.map_cons,List.map_nil,List.cons_append,List.nil_append]
  exact ⟨rfl,rfl⟩

theorem canonicalizeLoop_ok {s : State}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32) (hc : s.gpr .x10=16)
    (hr : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (canonicalizeBody++advance [.x0])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x10] s t ∧ (∀e<4,vword (t.v .v16) e=8380417#32) ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ CanonicalizePrefix s.mem t.mem (s.gpr .x0) 256 := by
  let I := fun u t => Keep [.x0,.x10] s t ∧ (∀e<4,vword (t.v .v16) e=8380417#32) ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧
    CanonicalizePrefix s.mem t.mem (s.gpr .x0) (16*u)
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hqt,h0,hp⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (canonicalizeBody_ok (by omega : 16*u+16≤256) hp hqt ?_ ?_ ?_) fun v ⟨hv,hpv⟩ => ?_
    · intro i hi
      simp only [h0,coeffAddr,BitVec.add_assoc,← BitVec.ofNat_add]
      congr 2
      omega
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hr _ (by omega)
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega)
    · refine WP.mono (canonicalizeAdvance_ok v) fun w ⟨⟨⟨hw0,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_⟩,?_⟩
      · rw [hvw,hv.vec .v16 (by decide)]; exact hqt
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hwm,show 16*(u+1)=16*u+16 by omega]; exact hpv
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,canonicalizePrefix_zero _ _⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response
