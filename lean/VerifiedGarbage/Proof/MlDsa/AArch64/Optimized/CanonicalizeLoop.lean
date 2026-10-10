import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop

/-! ## From `CanonicalizeWord.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- An accepted centered response needs only the conditional addition of q. -/
theorem acceptedCanonical_bounds (x : BitVec 32)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) : (signCorrected x).toNat<8380417 := by
  have he := signCorrected_int x hl (by omega)
  have hn := BitVec.toInt_eq_toNat_cond (signCorrected x)
  split at he <;> omega

theorem acceptedCanonical_mod (x : BitVec 32)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    ((signCorrected x).toNat : Int)=x.toInt%8380417 := by
  have he := signCorrected_int x hl (by omega)
  have hn := BitVec.toInt_eq_toNat_cond (signCorrected x)
  have hb := acceptedCanonical_bounds x hl hh
  split at he <;> omega

/-- Exact three-instruction accepted-output conversion, without an
additional subtraction or reduction pass. -/
theorem cadd_ok {d : VReg} (h7 : d≠.v7)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (k : ∀t,VChg [.v7,d] s t →
      (∀e<4,vword (t.v d) e=signCorrected (vword (s.v d) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Response.cadd d++rest)) s Q := by
  refine wp_vop (d := .v7) rfl fun a ha => wp_vop (d := .v7) rfl fun b hb =>
    wp_vop (d := d) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get d h7,ha.get d h7,hb.v,word_and,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v16 (by decide),hq e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_strq)

def canonicalizeGroup (off : Nat) : List Instr :=
  [.ldrq .v0 .x0 off] ++ VG.Impl.MlDsa.AArch64.Optimized.Response.cadd .v0 ++ [.strq .v0 .x0 off]

def canonicalizeVector (v : BitVec 128) : BitVec 128 :=
  laneVector fun e => Inverse.signCorrected (vword v e)

def canonicalizeGroupMem (m : Mem) (p : Addr) : Mem :=
  m.write p 16 (canonicalizeVector (m.read p 16))

/-- Exact read/modify/write semantics for four accepted response coefficients. -/
theorem canonicalizeGroup_ok {s : State} {off : Nat} (ho : off%16=0 ∧ off<4096*16)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v7] s t →
      t.mem=canonicalizeGroupMem s.mem (s.gpr .x0+BitVec.ofNat 64 off) →
      WP isa (.block rest) t Q) :
    WP isa (.block (canonicalizeGroup off++rest)) s Q := by
  unfold canonicalizeGroup
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun a ha => ?_
  refine cadd_ok (by decide : VReg.v0≠.v7)
    (by intro e he; rw [ha.get .v16]; exact hq e he) fun b hb hv => ?_
  have hk : VChg [.v0,.v7] s b := (ha.chg.trans hb).mono (by decide)
  have hval : b.v .v0=canonicalizeVector (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) := by
    apply vec_ext
    intro e he
    rw [canonicalizeVector,laneVector_word _ he,hv e he,ha.v]
  refine wp_strq ho rfl (by simpa only [hk.wr,hk.gpr] using hw) fun t ht => ?_
  refine k t ((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem ht) |>.mono (by decide)) ?_
  rw [ht.mem,hk.mem,hk.gpr,hval]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16)

theorem canonicalizeGroup_coeff (m : Mem) (p : Addr) {start k : Nat}
    (hs : start+4≤256) (hk : k<256) :
    coeffAt (canonicalizeGroupMem m (coeffAddr p start)) p k =
      if start≤k ∧ k<start+4 then Inverse.signCorrected (coeffAt m p k) else coeffAt m p k := by
  unfold canonicalizeGroupMem
  rw [coeffAt_write16 _ _ hs _ hk]
  split
  · rename_i h
    rw [canonicalizeVector,laneVector_word _ (by omega),VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ (by omega),coeffAddr_add]
    rw [show start+(k-start)=k by omega]
    rfl
  · rfl

/-- Each group leaves every other coefficient unchanged, allowing in-place
iteration without changing the inputs of future groups. -/
theorem canonicalizeGroup_outside (m : Mem) (p : Addr) {start k : Nat}
    (hs : start+4≤256) (hk : k<256) (ho : k<start ∨ start+4≤k) :
    coeffAt (canonicalizeGroupMem m (coeffAddr p start)) p k=coeffAt m p k := by
  rw [canonicalizeGroup_coeff m p hs hk,ite_eq_right (by omega)]

/-- Invariant for the in-place conversion: the processed prefix is corrected,
and all subsequent coefficients still contain the original signed words. -/
def CanonicalizePrefix (initial current : Mem) (p : Addr) (done : Nat) : Prop :=
  ∀ k<256, coeffAt current p k =
    if k<done then Inverse.signCorrected (coeffAt initial p k) else coeffAt initial p k

theorem canonicalizePrefix_zero (m : Mem) (p : Addr) : CanonicalizePrefix m m p 0 := by
  intro k hk
  simp

theorem canonicalizePrefix_step {initial current : Mem} {p : Addr} {done : Nat}
    (hd : done+4≤256) (h : CanonicalizePrefix initial current p done) :
    CanonicalizePrefix initial (canonicalizeGroupMem current (coeffAddr p done)) p (done+4) := by
  intro k hk
  rw [canonicalizeGroup_coeff current p hd hk]
  by_cases before : k<done
  · rw [ite_eq_right (by omega),h k hk,ite_eq_left before,ite_eq_left (by omega)]
  · by_cases inside : k<done+4
    · rw [ite_eq_left (by omega),h k hk,ite_eq_right before,ite_eq_left inside]
    · rw [ite_eq_right (by omega),h k hk,ite_eq_right before,ite_eq_right inside]

theorem canonicalizePrefix_complete {initial current : Mem} {p : Addr}
    (h : CanonicalizePrefix initial current p 256) {k : Nat} (hk : k<256) :
    coeffAt current p k=Inverse.signCorrected (coeffAt initial p k) := by
  rw [h k hk,ite_eq_left hk]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeLoop.lean` -/

section

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

end
