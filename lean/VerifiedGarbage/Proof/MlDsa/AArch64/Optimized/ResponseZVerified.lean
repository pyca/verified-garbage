import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Spec.MlDsa.ResponseZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

/-! ## From `ResponseZLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def addBody : List Instr := [0,16,32,48].flatMap addGroup

theorem addBody_ok {s : State} {m : Mem} {p a : Addr} {B : BitVec 32} {u : Nat}
    (hr : ZReady B s) (hm : s.mem=(zRun m p a B (4*u)).mem) (hf : s.v .v31=(zRun m p a B (4*u)).flags)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (ha : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block addBody) s fun t =>
      StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
      t.mem=(zRun m p a B (4*(u+1))).mem ∧ t.v .v31=(zRun m p a B (4*(u+1))).flags := by
  let I := fun i t => StepKeep [.v0,.v1,.v2,.v6,.v31] s t ∧ ZReady B t ∧
    t.mem=(zRun m p a B (4*u+i)).mem ∧ t.v .v31=(zRun m p a B (4*u+i)).flags
  have hinit : I 0 s := ⟨StepKeep.ofChg (VChg.refl _ _) (by decide),hr,hm,hf⟩
  have hstep : ∀i<4,∀t,I i t → WP isa (.block (addGroup (16*i))) t (I (i+1)) := by
    intro i hi t ⟨hk,hready,hmem,hflags⟩
    refine WP.mono (addGroup_step hi hready hmem hflags
      ((hk.keep.get .x0).trans h0) ((hk.keep.get .x1).trans h1) ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x0] using ha i hi
    · simpa only [hk.keep.rd,hk.keep.wr,hk.keep.get .x1] using hb i hi
    · simpa only [hk.keep.wr,hk.keep.get .x0] using hw i hi
    · refine ⟨(hk.trans hv).mono (by decide),hrv,?_,?_⟩
      · change v.mem=(zRun m p a B (4*u+(i+1))).mem
        rw [show 4*u+(i+1)=4*u+i+1 by omega,zRun_next]
        exact hmv
      · change v.v .v31=(zRun m p a B (4*u+(i+1))).flags
        rw [show 4*u+(i+1)=4*u+i+1 by omega,zRun_next]
        exact hfv
  have h := fourGroups_ok addGroup I hinit hstep
  simpa only [I,addBody,show 4*u+4=4*(u+1) by omega] using h

theorem addLoop_ok {s : State} (hr : ZReady ((s.gpr .x2).setWidth 32) s)
    (hc : s.gpr .x10=16) (hf : s.v .v31=0)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa (.loop (.block (addBody++advance [.x0,.x1])) (.nonzero .x .x10)) s fun t =>
      Keep [.x0,.x1,.x10] s t ∧ ZReady ((s.gpr .x2).setWidth 32) t ∧
      t.gpr .x0=s.gpr .x0+1024 ∧ t.gpr .x1=s.gpr .x1+1024 ∧
      t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).mem ∧
      t.v .v31=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).flags := by
  let B := (s.gpr .x2).setWidth 32
  let I := fun u t => Keep [.x0,.x1,.x10] s t ∧ ZReady B t ∧
    t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (64*u) ∧ t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (64*u) ∧
    t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) B (4*u)).mem ∧
    t.v .v31=(zRun s.mem (s.gpr .x0) (s.gpr .x1) B (4*u)).flags
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 16) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ⟨hk,hready,h0,h1,hm,hf⟩ _
    rw [WP.block_append_iff]
    refine WP.mono (addBody_ok hready hm hf h0 h1 ?_ ?_ ?_) fun v ⟨hv,hrv,hmv,hfv⟩ => ?_
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact ha _ (by omega)
    · intro i hi
      simp only [hk.rd,hk.wr,h1,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hb _ (by omega)
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega)
    · refine WP.mono (advance2_ok v) fun w ⟨⟨⟨hw0,hw1,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_,hwm.trans hmv,?_⟩,?_⟩
      · exact hrv.frame (rs := []) (by simp) (by intro r _; exact congrFun hvw r)
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hw1,hv.keep.get .x1,h1,show 64*(u+1)=64*u+64 by omega,BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hvw,hfv]
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hr,by simp,by simp,rfl,hf⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZCore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)

theorem addNorm_eq : VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm=
    .seq (.block addInit) (.seq (.seq (.block [.movz .x .x10 16 0])
      (.loop (.block (addBody++advance [.x0,.x1])) (.nonzero .x .x10)))
      VG.Impl.MlDsa.AArch64.Optimized.Response.finish) := rfl

theorem addNorm_words_ok (s : State)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s fun t =>
      Keep [.x0,.x1,.x9,.x10] s t ∧
      t.mem=(zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).mem ∧
      t.gpr .x0=finishValue (zRun s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32) 64).flags := by
  rw [addNorm_eq]
  apply WP.seq
  refine WP.mono (addInit_ok s) fun a ⟨hsa,hready,hzero⟩ => ?_
  have hka := setup_keep hsa (by decide)
  apply WP.seq
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hcount,hmem⟩,hkb⟩,hvec⟩ => ?_
  have hksb := hka.trans hkb
  have hrb : ZReady ((b.gpr .x2).setWidth 32) b := by
    rw [hkb.get .x2,hka.get .x2]
    exact hready.frame (rs := []) (by simp) (fun r _=>congrFun hvec r)
  refine WP.mono (addLoop_ok hrb hcount (by rw [hvec,hzero]) ?_ ?_ ?_) fun c ⟨hkc,hrc,h0,h1,hmc,hfc⟩ => ?_
  · simpa only [hkb.rd,hkb.wr,hkb.get .x0,hka.rd,hka.wr,hka.get .x0] using ha
  · simpa only [hkb.rd,hkb.wr,hkb.get .x1,hka.rd,hka.wr,hka.get .x1] using hb
  · simpa only [hkb.wr,hkb.get .x0,hka.wr,hka.get .x0] using hw
  · refine WP.mono (finish_ok c) fun t ⟨⟨⟨hout,hmt⟩,hkt⟩,hvt⟩ => ?_
    refine ⟨((hksb.trans hkc).trans hkt).mono,?_,?_⟩
    · rw [hmt,hmc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]
    · rw [hout,hfc,hmem,hsa.mem,hkb.get .x0,hka.get .x0,hkb.get .x1,hka.get .x1,hkb.get .x2,hka.get .x2]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)

theorem ofInt_nat (v : Nat) : ofInt (v:Int)=ofNat v := by
  apply Fin.ext
  change ((v:Int) % (q:Int)).toNat%q=v%q
  rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

theorem zSum_coeff (m : Mem) (p a : Addr) {k : Nat} (hk : k<n) :
    (add (polyAt m p) (signedPolyAt m a))[k]! =
      ofInt (((coeffAt m p k).toNat:Int)+(coeffAt m a k).toInt) := by
  rw [add_get _ _ hk,polyAt_get _ _ hk,ofInt_add,ofInt_nat]
  congr 1
  rw [getElem!_eq _ hk]
  simp only [signedPolyAt,Vector.getElem_ofFn]

theorem zRun_centered (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a) :
    CenteredReduced (zRun m p a B 64).mem p := by
  intro k hk
  rw [zRun_coeff m p a B hd hk,addReduced_int _ _ (ha k hk) (hb k hk)]
  have hak : (coeffAt m p k).toNat<8380417 := ha k hk
  have hbk : -8380417<(coeffAt m a k).toInt ∧ (coeffAt m a k).toInt<16760834 := hb k hk
  have := reduce32_bounds (x := ((coeffAt m p k).toNat:Int)+(coeffAt m a k).toInt)
    (by omega) (by omega)
  change -8380417<_ ∧ _<8380417
  omega

theorem zRun_poly (m : Mem) (p a : Addr) (B : BitVec 32)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a) :
    signedPolyAt (zRun m p a B 64).mem p=add (polyAt m p) (signedPolyAt m a) := by
  apply ext_getElem!
  intro k hk
  rw [zSum_coeff _ _ _ hk,getElem!_eq _ hk]
  simp only [signedPolyAt,Vector.getElem_ofFn]
  rw [zRun_coeff m p a B hd hk,addReduced_int _ _ (ha k hk) (hb k hk)]
  unfold ofInt
  congr 1
  exact congrArg Int.toNat (reduce32_mod _)

theorem zRun_finish (m : Mem) (p a : Addr) (B : Nat)
    (hd : (pR p).Disjoint (pR a)) (ha : Reduced m p) (hb : RawReduced m a)
    (hB : 1≤B) (hB' : B≤524288) :
    finishValue (zRun m p a (BitVec.ofNat 32 B) 64).flags=
      if normRq [add (polyAt m p) (signedPolyAt m a)]<B then 1 else 0 := by
  have hf := zRun_flags m p a B hd hB hB' ha hb (by decide : 64≤64)
  have he := finishValue_flags hf
  have hr := finishValue_flags_range hf
  have hn : (∀i<64,∀e<4,zBad m p a B i e=false) ↔ normRq [add (polyAt m p) (signedPolyAt m a)]<B := by
    rw [VG.Proof.MlDsa.Round.normRq_lt]
    constructor
    · intro h k hk
      have hg := h (k/4) (by change k<256 at hk; omega) (k%4) (by omega)
      simp only [zBad,decide_eq_false_iff_not,Nat.not_le] at hg
      rw [show 4*(k/4)+k%4=k by omega] at hg
      rw [zSum_coeff _ _ _ hk]
      exact hg
    · intro h i hi e he
      simp only [zBad,decide_eq_false_iff_not,Nat.not_le]
      have hk : 4*i+e<n := by rw [n_eq]; omega
      rw [← zSum_coeff _ _ _ hk]
      exact h _ hk
  rw [hn] at he
  split
  · exact he.mpr ‹_›
  · rcases hr with hr|hr
    · exact hr
    · exact False.elim (‹¬_› (he.mp hr))

theorem addNorm_ok (s : State)
    (hd : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)))
    (hay : Reduced s.mem (s.gpr .x0)) (hbs : RawReduced s.mem (s.gpr .x1))
    (hB : 1≤((s.gpr .x2).setWidth 32).toNat) (hB' : ((s.gpr .x2).setWidth 32).toNat≤524288)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s fun t =>
      VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x9,.x10] s t ∧
      CenteredReduced t.mem (s.gpr .x0) ∧
      signedPolyAt t.mem (s.gpr .x0)=add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1)) ∧
      t.gpr .x0=if normRq [add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1))]<
        ((s.gpr .x2).setWidth 32).toNat then 1 else 0 := by
  refine WP.mono (addNorm_words_ok s ha hb hw) fun t ⟨hk,hm,hret⟩ => ?_
  refine ⟨hk,?_,?_,?_⟩
  · rw [hm]; exact zRun_centered _ _ _ _ hd hay hbs
  · rw [hm]; exact zRun_poly _ _ _ _ hd hay hbs
  · rw [hret]
    have h := zRun_finish s.mem (s.gpr .x0) (s.gpr .x1) ((s.gpr .x2).setWidth 32).toNat hd hay hbs hB hB'
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

def addNormK : Contract isa where
  pre s := s.wr=[polyRegion (s.gpr .x0)] ∧ s.rd=[polyRegion (s.gpr .x1)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0) ∧ RawReduced s.mem (s.gpr .x1) ∧
    1≤((s.gpr .x2).setWidth 32).toNat ∧ ((s.gpr .x2).setWidth 32).toNat≤524288
  post s t := CenteredReduced t.mem (s.gpr .x0) ∧
    signedPolyAt t.mem (s.gpr .x0)=add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1)) ∧
    (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1))]<
      ((s.gpr .x2).setWidth 32).toNat then 1 else 0
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp

theorem addNorm_correct (s : State) (hp : addNormK.pre s) :
    ∃trace t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s trace t ∧
      abiPreserved s t ∧ addNormK.post s t := by
  obtain ⟨hw,hr,hd,ha,hb,hB,hB'⟩ := hp
  have hwrite : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hw]
    exact ⟨polyRegion (s.gpr .x0),List.mem_singleton_self _,Offset.contains_base _ ho (by omega)⟩
  have hread : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hr,hc⟩ := hwrite off ho
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have hinput : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hr]
    exact ⟨polyRegion (s.gpr .x1),by simp,Offset.contains_base _ ho (by omega)⟩
  obtain ⟨tr,t,he,hk,hcenter,hpoly,hret⟩ := addNorm_ok s hd ha hb hB hB' hread hinput hwrite
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hcenter,hpoly,?_⟩
  · intro r hr
    apply hk.gpr r
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hret]
    split <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseZVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa

theorem addNorm_contract_ct : ConstantTime isa addNormK.pre addNormK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply addNorm_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2 ?_,by simp⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hp.1
  · exact hp.2.1

def addNormSat : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 1 else 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩]
  wr := [⟨4096,1024⟩]

theorem addNorm_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
    (addNormContract abi) := by
  refine Verified.of_correct addNorm_correct addNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [addNormContract,addNormSig,abi,argRegs] at h
    sig_split h
    exact ⟨by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,h⟩
  · sig_implies_post [addNormContract,addNormSig,addNormK,abi,argRegs]
  · sig_implies_pub [addNormContract,addNormSig,addNormK,abi,argRegs]
  · refine ⟨addNormSat,?_⟩
    sig_pre [addNormContract,addNormSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
