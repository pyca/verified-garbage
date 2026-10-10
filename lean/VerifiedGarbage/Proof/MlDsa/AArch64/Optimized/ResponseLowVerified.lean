import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCore
import VerifiedGarbage.Spec.MlDsa.ResponseLow
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith

/-! ## From `ResponseLowCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Round

theorem lowRun_return (m : Mem) (g B : Nat) (p a l : Addr) (hg : IsG g)
    (hpl : (polyRegion p).Disjoint (polyRegion l))
    (hap : (polyRegion a).Disjoint (polyRegion p)) (hal : (polyRegion a).Disjoint (polyRegion l))
    (hB : 1≤B) (hB' : B≤524288) (ha : Reduced m p) (hb : RawReduced m a) :
    finishValue (lowRun m g B p a l 64).flags=if responseLowPass m p a g B then 1 else 0 := by
  have hflags := lowRun_flags m g B p a l hg hpl hap hal hB hB' ha hb (by decide : 64≤64)
  have hf := finishValue_flags hflags
  have he : (∀i<64,∀e<4,lowBad m g p a B i e=false) ↔ responseLowPass m p a g B := by
    simp only [lowBad,responseLowPass,responseDifference]
    constructor
    · intro h i hi
      change i<256 at hi
      have hh := h (i/4) (by omega) (i%4) (by omega)
      rw [show 4*(i/4)+i%4=i by omega] at hh
      exact Nat.lt_of_not_ge (of_decide_eq_false hh)
    · intro h i hi e he
      have hh := h (4*i+e) (by change 4*i+e<256; omega)
      exact decide_eq_false (by omega)
  have hr := finishValue_flags_range hflags
  by_cases h : responseLowPass m p a g B
  · rw [ite_eq_left h]; exact hf.mpr (he.mpr h)
  · rw [ite_eq_right h]
    exact hr.resolve_right (fun hone => h (he.mp (hf.mp hone)))

theorem subLowNorm_ok (s : State) (hg : IsG (arg32 s .x3))
    (hB : 1≤arg32 s .x4) (hB' : arg32 s .x4≤524288)
    (hcan : Reduced s.mem (s.gpr .x0)) (hraw : RawReduced s.mem (s.gpr .x1))
    (hpl : (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)))
    (hap : (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x0)))
    (hal : (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x2)))
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s fun t =>
      Keep [.x0,.x1,.x2,.x3,.x5,.x9,.x10] s t ∧
      (∀i<n,(coeffAt t.mem (s.gpr .x0) i).toNat=
        (highBits (arg32 s .x3) (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)).toNat) ∧
      (∀i<n,(coeffAt t.mem (s.gpr .x2) i).toInt=
        lowBits (arg32 s .x3) (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)) ∧
      t.gpr .x0=if responseLowPass s.mem (s.gpr .x0) (s.gpr .x1) (arg32 s .x3) (arg32 s .x4) then 1 else 0 := by
  refine WP.mono (subLowNorm_words_ok s hg hB (by simp only [arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]) ha hb hw hl) fun t ⟨hk,hm,hret⟩ => ?_
  refine ⟨hk,?_,?_,?_⟩
  · intro i hi
    rw [hm,(lowRun_coeff _ _ _ _ _ _ hpl hap hal hi).1]
    exact subHigh_word hg (hcan i hi) (hraw i hi).1 (hraw i hi).2
  · intro i hi
    rw [hm,(lowRun_coeff _ _ _ _ _ _ hpl hap hal hi).2]
    exact subLow_word hg (hcan i hi) (hraw i hi).1 (hraw i hi).2
  · rw [hret,lowRun_return _ _ _ _ _ _ hg hpl hap hal hB hB' hcan hraw]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlDsa.AArch64.Round

def subLowNormK : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1)] ∧ s.wr=[polyRegion (s.gpr .x0),polyRegion (s.gpr .x2)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x2)) ∧
    Reduced s.mem (s.gpr .x0) ∧ RawReduced s.mem (s.gpr .x1) ∧
    IsG (arg32 s .x3) ∧ 1≤arg32 s .x4 ∧ arg32 s .x4≤524288
  post s t :=
    (∀i<n,(coeffAt t.mem (s.gpr .x0) i).toNat=(highBits (arg32 s .x3)
      (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)).toNat) ∧
    (∀i<n,(coeffAt t.mem (s.gpr .x2) i).toInt=lowBits (arg32 s .x3)
      (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)) ∧
    (t.gpr .x0).setWidth 32=if responseLowPass s.mem (s.gpr .x0) (s.gpr .x1) (arg32 s .x3) (arg32 s .x4) then 1 else 0
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧
    (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32 ∧ s.sp=t.sp

theorem subLowNorm_correct (s : State) (hp : subLowNormK.pre s) :
    ∃ trace t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s trace t ∧
      abiPreserved s t ∧ subLowNormK.post s t := by
  obtain ⟨hr,hw,hpl,hap,hal,hcan,hraw,hg,hB,hB'⟩ := hp
  have hwrite (r : Reg) (hm : polyRegion (s.gpr r)∈s.wr) :
      ∀off,off+16≤1024 → InRegions s.wr (s.gpr r+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨_,hm,Offset.contains_base _ ho (by omega)⟩
  have hw0 := hwrite .x0 (by rw [hw]; simp)
  have hw2 := hwrite .x2 (by rw [hw]; simp)
  have hr0 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hm,hc⟩ := hw0 off ho
    exact ⟨r,List.mem_append_right _ hm,hc⟩
  have hr1 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨polyRegion (s.gpr .x1),by rw [hr]; simp,Offset.contains_base _ ho (by omega)⟩
  obtain ⟨tr,t,he,hk,hh,hl,hn⟩ := subLowNorm_ok s hg hB hB' hcan hraw hpl hap hal hr0 hr1 hw0 hw2
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hh,hl,?_⟩
  · intro r hp
    apply hk.gpr r
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [hn]
    split <;> rfl

theorem subLowNorm_contract_ct : ConstantTime isa subLowNormK.pre subLowNormK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
  apply zext_ct (τ:=Taint.ofRegs [.x0,.x1,.x2,.x3]) ?_ (by taint_decide)
  intro s t hp
  have h := agree_zext (gr:=.x3) (rs:=[.x0,.x1,.x2]) hp.2.2.2.2 hp.2.2.2.1 ?_
  · exact ⟨h.1,fun r hr=>h.2 r (by simpa [Taint.mem_ofRegs,List.mem_cons,or_comm,or_left_comm,or_assoc] using hr)⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseLowVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

def subLowNormSat : State where
  gpr r := match r with
    | .x0 => 4096 | .x1 => 8192 | .x2 => 12288 | .x3 => 95232 | .x4 => 1 | _ => 0
  sp := 65536
  mem _ := 0
  rd := [⟨8192,1024⟩]
  wr := [⟨4096,1024⟩,⟨12288,1024⟩]

theorem subLowNorm_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
    (subLowNormContract abi) := by
  refine Verified.of_correct subLowNorm_correct subLowNorm_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [subLowNormContract,subLowNormSig,abi,argRegs] at h
    sig_split h
    refine ⟨by assumption,by assumption,by assumption,?_,?_,by assumption,by assumption,?_,by assumption,h⟩
    · exact Region.Disjoint.symm (by assumption)
    · with_reducible assumption
    · exact isG_of_mem (by assumption)
  · sig_implies_post [subLowNormContract,subLowNormSig,subLowNormK,arg32,abi,argRegs]
  · sig_implies_pub [subLowNormContract,subLowNormSig,subLowNormK,abi,argRegs]
  · refine ⟨subLowNormSat,?_⟩
    sig_pre [subLowNormContract,subLowNormSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | exact Region.disjoint_of_sep (by decide)
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
