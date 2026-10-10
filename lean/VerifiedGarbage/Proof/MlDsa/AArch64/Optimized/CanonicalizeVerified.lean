import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Spec.MlDsa.Canonicalize
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

/-! ## From `CanonicalizeCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)

theorem canonicalizePrefix_poly {initial current : Mem} {p : Addr}
    (h : CanonicalizePrefix initial current p 256) (hb : CenteredReduced initial p) :
    PolyIs current p (signedPolyAt initial p) := by
  constructor
  · intro i hi
    rw [canonicalizePrefix_complete h hi]
    exact acceptedCanonical_bounds _ (hb i hi).1 (hb i hi).2
  · apply Vector.ext
    intro i hi
    simp only [polyAt,signedPolyAt,Vector.getElem_ofFn]
    rw [canonicalizePrefix_complete h hi]
    unfold ofInt
    congr 1
    have he := acceptedCanonical_mod (coeffAt initial p i) (hb i hi).1 (hb i hi).2
    exact (Int.toNat_natCast _).symm.trans (congrArg Int.toNat he)

/-- Complete measured accepted-response conversion, including initialization
and all sixteen fixed-count iterations. -/
theorem canonicalize_ok (s : State)
    (hb : CenteredReduced s.mem (s.gpr .x0))
    (hr : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize s fun t =>
      Keep [.x0,.x9,.x10] s t ∧ PolyIs t.mem (s.gpr .x0) (signedPolyAt s.mem (s.gpr .x0)) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize
  apply WP.seq
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ⟨ha,hva⟩ => ?_
  have ka := setup_keep (HighPack.SetupKeep.ofConst ha) (by decide)
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.loop
  apply WP.seq
  refine WP.mono (counter_ok a) fun b ⟨⟨⟨hc,hm⟩,kb⟩,hvb⟩ => ?_
  have hq : ∀e<4,vword (b.v .v16) e=8380417#32 := by
    intro e he
    rw [hvb,hva,HighPack.repeatedWord_lane _ he]
  have h0 : b.gpr .x0=s.gpr .x0 := (kb.get .x0).trans (ha.gpr .x0 (by decide))
  have hmem : b.mem=s.mem := hm.trans ha.mem
  have hrd : b.rd=s.rd := kb.rd.trans ha.rd
  have hwr : b.wr=s.wr := kb.wr.trans ha.wr
  change WP isa (.loop (.block (canonicalizeBody++advance [.x0])) (.nonzero .x .x10)) b _
  refine WP.mono (canonicalizeLoop_ok hq hc ?_ ?_) fun t ⟨kt,_,_,hp⟩ => ?_
  · simpa only [hrd,hwr,h0] using hr
  · simpa only [hwr,h0] using hw
  · refine ⟨((ka.trans kb).trans kt).mono,?_⟩
    rw [hmem,h0] at hp
    exact canonicalizePrefix_poly hp hb

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

def canonicalizeK : Contract isa where
  pre s := s.wr=[polyRegion (s.gpr .x0)] ∧ CenteredReduced s.mem (s.gpr .x0)
  post s t := PolyIs t.mem (s.gpr .x0) (signedPolyAt s.mem (s.gpr .x0))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.sp=t.sp

theorem canonicalize_correct (s : State) (hp : canonicalizeK.pre s) :
    ∃ trace t, Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize s trace t ∧
      abiPreserved s t ∧ canonicalizeK.post s t := by
  obtain ⟨hw,hb⟩ := hp
  have hwrite : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hw]
    exact ⟨polyRegion (s.gpr .x0),List.mem_singleton_self _,Offset.contains_base _ ho (by omega)⟩
  have hread : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hr,hc⟩ := hwrite off ho
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  obtain ⟨tr,t,he,hk,hpost⟩ := canonicalize_ok s hb hread hwrite
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hpost⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

theorem canonicalize_contract_ct : ConstantTime isa canonicalizeK.pre canonicalizeK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply canonicalize_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2 ?_,by simp⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hp.1

def canonicalizeSat : State where
  gpr _ := 0x1000
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000,1024⟩]

theorem canonicalize_verified : Verified target VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize
    (canonicalizeContract abi) := by
  refine Verified.of_correct canonicalize_correct canonicalize_contract_ct ?_
  refine { pre := ?_,post := ?_,pub := ?_,sat := ?_ }
  · intro s h
    sig_pre [canonicalizeContract,canonicalizeSig,abi,argRegs] at h
    sig_split h
    change s.wr=[polyRegion (s.gpr .x0)] ∧ CenteredReduced s.mem (s.gpr .x0)
    exact ⟨by assumption,h⟩
  · sig_implies_post [canonicalizeContract,canonicalizeSig,canonicalizeK,abi,argRegs]
  · sig_implies_pub [canonicalizeContract,canonicalizeSig,canonicalizeK,abi,argRegs]
  · refine ⟨canonicalizeSat,?_⟩
    sig_pre [canonicalizeContract,canonicalizeSig,abi,argRegs]
    sig_and_intros
    all_goals first
      | rfl
      | exact fun i _ => by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero]; decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
