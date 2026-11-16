module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedOutput
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseO
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.CanonicalizeContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! ### `MlDsa.AArch64.Optimized.CanonicalizeVerified`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.CanonicalizeLoop`, which only this module used -/

section

/-! ## From `CanonicalizeWord.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- An accepted centered response needs only the conditional addition of q. -/
theorem acceptedCanonical_bounds (x : BitVec 32)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) : (signCorrected x).toNat<8380417 := by
  have he := signCorrected_int x hl (by omega_using [hh])
  have hn := BitVec.toInt_eq_toNat_cond (signCorrected x)
  split at he <;> omega

theorem acceptedCanonical_mod (x : BitVec 32)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    ((signCorrected x).toNat : Int)=x.toInt%8380417 := by
  have he := signCorrected_int x hl (by omega_using [hh])
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
    rw [canonicalizeVector,laneVector_word _ (by omega_using [h]),VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ (by omega_using [h]),coeffAddr_add]
    rw [show start+(k-start)=k by omega_using [h]]
    rfl
  · rfl

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
  · rw [ite_eq_right (by omega_using [before]),h k hk,ite_eq_left before,ite_eq_left (by omega_using [before])]
  · by_cases inside : k<done+4
    · rw [ite_eq_left (by omega_using [before, inside]),h k hk,ite_eq_right before,ite_eq_left inside]
    · rw [ite_eq_right (by omega_using [inside]),h k hk,ite_eq_right before,ite_eq_right inside]

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
    have hg := canonicalizeGroup_ok (off := 16*i) (by omega_using [hi]) hrt hwt hqt
      (rest := []) (Q := I (i+1))
    simp only [List.append_nil] at hg
    apply hg
    intro v hv hm
    apply WP.block_nil_iff.mpr
    refine ⟨(hk.trans hv).mono (by decide),?_⟩
    rw [hm,hk.keep.get .x0,haddr i hi]
    have hs := canonicalizePrefix_step (by omega_using [hd, hi] : done+4*i+4≤256) hprefix
    simpa only [show done+4*(i+1)=done+4*i+4 by omega_using []] using hs
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
    refine WP.mono (canonicalizeBody_ok (by omega_using [hu] : 16*u+16≤256) hp hqt ?_ ?_ ?_) fun v ⟨hv,hpv⟩ => ?_
    · intro i hi
      simp only [h0,coeffAddr,BitVec.add_assoc,← BitVec.ofNat_add]
      congr 2
      omega_using []
    · intro i hi
      simp only [hk.rd,hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hr _ (by omega_using [hu, hi])
    · intro i hi
      simp only [hk.wr,h0,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hw _ (by omega_using [hu, hi])
    · refine WP.mono (canonicalizeAdvance_ok v) fun w ⟨⟨⟨hw0,hw10,hwm⟩,hkw⟩,hvw⟩ => ?_
      refine ⟨⟨((hk.trans hv.keep).trans hkw).mono,?_,?_,?_⟩,?_⟩
      · rw [hvw,hv.vec .v16 (by decide)]; exact hqt
      · rw [hw0,hv.keep.get .x0,h0,show 64*(u+1)=64*u+64 by omega_using [],BitVec.ofNat_add,BitVec.add_assoc]; rfl
      · rw [hwm,show 16*(u+1)=16*u+16 by omega_using []]; exact hpv
      · rw [hw10,hv.keep.get .x10]; rfl
  · exact ⟨Keep.refl _ _,hq,by simp,canonicalizePrefix_zero _ _⟩

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

end


/-! ## From `CanonicalizeCorrect.lean` -/

@[expose] public section

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
    exact ⟨polyRegion (s.gpr .x0),List.mem_singleton_self _,Offset.contains_base _ ho (by omega_using [ho])⟩
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

end

end

/-! ## From `OptimizedCanonicalize.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/CanonicalizeCallTiming.lean`, which only this module imported.
section

/-! ## From `CanonicalizeCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Response (canonicalize)

abbrev canonicalizeArgs (f : Ptr) : List (Reg × Arg) := [(.x0,.ptr f)]

theorem canonicalize_callee (S : Nat) : CalleeOk S canonicalize (canonicalizeContract abi) := by
  refine CalleeOk.of_ct canonicalize_verified.1 canonicalize_verified.2.1 (by lit_decide) (fun _ _ h => h) ?_
  change 0≤S
  exact Nat.zero_le _

theorem canonicalizeAt_pre {s s1 : State} {f : Ptr}
    (hfit : (pa s f).toNat+1024≤2^64) (hf : CenteredReduced s.mem (pa s f))
    (h1 : Args (canonicalizeArgs f) s s1) :
    (canonicalizeContract abi).pre (s1.callEntry.withRegions [] [⟨pa s f,1024⟩]) := by
  sig_pre [canonicalizeContract,canonicalizeSig,abi,argRegs]
  rw [Args.r0 h1,Args.mem h1]
  simp only [Arg.val]
  sig_and_intros
  all_goals first | rfl | exact hf | exact hfit | decide

theorem canonicalizeAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f : Ptr}
    (hfok : (Arg.ptr f).Ok) (hfit : (pa s f).toNat+1024≤2^64)
    (hf : CenteredReduced s.mem (pa s f))
    (hc : Covers ([]++[⟨pa s f,1024⟩]) (s.rd++s.wr)) (hw : Covers [⟨pa s f,1024⟩] s.wr) :
    WP isa (callAt nm canonicalize (canonicalizeArgs f)) s fun t =>
      Post S s t [⟨pa s f,1024⟩] ∧ PolyIs t.mem (pa s f) (signedPolyAt s.mem (pa s f)) := by
  have hok : ∀a∈canonicalizeArgs f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [canonicalizeArgs,List.mem_singleton]
    intro a ha; subst a; exact ⟨hfok,by change Reg.x0∈argRegs; decide⟩
  refine WP.mono (callAt_ok hS (canonicalize_callee S) hok (by simp)
    (fun s1 h1 => canonicalizeAt_pre hfit hf h1) hc hw) fun t ⟨hp,s1,h1,hpost⟩ => ⟨hp,?_⟩
  sig_post [canonicalizeContract,canonicalizeSig,abi,argRegs] at hpost
  rw [Args.r0 h1,Args.mem h1] at hpost
  exact hpost

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `CanonicalizeCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Response (canonicalize)

structure CanonicalizeCallReady (f : Ptr) (s : State) : Prop where
  fit : (pa s f).toNat+1024≤2^64
  centered : CenteredReduced s.mem (pa s f)
  readable : Covers ([]++[⟨pa s f,1024⟩]) (s.rd++s.wr)
  writable : Covers [⟨pa s f,1024⟩] s.wr

/-- Calling the accepted-output conversion reveals only the buffer address
and stack pointer, never the signs or values of its coefficients. -/
theorem canonicalizeAt_tr {S : Nat} {nm : String} {f : Ptr} (hfok : (Arg.ptr f).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → CanonicalizeCallReady f x ∧ CanonicalizeCallReady f y ∧
      pa x f=pa y f ∧ x.sp=y.sp) :
    RelCT isa Q (callAt nm canonicalize (canonicalizeArgs f)) fun _ _ => True := by
  have hok : ∀a∈canonicalizeArgs f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [canonicalizeArgs,List.mem_singleton]
    intro a ha; subst a; exact ⟨hfok,by change Reg.x0∈argRegs; decide⟩
  refine callAt_tr (canonicalize_callee S) hok (by simp) fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨rx,ry,ep,esp⟩ := hQ x y hp
  refine ⟨[],[⟨pa x f,1024⟩],canonicalizeAt_pre rx.fit rx.centered h1,?_,?_,
    rx.readable,rx.writable,?_,?_⟩
  · rw [ep]; exact canonicalizeAt_pre ry.fit ry.centered h2
  · sig_pub [canonicalizeContract,canonicalizeSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,ep⟩
  · rw [ep]; exact ry.readable
  · rw [ep]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- Accepted norm bounds supply the strictly centered conversion precondition. -/
theorem centered_of_signed {m : Mem} {p : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    CenteredReduced m p := by
  intro i hn
  have := h.bound i hn
  omega_using [hl, hh, this]

theorem value_of_signed {m : Mem} {p : Addr} {f : Poly} {lo hi : Int}
    (h : SignedPolyIs m p f lo hi) : signedPolyAt m p=f := by
  apply Vector.ext
  intro i hi
  simp only [signedPolyAt,Vector.getElem_ofFn]
  simpa only [getElem!_pos f i hi] using h.value i hi

/-- Convert an accepted signed polynomial in its existing writable slot;
all surrounding signer state is retained by the call frame. -/
theorem canonicalizeAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {p : Ptr} {f : Poly} {lo hi : Int}
    (hr : inB (rbs++wbs) p 1024=true) (hw : inB wbs p 1024=true)
    (hf : SignedPolyIs s.mem (pa s p) f lo hi) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    WP isa (callAt "vg_mldsa_canonicalize_signed"
      VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize (Response.canonicalizeArgs p)) s fun t =>
      PPostB S s t [(p,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧ PolyIs t.mem (pa s p) f := by
  refine WP.mono (Response.canonicalizeAt_ok L.s64 (ptr_ok (L.ptrBs hr)) (L.nwp hr)
    (centered_of_signed hf hl hh) (L.cR hr) (L.cW hw)) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),by simpa only [value_of_signed hf] using hv⟩

open VG.Impl.MlDsa.AArch64.Sign

def canonicalizeZChk (p : Params) (r : Nat) : Bool :=
  inB (sgR p++sgW p) (yP p r) 1024 && inB (sgW p) (yP p r) 1024 &&
  stChk p [(yP p r,1024)]

theorem canonicalizeZChk_ok {p : Params} (hp : Ok3 p) :
    ∀r<p.ℓ,canonicalizeZChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedCanonicalizeVector.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized

def canonicalizeZKeepChk (p : Params) : Bool :=
  (List.range p.ℓ).all fun r => (List.range p.ℓ).all fun j =>
    if j=r then true else keepB (sgR p) (sgW p) [(yP p r,1024)] (yP p j) 1024

theorem canonicalizeZKeepChk_ok {p : Params} (hp : Ok3 p) : canonicalizeZKeepChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem canonicalizeZ_keep {p : Params} (hc : canonicalizeZKeepChk p=true)
    {r j : Nat} (hr : r<p.ℓ) (hj : j<p.ℓ) (hne : j≠r) :
    keepB (sgR p) (sgW p) [(yP p r,1024)] (yP p j) 1024=true := by
  simp only [canonicalizeZKeepChk,List.all_eq_true,List.mem_range] at hc
  simpa only [ite_eq_right hne] using hc r hr j hj

structure CanonicalizeZState (p : Params) (S : Nat) (σ : State) (f : Nat → Poly)
    (lo hi : Int) (done : Nat) (s : State) : Prop where
  rooted : RootedSt p S σ s
  converted : ∀j<done,PolyIs s.mem (pa s (yP p j)) (f j)
  pending : ∀j,done≤j → j<p.ℓ → SignedPolyIs s.mem (pa s (yP p j)) (f j) lo hi
  flag : s.gpr .x24=1

theorem canonicalizeZ_step_post {p : Params} {S : Nat} {σ s : State} {f : Nat → Poly}
    {lo hi : Int} {r : Nat} (hr : r<p.ℓ)
    (hc : canonicalizeZChk p r=true) (hk : canonicalizeZKeepChk p=true)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : CanonicalizeZState p S σ f lo hi r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s
      (fun t => CanonicalizeZState p S σ f lo hi (r+1) t ∧ PPostB S s t [(yP p r,1024)]) := by
  simp only [canonicalizeZChk,Bool.and_eq_true] at hc
  obtain ⟨⟨hread,hwrite⟩,hst⟩ := hc
  refine WP.mono_syms (canonicalizeAt_layout h.rooted.1.lay hread hwrite
    (h.pending r (by omega_using []) hr) hl hh) fun t ⟨hp,h24,hval⟩ hy => ?_
  refine ⟨?_,hp⟩
  refine ⟨h.rooted.step hp hy hst (by simpa using hwrite),?_,?_,h24.trans h.flag⟩
  · intro j hj
    by_cases he : j=r
    · subst j
      rw [hp.pa (h.rooted.1.lay.ptrBs hread)]
      exact hval
    · exact h.rooted.1.lay.keepPoly hp (canonicalizeZ_keep hk hr (by omega_using [hr, hj]) he)
        (h.converted j (by omega_using [hj, he]))
  · intro j hj hjl
    exact keepSignedPoly h.rooted.1.lay hp (canonicalizeZ_keep hk hr hjl (by omega_using [hj]))
      (h.pending j (by omega_using [hj]) hjl)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedOutputCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

def conversionOutputChk (p : Params) : Bool :=
  (List.range p.ℓ).all fun r =>
    keepB (sgR p) (sgW p) [(yP p r,1024)] (sc oCT) (cLen p) &&
    famChk (sgR p) (sgW p) [(yP p r,1024)] 5 p.k

theorem conversionOutputChk_ok {p : Params} (hp : Ok3 p) : conversionOutputChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

structure AcceptedConversion (p : Params) (S : Nat) (σ : State) (κ : Nat)
    (lo hi : Int) (done : Nat) (s : State) : Prop where
  z : CanonicalizeZState p S σ (Zv p σ κ) lo hi done s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ κ
  hints : HFam s 5 p.k (Hv p σ κ)

theorem acceptedConversion_step {p : Params} {S : Nat} {σ s : State} {κ r : Nat} {lo hi : Int}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : AcceptedConversion p S σ κ lo hi r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r) s
      (AcceptedConversion p S σ κ lo hi (r+1)) := by
  have hc := conversionOutputChk_ok hp
  simp only [conversionOutputChk,List.all_eq_true,List.mem_range,Bool.and_eq_true] at hc
  refine WP.mono (canonicalizeZ_step_post hr (canonicalizeZChk_ok hp r hr)
    (canonicalizeZKeepChk_ok hp) hl hh h.z) fun t ⟨hz,hpost⟩ => ?_
  exact ⟨hz,(h.z.rooted.1.lay.keepBytes hpost (hc r hr).1).trans h.ct,
    HFam.keep h.z.rooted.1.lay hpost (hc r hr).2 h.hints⟩

/-- Accepted signed responses are converted once and packed to the exact
signature bytes of the passing iteration. -/
theorem optimizedOutput_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {κ : Nat} {lo hi : Int}
    (h : AcceptedConversion p S σ κ lo hi 0 s)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) (hpass : PassV p σ κ) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.output P p) s fun t =>
      St p S σ t ∧ bytesAt t.mem (pa t (.x23,0)) p.sigLen=sigV p σ κ ∧ t.gpr .x24=1 := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.output
  refine WP.seq (WP.mono (seqR_ok (I := fun r s => AcceptedConversion p S σ κ lo hi r s)
    p.ℓ 0 (fun r _ hr s h => acceptedConversion_step hp (by omega_using [hr]) hl hh h) s h)
    fun t ht => ?_)
  simp only [Nat.zero_add] at ht
  exact Output.output_ok hP (Output.oChk_ok hp) ht.z.rooted.1 ht.ct ht.z.converted ht.hints hpass ht.z.flag

end VG.Proof.MlDsa.AArch64.Sign

end
