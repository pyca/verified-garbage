import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckCoverage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSatMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi

/-! ## From `PairedZContractTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_public {s t : State}
    (h : (pairedZContract (abi.withConsts pairedConsts)).pub s t) :
    Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t := by
  sig_pub [pairedZContract,pairedZSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4⟩ := h
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hsp ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · intro name hn
    have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
    subst name
    exact htable

theorem pairedZ_contract_ct : ConstantTime isa
    (pairedZContract (abi.withConsts pairedConsts)).pre
    (pairedZContract (abi.withConsts pairedConsts)).pub (selected .z) := by
  intro s t tr1 tr2 s' t' _ _ hp he hf
  exact z_ct s t tr1 tr2 s' t' trivial trivial (pairedZ_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZEntryFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

structure ZEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced m (pairPolyPtr (s.gpr .x2) j)
  sum : ∀j<2,add (polyAt m (pairPolyPtr (s.gpr .x2) j)) (pairedProduct m (s.gpr .x0) (s.gpr .x1) j)=
    add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j)) (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)

theorem zEntry_frame {s : State} {m : Mem} (h : ZSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : ZEntryFrame s m := by
  have hc : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x0,1024⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.commonWork.sub_right (Offset.sub_base _ (by decide))
  have hs : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x1,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.secretWork.sub_right (Offset.sub_base _ (by decide))
  have ho : ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨s.gpr .x2,2048⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.dataWork.sub_right (Offset.sub_base _ (by decide))
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,?_⟩
  · intro j hj
    apply VG.Proof.MlDsa.Verify.reduced_frame hf _ (h.data j hj)
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by omega))
  · intro j hj
    rw [pairedProduct_frame hf hc hs hj,VG.Proof.MlDsa.Verify.polyAt_frame hf]
    intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZAllFields.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem zPass_all_fields {m : Mem} {work challenge secret out aux : Addr} (c : CheckConstants)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (finalPassData false work out aux c d 8).mem
    ∀j<2,CenteredReduced result (pairPolyPtr out j) ∧
      signedPolyAt result (pairPolyPtr out j)=add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j) := by
  dsimp only
  intro j hj
  have hv : ∀k<n,
      let x := coeffAt (finalPassData false work out aux c
        ⟨firstPassMem m work challenge secret 8,flags,count⟩ 8).mem (pairPolyPtr out j) k;
      -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
        ofInt x.toInt=(add (polyAt m (pairPolyPtr out j)) (pairedProduct m challenge secret j))[k]! := by
    intro k hk
    obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
    have h := zPass_stored_field (aux:=aux) hu he (⟨j,hj⟩,⟨k/32,hi⟩) c hc hs ho hp hy flags count
    simpa only [←heq] using h
  constructor
  · intro k hk
    have h := hv k hk
    change -8380417<_ ∧ _<8380417
    exact ⟨by omega,by omega⟩
  · apply Vector.ext
    intro k hk
    simpa only [signedPolyAt,Vector.getElem_ofFn,VG.Proof.MlDsa.Arith.getElem!_eq _ hk] using (hv k hk).2.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZLaneNorm.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem zLane_norm {m : Mem} {work challenge secret out : Addr} {u e B : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    passMask false work out c (firstPassMem m work challenge secret 8) u i e=0 ↔
      normZq (add (polyAt m (pairPolyPtr out i.1.val))
        (pairedProduct m challenge secret i.1.val))[4*u+32*i.2.val+e]!<B := by
  have hk : 4*u+32*i.2.val+e<n := by change 4*u+32*i.2.val+e<256; omega
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  simp only [passMask,checkMask,Bool.false_eq_true,ite_false,hlower,hwidth]
  rw [firstPass_checkInput_read hu i ho,checkAddr_coeff _ _ _ _ he,
    zMask_zero (hy _ i.1.isLt _ hk) ⟨hr.1,hr.2.1⟩ hB hB',
    ofInt_add,ofInt_nat_eq,←polyAt_get _ _ hk,hr.2.2,add_get _ _ hk]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZAccess.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega)⟩

theorem ZSpecPre.access {s : State} (h : ZSpecPre s) : EntryAccess s := by
  constructor
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

/-- The public paired-z signature provides every actual access, including the
saved register area, without assigning memory to the unused fourth argument. -/
theorem pairedZ_machine {s : State} (h : ZSpecPre s) :
    WP isa (selected .z) s fun t =>
      ∃a u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Prepared a u ∧ CheckSetup false a u ∧ Keep entryRegs s t ∧
        let d := finalPassData false (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .z d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  exact selected_check_ok false h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) (by simp)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZPreIntro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_pre_intro {s : State} (h : ZSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedZContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedZContract,pairedZSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonWork,h.secretData,h.secretWork,
    h.dataWork,fit0,fit1,fit2,fit4,h.products,h.data,h.boundLow,h.boundHigh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZNormComplete.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem zPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (finalPassData false work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j))<B := by
  dsimp only
  rw [paired_norm_iff _ (by omega),←checkCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [finalPass_flag_zero_iff false work out aux c _ (by decide : 8≤8) ho he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  exact zLane_norm hu he i c (hlower e he) (hwidth e he) hB hB' hc hs ho.symm hp hy

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def zSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 1 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨20480,2176⟩]

theorem zSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,Reduced m (pairPolyPtr 12288 j)) :
    (pairedZContract (abi.withConsts pairedConsts)).pre (zSatWith m) := by
  apply pairedZ_pre_intro (s:=zSatWith m) ?_ held (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide) (by dsimp only [zSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,by dsimp only [zSatWith]; decide,by dsimp only [zSatWith]; decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [zSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [zSatWith]; decide)

def zSat : State := zSatWith pairedSatMem

theorem pairedZ_sat : (pairedZContract (abi.withConsts pairedConsts)).pre zSat := by
  apply zSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega)
  · intro j hj
    change Reduced pairedSatMem (12288+BitVec.ofNat 64 (1024*j))
    rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
    exact pairedSat_reduced (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZReturnSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem zPass_return {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    finishValue (finalPassData false work out aux c d 8).flags=
      if normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr out j))
        (pairedProduct m challenge secret j))<B then 1 else 0 := by
  dsimp only
  have hn := zPass_norm_complete (aux:=aux) c hlower hwidth hB hB' hc hs ho hp hy count
  dsimp only at hn
  rw [finishValue_accept _ (finalPass_masks _ _ _ _ _ _ _ (by intro e he; left; simp [vword])),
    hn]
  split <;> simp_all only

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZFunctional.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure ZResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : ∀j<2,CenteredReduced t.mem (pairPolyPtr (s.gpr .x2) j) ∧
    signedPolyAt t.mem (pairPolyPtr (s.gpr .x2) j)=add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
      (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)
  ret : t.gpr .x0=if normRq ((List.range 2).map fun j => add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
    (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j))<Round.arg32 s .x6 then 1 else 0

theorem pairedZ_functional {s : State} (h : ZSpecPre s) :
    WP isa (selected .z) s (ZResult s) := by
  refine WP.mono (pairedZ_machine h) fun t ⟨a,u,ha,hf,hp,hl,ht,hmem,hret⟩ => ?_
  have hframe := zEntry_frame h hf
  have hdata : dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,u.v .v14⟩ := by
    unfold dataAt
    rw [hp.mem,ha.work,ha.common,ha.secret,hl.flags]
  have hlower : ∀e<4,vword (constantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x6-1) := by
    intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,ha.bound]
    exact bound_sub_one _ h.boundLow
  have hwidth : ∀e<4,vword (constantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x6-1) := by
    intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,ha.bound]
    exact bound_width _ h.boundLow
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := zPass_all_fields (aux:=s.gpr .x3) (constantsAt u) hc hs ho hframe.products hframe.data 0 (u.v .v14)
  have hvalue := zPass_return (aux:=s.gpr .x3) (constantsAt u) hlower hwidth h.boundLow h.boundHigh
    hc hs ho hframe.products hframe.data (u.v .v14)
  dsimp only at hfields hvalue
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · intro j hj
    rw [hmem]
    have hv := hfields j hj
    rw [hframe.sum j hj] at hv
    exact hv
  · rw [hret]
    change Response.finishValue _=_
    rw [hvalue]
    have he : ((List.range 2).map fun j => add (polyAt a.mem (pairPolyPtr (s.gpr .x2) j))
        (pairedProduct a.mem (s.gpr .x0) (s.gpr .x1) j))=
        ((List.range 2).map fun j => add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
        (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)) := by
      apply List.map_congr_left
      intro j hj
      exact hframe.sum j (List.mem_range.mp hj)
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_post {s t : State} (h : ZResult s t) :
    (pairedZContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedZContract,pairedZSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  refine ⟨h.fields,?_⟩
  rw [h.ret]
  split <;> rfl

theorem pairedZ_correct (s : State)
    (h : (pairedZContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .z) s tr t ∧ abiPreserved s t ∧
      (pairedZContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedZ_functional (pairedZ_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedZ_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedZVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact selected batched response-sum kernel, including all-path outputs,
strict norm return, restored ABI, and the shared public-input timing policy. -/
theorem pairedZ_verified : Verified target (selected .z)
    (pairedZContract (abi.withConsts pairedConsts)) :=
  ⟨pairedZ_correct,pairedZ_contract_ct,⟨zSat,pairedZ_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
