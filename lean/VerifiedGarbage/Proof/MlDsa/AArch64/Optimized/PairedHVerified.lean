import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHStoredField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZStoredField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskSemantic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintOrder
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckCount
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckCoverage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCount
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSatMemory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi

/-! ## From `PairedHAllFields.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hPass_all_fields {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    HintIs (finalPassData true work out aux c d 8).mem out 2
      ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j) := by
  dsimp only
  refine ⟨by simp,?_⟩
  intro j hj k hk
  obtain ⟨heq,hu,hi,he⟩ := paired_coordinate hk
  have hv := hPass_stored_field hu he hg (⟨j,hj⟩,⟨k/32,hi⟩) c (hgamma _ he)
    hc hs ho ha hd hp hy flags count
  have hv' : coeffAt (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,flags,count⟩ 8).mem (pairPolyPtr out j) k=
      BitVec.ofNat 32 (pairedHintPoly m challenge secret out aux g j)[k]!.toNat := by
    simpa only [←heq] using hv
  have hpointer : ∀mm:Mem,coeffAt mm out (256*j+k)=coeffAt mm (pairPolyPtr out j) k := by
    intro mm
    simp only [coeffAt,pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 4*(256*j+k)=1024*j+4*k by omega]
  rw [hpointer,hv']
  have hj' : j<((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j).length := by simpa using hj
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some,
    List.getElem_map,List.getElem_range]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem pairedCoeff_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀r∈rs,(⟨p,2048⟩:Region).Disjoint r)
    {j k : Nat} (hj : j<2) (hk : k<n) :
    coeffAt m' (pairPolyPtr p j) k=coeffAt m (pairPolyPtr p j) k := by
  apply VG.Proof.MlDsa.Verify.coeffAt_congr _ hk
  apply VG.Proof.MlKem.bytes_frame hf _ (by decide)
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base _ (by omega))

theorem pairedHintBase_frame {rs : List Region} {m m' : Mem} {out aux : Addr}
    (hf : Frame rs m m') (ho : ∀r∈rs,(⟨out,2048⟩:Region).Disjoint r)
    (ha : ∀r∈rs,(⟨aux,2048⟩:Region).Disjoint r) (g : Nat)
    {j k : Nat} (hj : j<2) (hk : k<n) :
    responseHintBase m' (pairPolyPtr out j) (pairPolyPtr aux j) g k=
      responseHintBase m (pairPolyPtr out j) (pairPolyPtr aux j) g k := by
  rw [responseHintBase,pairedCoeff_frame hf ho hj hk,pairedCoeff_frame hf ha hj hk]
  rfl

structure HintEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  decomposed : ∀j<2,ResponseDecomposed m (pairPolyPtr (s.gpr .x2) j)
    (pairPolyPtr (s.gpr .x3) j) ((s.gpr .x5).setWidth 32).toNat
  product : ∀j<2,pairedProduct m (s.gpr .x0) (s.gpr .x1) j=pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j
  hints : ∀j<2,pairedHintPoly m (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) ((s.gpr .x5).setWidth 32).toNat j=
    pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) ((s.gpr .x5).setWidth 32).toNat j

theorem hintEntry_frame {s : State} {m : Mem} (h : HintSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : HintEntryFrame s m := by
  have sep {p : Addr} {len : Nat} (hd : (⟨p,len⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩) :
      ∀r∈[⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩],(⟨p,len⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hd.sub_right (Offset.sub_base _ (by decide))
  have hc := sep h.commonWork
  have hs := sep h.secretWork
  have ho := sep h.dataWork
  have ha := sep h.auxWork
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,fun j hj => pairedProduct_frame hf hc hs hj,?_⟩
  · intro j hj k hk
    rw [pairedCoeff_frame hf ho hj hk,pairedCoeff_frame hf ha hj hk,pairedHintBase_frame hf ho ha _ hj hk]
    exact h.decomposed j hj k hk
  · intro j hj
    apply Vector.ext
    intro k hk
    simp only [pairedHintPoly,Vector.getElem_ofFn]
    rw [pairedProduct_frame hf hc hs hj,pairedHintBase_frame hf ho ha _ hj hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHLaneNorm.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem hLane_norm {m : Mem} {work challenge secret out : Addr} {u e B : Nat}
    (hu : u<8) (he : e<4) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret) :
    passMask true work out c (firstPassMem m work challenge secret 8) u i e=0 ↔
      normZq (pairedProduct m challenge secret i.1.val)[4*u+32*i.2.val+e]!<B := by
  have hr := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt)) i.2 he
  simp only [passMask,checkMask,ite_true,hlower,hwidth]
  rw [hMask_zero ⟨hr.1,hr.2.1⟩ hB hB',hr.2.2]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintFinishSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

private theorem fourCount_nat (a b c d : BitVec 32)
    (ha : a.toNat≤128) (hb : b.toNat≤128) (hc : c.toNat≤128) (hd : d.toNat≤128) :
    (a+b+c+d).toNat=a.toNat+b.toNat+c.toNat+d.toNat := by
  simp only [BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]

private theorem pack_success (lo : BitVec 32) (P : Prop) [Decidable P] :
    (lo.setWidth 64 ||| ((if P then (1 : BitVec 64) else 0) <<< 32))=
      BitVec.ofNat 64 (lo.toNat+(if P then 4294967296 else 0)) := by
  apply BitVec.eq_of_toNat_eq
  have hlo := lo.isLt
  by_cases hp : P
  · simp only [ite_eq_left hp]
    change (lo.setWidth 64 ||| ((1#32).setWidth 64 <<< 32)).toNat=_
    rw [packedWords_nat]
    simp only [BitVec.toNat_ofNat,show (1#32).toNat=1 by decide,Nat.one_mul]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [ite_eq_right hp]
    change (lo.setWidth 64 ||| ((0#32).setWidth 64 <<< 32)).toNat=_
    rw [packedWords_nat]
    simp only [BitVec.toNat_ofNat,show (0#32).toNat=0 by decide,Nat.zero_mul]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem hintFinish_packed (counts flags : BitVec 128) (P : Prop) [Decidable P]
    (hb : ∀e<4,(vword counts e).toNat≤128)
    (hf : finishValue flags=if P then 1 else 0) :
    hintFinishValue counts flags=BitVec.ofNat 64
      (sumN 4 (fun e => (vword counts e).toNat)+(if P then 4294967296 else 0)) := by
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have hs : sumN 4 (fun e => (vword counts e).toNat)=
      (vword counts 0).toNat+(vword counts 1).toNat+(vword counts 2).toNat+(vword counts 3).toNat := by
    exact sumN_four _
  have hsum : (vword counts 0+vword counts 1+vword counts 2+vword counts 3).toNat=
      sumN 4 (fun e => (vword counts e).toNat) := by
    rw [hs]
    exact fourCount_nat _ _ _ _ h0 h1 h2 h3
  unfold hintFinishValue
  rw [hf,pack_success,hsum]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHOutputField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hOutput_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : Fin 2 × Fin 8) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let mem := firstPassMem m work challenge secret 8
    (vword (checkOutput true
      ((Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 i.1))[i.2.val])
      (mem.read (checkAddr (out+BitVec.ofNat 64 (16*u)) i) 16)
      (mem.read (checkAddr (aux+BitVec.ofNat 64 (16*u)) i) 16) c) e).toNat=
      (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat := by
  dsimp only
  have h := hPass_stored_field hu he hg i c hgamma hc hs ho ha hd hp hy 0 0
  dsimp only at h
  rw [←checkAddr_coeff _ out u i he,
    finalPass_read_written true work out aux c _ (by decide : 8≤8) hu i ho hd] at h
  rw [h,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have hb := (pairedHintPoly m challenge secret out aux g i.1.val)[4*u+32*i.2.val+e]!.toNat_le
  omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintAccess.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega)⟩

theorem HintSpecPre.access {s : State} (h : HintSpecPre s) : EntryAccess s := by
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

theorem pairedHint_machine {s : State} (h : HintSpecPre s) :
    WP isa (selected .h) s fun t =>
      ∃a u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Prepared a u ∧ CheckSetup true a u ∧ Keep entryRegs s t ∧
        let d := finalPassData true (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .h d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  exact selected_check_ok true h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) (by
      intro _ off ho
      exact accessRegion (by rw [h.rd]; simp) ho (by decide))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintContractTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_public {s t : State}
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pub s t) :
    Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t := by
  sig_pub [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4,_hgamma⟩ := h
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hsp ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · intro name hn
    have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
    subst name
    exact htable

theorem pairedHint_contract_ct : ConstantTime isa
    (pairedHintContract (abi.withConsts pairedConsts)).pre
    (pairedHintContract (abi.withConsts pairedConsts)).pub (selected .h) := by
  intro s t tr1 tr2 s' t' _ _ hp he hf
  exact h_ct s t tr1 tr2 s' t' trivial trivial (pairedHint_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPassCount.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def passHintSum (work out aux : Addr) (c : CheckConstants) (m : Mem) (e : Nat) : Nat → BitVec 32
  | 0 => 0
  | n+1 => passHintSum work out aux c m e n+
      hintSum (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c m e allChecks

/-- The final counter includes exactly the original-input hint outputs from
all completed slices, with no dependence on earlier output writes. -/
theorem finalPass_count (work out aux : Addr) (c : CheckConstants) (d : CheckData)
    {n : Nat} (hn : n≤8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) {e : Nat} (he : e<4) :
    vword (finalPassData true work out aux c d n).count e=
      vword d.count e+passHintSum work out aux c d.mem e n := by
  induction n with
  | zero => exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [finalPass_step true work out aux c d (by omega) hw,
      checkRun_count _ _ _ _ _ _ allChecks_nodup
        (fun i _ j _ => ha.sep (checkAddr_contains aux (by omega) i) (checkAddr_contains out (by omega) j)) he,
      ih (by omega)]
    have hs : hintSum
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c
        (finalPassData true work out aux c d n).mem e allChecks=
      hintSum
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c d.mem e allChecks := by
      unfold hintSum
      apply congrArg (fun xs : List (BitVec 32) => xs.sum)
      apply List.map_congr_left
      intro i _
      rw [finalPass_read_future true work out aux c d (Nat.le_refl n) (by omega) i,
        finalPass_read_aux true work out aux c d (by omega) (by omega) i ha]
    rw [hs,passHintSum]
    exact BitVec.add_assoc _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintPreIntro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_pre_intro {s : State} (h : HintSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64)
    (fit3 : (s.gpr .x3).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedHintContract,pairedHintSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonWork,h.secretData,h.secretWork,
    h.auxData.symm,h.dataWork,h.auxWork,fit0,fit1,fit2,fit3,fit4,h.products,h.gamma,h.bound,h.decomposed⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHNormComplete.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem hPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {B : Nat}
    (c : CheckConstants)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (finalPassData true work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<B := by
  dsimp only
  rw [paired_norm_iff _ (by omega),←checkCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [finalPass_flag_zero_iff true work out aux c _ (by decide : 8≤8) ho he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  exact hLane_norm hu he i c (hlower e he) (hwidth e he) hB hB' hc hs hp

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedCountBound.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem checkOutput_bit (raw low high : BitVec 128) (c : CheckConstants)
    {e : Nat} (he : e<4) : (vword (checkOutput true raw low high c) e).toNat≤1 := by
  simp only [checkOutput,ite_true,laneVector_word _ he]
  exact hintWord_bit _ _ _

/-- A bounded list of bits has an exact natural sum in its 32-bit accumulator. -/
theorem bitSum_value (xs : List (BitVec 32)) (hl : xs.length≤128)
    (hb : ∀x∈xs,x.toNat≤1) :
    xs.sum.toNat=(xs.map BitVec.toNat).sum ∧ xs.sum.toNat≤xs.length := by
  induction xs with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (by simp only [List.length_cons] at hl; omega)
      (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    have hn : x.toNat+xs.sum.toNat<2^32 := by simp only [List.length_cons] at hl; omega
    simp only [List.sum_cons,List.map_cons,BitVec.toNat_add,Nat.mod_eq_of_lt hn]
    exact ⟨by rw [ht.1],by simp only [List.length_cons]; omega⟩

theorem hintSum_bound (v : Values) (out aux : Addr) (c : CheckConstants) (m : Mem)
    {e : Nat} (he : e<4) : (hintSum v out aux c m e allChecks).toNat≤16 := by
  unfold hintSum
  have h := bitSum_value
    (allChecks.map fun i => vword (checkOutput true ((v i.1)[i.2.val])
      (m.read (checkAddr out i) 16) (m.read (checkAddr aux i) 16) c) e)
    (by rw [List.length_map]; decide)
    (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact checkOutput_bit _ _ _ _ he)
  exact h.2

/-- Eight paired slices accumulate at most 128 hints in each SIMD lane. -/
theorem passHintSum_bound (work out aux : Addr) (c : CheckConstants) (m : Mem)
    {e n : Nat} (he : e<4) (hn : n≤8) :
    (passHintSum work out aux c m e n).toNat≤16*n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hp := ih (by omega)
    have hs := hintSum_bound
      (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*n)) 128 p))
      (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c m he
    rw [passHintSum,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHintSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def hintSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 95232 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨16384,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨20480,2176⟩]

theorem hintSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,ResponseDecomposed m (pairPolyPtr 12288 j) (pairPolyPtr 16384 j) 95232) :
    (pairedHintContract (abi.withConsts pairedConsts)).pre (hintSatWith m) := by
  apply pairedHint_pre_intro (s:=hintSatWith m) ?_ held (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide) (by dsimp only [hintSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,rfl,by dsimp only [hintSatWith]; decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [hintSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [hintSatWith]; decide)

def hintSat : State := hintSatWith pairedSatMem

theorem pairedHint_sat : (pairedHintContract (abi.withConsts pairedConsts)).pre hintSat := by
  apply hintSatWith_pre pairedSatMem pairedSat_held
  · refine ⟨pairedSat_positive (by decide : 4096≤32768),?_⟩
    intro j hj
    change PositiveReduced pairedSatMem (8192+BitVec.ofNat 64 (1024*j))
    rw [show (8192:BitVec 64)=BitVec.ofNat 64 8192 by rfl,←BitVec.ofNat_add]
    exact pairedSat_positive (by omega)
  · intro j hj i hi
    have hl : coeffAt pairedSatMem (pairPolyPtr 12288 j) i=0 := by
      change coeffAt pairedSatMem (12288+BitVec.ofNat 64 (1024*j)) i=0
      rw [show (12288:BitVec 64)=BitVec.ofNat 64 12288 by rfl,←BitVec.ofNat_add]
      exact pairedSat_coeff_zero (by omega) hi
    have hh : coeffAt pairedSatMem (pairPolyPtr 16384 j) i=0 := by
      change coeffAt pairedSatMem (16384+BitVec.ofNat 64 (1024*j)) i=0
      rw [show (16384:BitVec 64)=BitVec.ofNat 64 16384 by rfl,←BitVec.ofNat_add]
      exact pairedSat_coeff_zero (by omega) hi
    simp only [responseHintBase,hl,hh]
    decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCountField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hintSum_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let mem := firstPassMem m work challenge secret 8
    (hintSum (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p))
      (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c mem e allChecks).toNat=
      sumN 2 (fun p => sumN 8 (fun j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat)) := by
  dsimp only
  unfold hintSum
  rw [(bitSum_value _ (by rw [List.length_map]; decide)
    (by intro x hx; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact checkOutput_bit _ _ _ _ he)).1]
  simp only [List.map_map,Function.comp_def]
  have hm := List.map_congr_left (l:=allChecks) (fun i _ =>
    hOutput_field hu he hg i c hgamma hc hs ho ha hd hp hy)
  rw [hm]
  exact allChecks_sum (fun p j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCountPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem passHintSum_field {m : Mem} {work challenge secret out aux : Addr} {e g n : Nat}
    (hn : n≤8) (he : e<4) (hg : IsG g) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    (passHintSum work out aux c (firstPassMem m work challenge secret 8) e n).toNat=
      sumN n (fun u => sumN 2 (fun p => sumN 8
        (fun j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpbound := passHintSum_bound work out aux c (firstPassMem m work challenge secret 8) he (by omega : n≤8)
    have hsbound := hintSum_bound
      (fun p => Inverse.rawFinalValues (readPair (firstPassMem m work challenge secret 8)
        (work+BitVec.ofNat 64 (16*n)) 128 p))
      (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c
      (firstPassMem m work challenge secret 8) he
    rw [passHintSum,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega),ih (by omega),sumN_succ]
    rw [hintSum_field (by omega) he hg c hgamma hc hs ho ha hd hp hy]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCountComplete.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem hPass_count_complete {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g)
    (flags : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,0⟩
    sumN 4 (fun e => (vword (finalPassData true work out aux c d 8).count e).toNat)=
      hintOnes ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j) := by
  dsimp only
  rw [hintOnes_pair_sum,←pairedHintSum_order]
  unfold sumN at *
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have he' := List.mem_range.mp he
  rw [finalPass_count work out aux c _ (by decide : 8≤8) ho hd he']
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  rw [hz]
  change (0+(passHintSum work out aux c (firstPassMem m work challenge secret 8) e 8)).toNat=_
  have hv := passHintSum_field (n:=8) (by decide : 8≤8) he' hg c (hgamma e he') hc hs ho ha hd hp hy
  have hzadd := congrArg BitVec.toNat (BitVec.zero_add (passHintSum work out aux c (firstPassMem m work challenge secret 8) e 8))
  exact hzadd.trans hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHReturnSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem hPass_return {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : CheckConstants)
    (hgamma : ∀e<4,vword c.gamma e=BitVec.ofNat 32 g)
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (g-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*g-1))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,0⟩
    let result := finalPassData true work out aux c d 8
    hintFinishValue result.count result.flags=BitVec.ofNat 64
      (hintOnes ((List.range 2).map fun j => pairedHintPoly m challenge secret out aux g j)+
        if normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<g then 4294967296 else 0) := by
  dsimp only
  have hgb : 1≤g ∧ g≤524288 := by rcases hg with rfl|rfl <;> decide
  have hnorm := hPass_norm_complete (aux:=aux) c hlower hwidth hgb.1 hgb.2 hc hs ho hp 0
  dsimp only at hnorm
  have hfinish : finishValue (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,0,0⟩ 8).flags=
      if normRq ((List.range 2).map fun j => pairedProduct m challenge secret j)<g then 1 else 0 := by
    rw [finishValue_accept _ (finalPass_masks _ _ _ _ _ _ _ (by intro e he; left; simp [vword])),hnorm]
    split <;> simp_all only
  have hbound : ∀e<4,(vword (finalPassData true work out aux c
      ⟨firstPassMem m work challenge secret 8,0,0⟩ 8).count e).toNat≤128 := by
    intro e he
    rw [finalPass_count work out aux c _ (by decide : 8≤8) ho hd he]
    have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
    rw [hz]
    have hb := passHintSum_bound work out aux c (firstPassMem m work challenge secret 8) he (by decide : 8≤8)
    exact (congrArg BitVec.toNat (BitVec.zero_add _)).trans_le hb
  rw [hintFinish_packed _ _ _ hbound hfinish]
  have hcount := hPass_count_complete hg c hgamma hc hs ho ha hd hp hy 0
  dsimp only at hcount
  rw [hcount]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHFunctional.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure HResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : HintIs t.mem (s.gpr .x2) 2 ((List.range 2).map fun j =>
    pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)
  ret : t.gpr .x0=BitVec.ofNat 64
    (hintOnes ((List.range 2).map fun j => pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)+
      if normRq ((List.range 2).map fun j => pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)<Round.arg32 s .x5
      then 4294967296 else 0)

theorem pairedHint_functional {s : State} (h : HintSpecPre s) :
    WP isa (selected .h) s (HResult s) := by
  refine WP.mono (pairedHint_machine h) fun t ⟨a,u,ha,hf,hp,hl,ht,hmem,hret⟩ => ?_
  have hg : Round.IsG (Round.arg32 s .x5) := by
    simpa [or_comm,gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,
      VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  have hgb : 1≤Round.arg32 s .x5 := by rcases hg with hv|hv <;> rw [hv] <;> decide
  have hframe := hintEntry_frame h hf
  have hdata : dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,0⟩ := by
    unfold dataAt
    rw [hp.mem,ha.work,ha.common,ha.secret,hl.flags,hl.count rfl]
  have hgamma : ∀e<4,vword (constantsAt u).gamma e=BitVec.ofNat 32 (Round.arg32 s .x5) := by
    intro e he
    change vword (u.v .v11) e=_
    rw [hl.gamma rfl e he,ha.gamma]
    simp only [Round.arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hlower : ∀e<4,vword (constantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x5-1) := by
    intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,ha.bound,h.bound]
    exact bound_sub_one _ hgb
  have hwidth : ∀e<4,vword (constantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x5-1) := by
    intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,ha.bound,h.bound]
    exact bound_width _ hgb
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hx := h.auxWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := hPass_all_fields hg (constantsAt u) hgamma hc hs ho hx h.auxData hframe.products hframe.decomposed 0 0
  have hvalue := hPass_return hg (constantsAt u) hgamma hlower hwidth hc hs ho hx h.auxData hframe.products hframe.decomposed
  dsimp only at hfields hvalue
  have hhints : ((List.range 2).map fun j => pairedHintPoly a.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)=
      ((List.range 2).map fun j => pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j) := by
    apply List.map_congr_left
    intro j hj
    exact hframe.hints j (List.mem_range.mp hj)
  have hproducts : ((List.range 2).map fun j => pairedProduct a.mem (s.gpr .x0) (s.gpr .x1) j)=
      ((List.range 2).map fun j => pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j) := by
    apply List.map_congr_left
    intro j hj
    exact hframe.product j (List.mem_range.mp hj)
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · rw [hmem,←hhints]
    exact hfields
  · rw [hret]
    change Response.hintFinishValue _ _=_
    rw [hvalue,hhints,hproducts]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_post {s t : State} (h : HResult s t) :
    (pairedHintContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  exact ⟨h.fields,h.ret⟩

theorem pairedHint_correct (s : State)
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .h) s tr t ∧ abiPreserved s t ∧
      (pairedHintContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedHint_functional (pairedHint_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedHint_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedHVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact paired hint generation, all-path hint outputs/counts and strict
product norm, with the original ABI and public-input timing policy. -/
theorem pairedHint_verified : Verified target (selected .h)
    (pairedHintContract (abi.withConsts pairedConsts)) :=
  ⟨pairedHint_correct,pairedHint_contract_ct,⟨hintSat,pairedHint_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
