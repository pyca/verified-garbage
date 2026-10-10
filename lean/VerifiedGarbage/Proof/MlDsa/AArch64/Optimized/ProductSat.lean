import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductFullTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Spec.MlDsa.RawInverse

/-! ## From `ProductStatic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlKem.AArch64 (mov)

theorem multiplyInverseMem_frame (raw : Bool) (m : Mem) (p a b : Addr) :
    Frame [outputRegion p] m (multiplyInverseMem raw m p a b) := by
  apply (productPass_frame (m := m) (p := p) (a := a) (b := b) (u := 8) (by decide)).trans
  cases raw with
  | false => exact finalPass_frame (by decide)
  | true => exact rawFinalPass_frame (by decide)

theorem productCore_words_ok (raw : Bool) {s : State}
    (ht : InverseTable.Words s.mem (s.gpr .x1))
    (htr : tableRegion (s.gpr .x1)∈s.rd++s.wr)
    (har : polyRegion (s.gpr .x13)∈s.rd++s.wr)
    (hbr : polyRegion (s.gpr .x14)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x13)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x14)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.core raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x13) (s.gpr .x14) := by
  refine WP.mono (productCore_ok raw ht hsep ha hb ?_ ?_ ?_ ?_ ?_) fun t ⟨hk,hp,hm⟩ => ?_
  · intro off ho; exact ⟨_,htr,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,har,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,hbr,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,List.mem_append_right _ hw,Offset.contains_base _ ho (by omega)⟩
  · intro off ho; exact ⟨_,hw,Offset.contains_base _ ho (by omega)⟩
  · exact ⟨hk,hp,by rw [hm]; exact multiplyInverseMem_frame _ _ _ _ _,hm⟩

theorem productStaticInit_ok (s : State) :
    WP isa (.block [mov .x13 .x1,mov .x14 .x2,.adrSym .x1 "VG_MLDSA_INV_FOLDED"]) s fun t =>
      (t.gpr .x13=s.gpr .x1 ∧ t.gpr .x14=s.gpr .x2 ∧
        t.gpr .x1=s.syms "VG_MLDSA_INV_FOLDED" ∧ t.mem=s.mem) ∧ Keep [.x1,.x13,.x14] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold mov
  arun [exec_adrSym]
  rfl

theorem productStatic_words_ok (raw : Bool) {s : State}
    (ht : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED"))
    (htr : tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr)
    (har : polyRegion (s.gpr .x1)∈s.rd++s.wr)
    (hbr : polyRegion (s.gpr .x2)∈s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0)∈s.wr)
    (hsep : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)))
    (ha : (polyRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)))
    (hb : (polyRegion (s.gpr .x2)).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode raw) s fun t =>
      Keep productCoreRegs s t ∧ t.gpr .x0=s.gpr .x0 ∧
      Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=multiplyInverseMem raw s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode
  refine WP.seq (WP.mono (productStaticInit_ok s) fun a ⟨⟨h13,h14,h1,hm⟩,hk⟩ => ?_)
  have ht' : InverseTable.Words a.mem (a.gpr .x1) := by simpa only [h1,hm] using ht.words
  have h0 : a.gpr .x0=s.gpr .x0 := hk.get .x0 (by decide)
  refine WP.mono (productCore_words_ok raw ht' ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun t ⟨hkt,hpt,hft,hmt⟩ => ?_
  · simpa only [h1,hk.rd,hk.wr] using htr
  · simpa only [h13,hk.rd,hk.wr] using har
  · simpa only [h14,hk.rd,hk.wr] using hbr
  · simpa only [h0,hk.wr] using hw
  · simpa only [h1,h0] using hsep
  · simpa only [h13,h0] using ha
  · simpa only [h14,h0] using hb
  · exact ⟨(hk.trans hkt).mono,hpt.trans h0,
      by simpa only [hm,h0] using hft,
      by simpa only [hm,h0,h13,h14] using hmt⟩

theorem productCoreKeep_abi {s t : State} (h : Keep productCoreRegs s t) : abiPreserved s t := by
  refine ⟨?_,h.sp,h.vcs⟩
  intro r hr
  apply h.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def productRawK : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    polyRegion (s.gpr .x1)∈s.rd++s.wr ∧ polyRegion (s.gpr .x2)∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x2)).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧
    PositiveReduced s.mem (s.gpr .x1) ∧ PositiveReduced s.mem (s.gpr .x2)
  post s t := RawPolyIs t.mem (s.gpr .x0)
    (nttInv (multiplyNTT (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2))))
  pub s t := (∀ r∈[Reg.x0,.x1,.x2], s.gpr r=t.gpr r) ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem productRaw_pre {s : State}
    (h : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre s) : productRawK.pre s := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,
    inverseConsts_eq,Abi.withConsts,Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,ht,hw,hoa,hob,_,_,_,_,_,_,_,hpa,hpb⟩ := h
  have hrd : s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2),tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hrd]; simp,by rw [hrd]; simp,
    by rw [hw]; simp [outputRegion],?_,hoa.symm,hob.symm,?_,hpa,hpb⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))

theorem productRaw_ct : ConstantTime isa productRawK.pre productRawK.pub
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply productStatic_ct true s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 hp.1,?_⟩
  intro name hn
  have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
  subst name; exact hp.2.2

theorem productRaw_pub {s t : State}
    (h : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pub s t) : productRawK.pub s t := by
  sig_pub [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  refine ⟨?_,h.1,h.2.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `ProductSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def productSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 8192 else if r=.x1 ∨ r=.x2 then 4096 else if r=.x3 then 12288 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨4096,1024⟩,⟨65536,3904⟩]
  wr := [⟨8192,1024⟩,⟨12288,1024⟩]

theorem reduced_positive {m : Mem} {p : Addr} (h : Reduced m p) : PositiveReduced m p := by
  intro i hi
  exact Nat.lt_trans (h i hi) (by decide : q<3*q)

theorem inverseSat_positive : PositiveReduced inverseSat.mem (4096 : Addr) := by
  apply reduced_positive
  exact inverseSat_reduced

theorem productRaw_spec_pre {s : State}
    (hrd : s.rd=[⟨s.gpr .x1,1024⟩,⟨s.gpr .x2,1024⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩])
    (hwr : s.wr=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x3,1024⟩])
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈s.wr, (⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩ : Region).Disjoint r)
    (h01 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x1,1024⟩)
    (h02 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x2,1024⟩)
    (h03 : (⟨s.gpr .x0,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (h13 : (⟨s.gpr .x1,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (h23 : (⟨s.gpr .x2,1024⟩ : Region).Disjoint ⟨s.gpr .x3,1024⟩)
    (hf0 : (s.gpr .x0).toNat+1024≤2^64) (hf1 : (s.gpr .x1).toNat+1024≤2^64)
    (hf2 : (s.gpr .x2).toNat+1024≤2^64) (hf3 : (s.gpr .x3).toNat+1024≤2^64)
    (ha : PositiveReduced s.mem (s.gpr .x1)) (hb : PositiveReduced s.mem (s.gpr .x2)) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre s := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,
    inverseConsts_eq,Abi.withConsts,Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  exact ⟨by rw [hrd]; rfl,held,hfit,hsep,by rw [hrd]; rfl,hwr,h01,h02,h03,h13,h23,hf0,hf1,hf2,hf3,ha,hb⟩

theorem productSatWith_pre (m : Mem)
    (held : ∀ i<488,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hpos : PositiveReduced m 4096) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre (productSatWith m) := by
  apply productRaw_spec_pre (s := productSatWith m) rfl rfl held (by dsimp only [productSatWith]; decide) ?_
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide))
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide))
    (Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide) (by dsimp only [productSatWith]; decide)
    hpos hpos
  intro r hr
  change r∈[⟨8192,1024⟩,⟨12288,1024⟩] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by dsimp only [productSatWith]; decide)

def productSat : State := productSatWith inverseSat.mem

theorem productRaw_sat : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre productSat :=
  productSatWith_pre inverseSat.mem inverseSat_held inverseSat_positive

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
