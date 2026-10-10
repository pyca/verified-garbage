import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotContract

/-! ## From `DotCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse

theorem dot_correct {count : Nat} (hn : 0<count) (hn7 : count≤7) (s : State) (hp : (dotK count).pre s) :
    ∃trace t,Exec isa (staticCode count) s trace t ∧ abiPreserved s t ∧ (dotK count).post s t := by
  obtain ⟨htr,ha,hb,hw,hsep,hoa,hob,ht,hfa,hfb⟩ := hp
  obtain ⟨tr,t,he,hk,_,_,hm⟩ := dotStaticCode_words_ok hn hn7 ht htr ha hb hw hsep
  have hv := dotInverseMem_field hn7
    (fun j hj => positiveReduced_iff.mp (hfa j hj)) (fun j hj => positiveReduced_iff.mp (hfb j hj))
    (fun j hj => hoa.sub_left (VG.Offset.sub_base _ (by omega)))
    (fun j hj => hob.sub_left (VG.Offset.sub_base _ (by omega)))
  rw [← hm] at hv
  exact ⟨tr,t,he,dotCoreKeep_abi hk,hv⟩

theorem dot_ct {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    ConstantTime isa (dotK count).pre (dotK count).pub (staticCode count) := by
  have ct : ConstantTime isa (fun _ => True)
      (Taint.AgreeS ["VG_MLDSA_INV_FOLDED"] (Taint.ofRegs [.x0,.x1,.x2])) (staticCode count) := by
    rcases hc with rfl | rfl | rfl
    · exact dot4Inverse_ct
    · exact dot5Inverse_ct
    · exact dot7Inverse_ct
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2.2.1 ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1
  · intro name hn
    have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2.2.2

theorem dot_pub {count : Nat} {s t : State}
    (h : (dotInverseContract count (abi.withConsts VG.Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts)).pub s t) :
    (dotK count).pub s t := by
  sig_pub [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotSat.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def dotSat (count : Nat) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 16384 else if r=.x2 then 32768 else if r=.x3 then 8192 else 0
  sp := 131072
  syms _ := 65536
  mem := constMem 65536 expandedWords
  rd := [⟨16384,1024*count⟩,⟨32768,1024*count⟩,⟨65536,3904⟩]
  wr := [⟨4096,1024⟩,⟨8192,1024⟩]

theorem dotSat_held (count : Nat) : ∀i<488,
    (dotSat count).mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0 := inverseSat_held

theorem dotSat_reduced (count : Nat) (p : Addr) (hp : p.toNat+1024≤65536) : Reduced (dotSat count).mem p := by
  intro i hi
  simp only [dotSat,coeffAt,Mem.readW,BitVec.setWidth_eq]
  rw [Mem.read_eq_of_bytes (v:=(0#32)) ?_]
  · decide
  · intro j hj
    have ha : ¬ ((p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j)-65536).toNat<8*expandedWords.length := by
      rw [InverseTable.expandedWords_length]
      have hi' : i<256 := hi
      simp only [BitVec.toNat_sub,BitVec.toNat_add,BitVec.toNat_ofNat,
        show (65536:BitVec 64).toNat=65536 by decide]
      omega
    simp only [constMem,ha,ite_false]
    simp

theorem dot_spec_pre {count : Nat} {s : State} (hc : count≤7)
    (hg0 : s.gpr .x0=4096) (hg1 : s.gpr .x1=16384) (hg2 : s.gpr .x2=32768)
    (hg3 : s.gpr .x3=8192) (hsym : s.syms "VG_MLDSA_INV_FOLDED"=65536)
    (hrd : s.rd=[⟨16384,1024*count⟩,⟨32768,1024*count⟩,⟨65536,3904⟩])
    (hwr : s.wr=[⟨4096,1024⟩,⟨8192,1024⟩])
    (held : ∀i<488,s.mem.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (ha : ∀j<count,PositiveReduced s.mem (16384+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<count,PositiveReduced s.mem (32768+BitVec.ofNat 64 (1024*j))) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre s := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  rw [hg0,hg1,hg2,hg3,hsym,hrd,hwr]
  have he : count*256*4=1024*count := by omega
  rw [he]
  refine ⟨rfl,held,by decide,?_,rfl,rfl,?_,?_,?_,?_,?_,by decide,?_,?_,by decide,ha,hb⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · exact Region.disjoint_of_sep (by simp [Region.sep]; omega)
  · simp; omega
  · simp; omega

theorem dot_sat (count : Nat) (hc : count≤7) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre (dotSat count) := by
  apply dot_spec_pre hc rfl rfl rfl rfl rfl rfl rfl (dotSat_held count)
  · intro j hj i hi
    have hr := dotSat_reduced count (16384+BitVec.ofNat 64 (1024*j)) (by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, show (16384:Addr).toNat=16384 by decide]; omega) i hi
    change _<3*8380417
    change _<8380417 at hr
    omega
  · intro j hj i hi
    have hr := dotSat_reduced count (32768+BitVec.ofNat 64 (1024*j)) (by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, show (32768:Addr).toNat=32768 by decide]; omega) i hi
    change _<3*8380417
    change _<8380417 at hr
    omega

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `DotVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts)

/-- The selected fused dot/inverse kernels have canonical output and positive-lazy inputs. -/
theorem dot_verified {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    Verified target (staticCode count) (dotInverseContract count (abi.withConsts inverseConsts)) := by
  refine Verified.of_correct (dot_correct (by omega) (by omega)) (dot_ct hc)
    { pre := fun _ h => dot_pre h, post := ?_, pub := ?_, sat := ⟨dotSat count,dot_sat count (by omega)⟩ }
  · intro s t _ h
    sig_post [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    exact h
  · intro s t _ _ h
    exact dot_pub h

theorem dot4_verified : Verified target (staticCode 4)
    (dotInverseContract 4 (abi.withConsts inverseConsts)) := dot_verified (Or.inl rfl)

theorem dot5_verified : Verified target (staticCode 5)
    (dotInverseContract 5 (abi.withConsts inverseConsts)) := dot_verified (Or.inr (Or.inl rfl))

theorem dot7_verified : Verified target (staticCode 7)
    (dotInverseContract 7 (abi.withConsts inverseConsts)) := dot_verified (Or.inr (Or.inr rfl))

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
