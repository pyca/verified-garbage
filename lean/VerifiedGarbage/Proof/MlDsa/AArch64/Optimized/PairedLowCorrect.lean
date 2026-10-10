import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowKernel
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedWordTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecFrame
import VerifiedGarbage.Spec.MlDsa.PairedResponse
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.Arith.Zq
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMaskInvariant
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSatMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowField

/-! ## `PairedLowAllFields` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_all_fields {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (lowPassData g work out aux c d 8).mem
    ∀j<2,∀k<n,
      (coeffAt result (pairPolyPtr out j) k).toNat=
          (highBits g (pairedDifference m challenge secret out j)[k]!).toNat ∧
        (coeffAt result (pairPolyPtr aux j) k).toInt=
          lowBits g (pairedDifference m challenge secret out j)[k]! := by
  dsimp only
  intro j hj k hk
  have hkn : k<256 := hk
  have hu : k%32/4<8 := by omega
  have hi : k/64<4 := by omega
  have hh : k%64/32<2 := by omega
  have he : k%4<4 := by omega
  have hv := lowPass_stored_field hu he hg (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ c
    (hscale _ he) hc hs ho ha hd hp hy flags count
  have hidx : lowCoeff (k%32/4) (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ (k%4)=k := by
    change 4*(k%32/4)+64*(k/64)+32*(k%64/32)+k%4=k
    have hm : k%64%32=k%32 := Nat.mod_mod_of_dvd k (by decide : 32∣64)
    have hm4 : k%32%4=k%4 := Nat.mod_mod_of_dvd k (by decide : 4∣32)
    omega
  simpa only [hidx] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowContractTiming` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_public {s t : State}
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pub s t) : WordPublic s t := by
  sig_pub [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4,h5⟩ := h
  refine ⟨hsp,?_,h5,htable⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption

theorem pairedLow_contract_ct : ConstantTime isa
    (pairedLowContract (abi.withConsts pairedConsts)).pre
    (pairedLowContract (abi.withConsts pairedConsts)).pub (selected .r0) := by
  intro s t tr1 tr2 s' t' hs ht hp he hf
  exact r0_word_ct s t tr1 tr2 s' t' (pairedLow_pre hs).access (pairedLow_pre ht).access
    (pairedLow_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowEntryFrame` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

structure LowEntryFrame (s : State) (m : Mem) : Prop where
  products : pairedProductsReduced m (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced m (pairPolyPtr (s.gpr .x2) j)
  difference : ∀j<2,pairedDifference m (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j=
    pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j

theorem lowEntry_frame {s : State} {m : Mem} (h : LowSpecPre s)
    (hf : Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem m) : LowEntryFrame s m := by
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
  refine ⟨pairedProductsReduced_frame hf hc hs h.products,?_,fun j hj => pairedDifference_frame hf hc hs ho hj⟩
  intro j hj
  apply VG.Proof.MlDsa.Verify.reduced_frame hf _ (h.data j hj)
  intro r hr
  exact (ho r hr).sub_left (Offset.sub_base _ (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCoverage` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

/-- The paired SIMD traversal covers exactly all coefficients of both polynomials. -/
theorem lowCoverage (P : Nat → Nat → Prop) :
    (∀e<4,∀u<8,∀i:LowIndex,∀h:Fin 2,P i.1.val (lowCoeff u i h e)) ↔
      ∀j<2,∀k<n,P j k := by
  constructor
  · intro hall j hj k hk
    have hkn : k<256 := hk
    have hu : k%32/4<8 := by omega
    have hi : k/64<4 := by omega
    have hh : k%64/32<2 := by omega
    have he : k%4<4 := by omega
    have hv := hall _ he _ hu (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩
    have hidx : lowCoeff (k%32/4) (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ (k%4)=k := by
      change 4*(k%32/4)+64*(k/64)+32*(k%64/32)+k%4=k
      have hm : k%64%32=k%32 := Nat.mod_mod_of_dvd k (by decide : 32∣64)
      have hm4 : k%32%4=k%4 := Nat.mod_mod_of_dvd k (by decide : 4∣32)
      omega
    simpa only [hidx] using hv
  · intro hall e he u hu i h
    exact hall i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLaneNorm` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowLane_norm {m : Mem} {work challenge secret out : Addr} {u e g B : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    let mem := firstPassMem m work challenge secret 8
    let addr := lowAddr (out+BitVec.ofNat 64 (16*u)) i h
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p)) i h
    lowMask g mem addr raw c e=0 ↔
      normZq (ofInt (lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!))<B := by
  dsimp only
  have hr := lowHalf_raw_field hu he i h hc hs hp
  have hb : (vword ((firstPassMem m work challenge secret 8).read
      (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16) e).toNat<q := by
    rw [firstPass_lowInput_read hu i h ho,lowAddr_coeff _ _ _ _ _ he]
    exact hy i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)
  have hv := lowInputField_difference m challenge secret out hu he i h _ hr.2.2
  rw [lowMask_zero hg hscale hlower hwidth hb ⟨hr.1,hr.2.1⟩ hB hB',
    firstPass_lowInputField hu i h _ e ho,hv]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowNormRq` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The shared paired norm is exactly the strict low-bits check on all coefficients. -/
theorem pairedLow_norm_iff (m : Mem) (challenge secret out : Addr) (g B : Nat) (hB : 0<B) :
    normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B ↔
      ∀j<2,∀k<n,normZq (ofInt (lowBits g (pairedDifference m challenge secret out j)[k]!))<B := by
  rw [VG.Proof.MlDsa.Sign.normRq_lt_iff _ hB]
  simp only [List.forall_mem_map,List.mem_range]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  rw [VG.Proof.MlDsa.Round.normRq_lt]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  rw [pairedLowPoly,getElem!_eq _ hk,Vector.getElem_map,getElem!_eq _ hk]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowNormComplete` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_norm_complete {m : Mem} {work challenge secret out aux : Addr} {g B : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    (∀e<4,vword (lowPassData g work out aux c d 8).flags e=0) ↔
      normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B := by
  dsimp only
  rw [pairedLow_norm_iff _ _ _ _ _ _ (by omega),←lowCoverage]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  rw [lowPass_flag_zero_iff _ _ _ _ _ _ (by decide : 8≤8) ho ha hd he]
  have hz : vword (0 : BitVec 128) e=0 := by simp [vword]
  simp only [hz,true_and]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  apply forall_congr'
  intro i
  rw [lowPassAccept,lowPairAccept_halves]
  apply forall_congr'
  intro h
  exact lowLane_norm hu he hg i h c (hscale e he) (hlower e he) (hwidth e he)
    hB hB' hc hs ho.symm hp hy

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReturnComplete` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_return_complete {m : Mem} {work challenge secret out aux : Addr} {g B : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : ∀e<4,vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : ∀e<4,vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,0,count⟩
    Response.finishValue (lowPassData g work out aux c d 8).flags =
      if normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B then 1 else 0 := by
  dsimp only
  have hz : FlagMasks (0 : BitVec 128) := by
    intro e he
    exact Or.inl (by simp [vword])
  rw [finishValue_accept _ (lowPass_masks _ _ _ _ _ _ _ hz)]
  have hn := lowPass_norm_complete hg c hscale hlower hwidth hB hB' hc hs ho ha hd hp hy count
  dsimp only at hn
  rw [hn]
  by_cases h : normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m challenge secret out j))<B
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowEntryState` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)

theorem preparedLow_data {s a b u : State} (ha : Arguments s a)
    (hk : Keep [.x17,.x7] a b) (hm : b.mem=a.mem)
    (hp : Prepared b u) (hl : LowSetup (Round.arg32 s .x5) b u) :
    dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,u.v .v14⟩ := by
  unfold dataAt
  rw [hp.mem,hm,hk.get .x0 (by decide),hk.get .x13 (by decide),hk.get .x14 (by decide),
    ha.work,ha.common,ha.secret,hl.flags]

theorem bound_sub_one (w : BitVec 32) (hw : 1≤w.toNat) :
    w-1=BitVec.ofNat 32 (w.toNat-1) := by
  have h := BitVec.ofNat_sub_ofNat_of_le (w:=32) w.toNat 1 (by decide) hw
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.ofNat_eq_ofNat] using h

theorem bound_width (w : BitVec 32) (hw : 1≤w.toNat) :
    w+(w-1)=BitVec.ofNat 32 (2*w.toNat-1) := by
  rw [bound_sub_one w hw]
  have he : w=BitVec.ofNat 32 w.toNat := by simp
  conv => lhs; lhs; rw [he]
  rw [←BitVec.ofNat_add]
  congr 1
  omega

theorem preparedLow_constants {s a b u : State} (ha : Arguments s a)
    (hk : Keep [.x17,.x7] a b) (hl : LowSetup (Round.arg32 s .x5) b u)
    (hB : 1≤Round.arg32 s .x6) :
    (∀e<4,vword (lowConstantsAt u).scale e=BitVec.ofNat 32 (2*Round.arg32 s .x5)) ∧
    (∀e<4,vword (lowConstantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x6-1)) ∧
    (∀e<4,vword (lowConstantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x6-1)) := by
  refine ⟨hl.scale,?_,?_⟩
  · intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,hk.get .x8 (by decide),ha.bound]
    exact bound_sub_one _ hB
  · intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,hk.get .x8 (by decide),ha.bound]
    exact bound_width _ hB

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFunctional` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : ∀j<2,∀i<n,
    (coeffAt t.mem (pairPolyPtr (s.gpr .x2) j) i).toNat=
      (highBits (Round.arg32 s .x5) (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)[i]!).toNat ∧
    (coeffAt t.mem (pairPolyPtr (s.gpr .x3) j) i).toInt=
      lowBits (Round.arg32 s .x5) (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)[i]!
  ret : t.gpr .x0=if normRq ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
    (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j))<Round.arg32 s .x6 then 1 else 0

theorem pairedLow_functional {s : State} (h : LowSpecPre s) :
    WP isa (selected .r0) s (LowResult s) := by
  refine WP.mono (pairedLow_machine h) fun t ⟨a,b,u,ha,hf,hk,hm,hp,hl,ht,hmem,hret⟩ => ?_
  have hg : Round.IsG (Round.arg32 s .x5) := by
    simpa [or_comm,gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,
      VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  have hframe := lowEntry_frame h hf
  obtain ⟨hscale,hlower,hwidth⟩ := preparedLow_constants ha hk hl h.boundLow
  have hdata := preparedLow_data ha hk hm hp hl
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hx := h.auxWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := lowPass_all_fields hg (lowConstantsAt u) hscale hc hs ho hx h.dataAux
    hframe.products hframe.data 0 (u.v .v14)
  have hvalue := lowPass_return_complete hg (lowConstantsAt u) hscale hlower hwidth h.boundLow h.boundHigh
    hc hs ho hx h.dataAux hframe.products hframe.data (u.v .v14)
  dsimp only at hfields hvalue
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · intro j hj i hi
    rw [hmem]
    have hv := hfields j hj i hi
    rw [hframe.difference j hj] at hv
    exact hv
  · change t.gpr .x0=_
    rw [hret]
    change Response.finishValue _=_
    rw [hvalue]
    have he : ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
        (pairedDifference a.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j))=
        ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
        (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)) := by
      apply List.map_congr_left
      intro j hj
      rw [hframe.difference j (List.mem_range.mp hj)]
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCorrect` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_post {s t : State} (h : LowResult s t) :
    (pairedLowContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  refine ⟨h.fields,?_⟩
  rw [h.ret]
  split <;> rfl

theorem pairedLow_correct (s : State)
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .r0) s tr t ∧ abiPreserved s t ∧
      (pairedLowContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedLow_functional (pairedLow_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedLow_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPreIntro` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_pre_intro {s : State} (h : LowSpecPre s)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (fitTable : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (fit0 : (s.gpr .x0).toNat+1024≤2^64) (fit1 : (s.gpr .x1).toNat+2048≤2^64)
    (fit2 : (s.gpr .x2).toNat+2048≤2^64) (fit3 : (s.gpr .x3).toNat+2048≤2^64)
    (fit4 : (s.gpr .x4).toNat+2176≤2^64) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre s := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  exact ⟨by rw [h.rd]; rfl,held,fitTable,h.tableSep,by rw [h.rd]; rfl,h.wr,
    h.commonData,h.commonAux,h.commonWork,h.secretData,h.secretAux,h.secretWork,
    h.dataAux,h.dataWork,h.auxWork,fit0,fit1,fit2,fit3,fit4,h.products,h.data,h.gamma,h.boundLow,h.boundHigh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSat` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def lowSatWith (m : Mem) : State where
  gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 12288
    else if r=.x3 then 16384 else if r=.x4 then 20480 else if r=.x5 then 95232
    else if r=.x6 then 1 else 0
  sp := 131072
  syms _ := 65536
  mem := m
  rd := [⟨4096,1024⟩,⟨8192,2048⟩,⟨65536,4096⟩]
  wr := [⟨12288,2048⟩,⟨16384,2048⟩,⟨20480,2176⟩]

theorem lowSatWith_pre (m : Mem)
    (held : ∀i<512,m.readW (65536+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0)
    (hprod : pairedProductsReduced m 4096 8192)
    (hdata : ∀j<2,Reduced m (pairPolyPtr 12288 j)) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre (lowSatWith m) := by
  apply pairedLow_pre_intro (s:=lowSatWith m) ?_ held (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide) (by dsimp only [lowSatWith]; decide)
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hprod,hdata,by dsimp only [lowSatWith]; decide,by dsimp only [lowSatWith]; decide,by dsimp only [lowSatWith]; decide⟩
  · intro i hi
    refine (held i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]
  · intro r hr
    change r∈[⟨12288,2048⟩,⟨16384,2048⟩,⟨20480,2176⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by dsimp only [lowSatWith]; decide)
  all_goals exact Region.disjoint_of_sep (by dsimp only [lowSatWith]; decide)

def lowSat : State := lowSatWith pairedSatMem

theorem pairedLow_sat : (pairedLowContract (abi.withConsts pairedConsts)).pre lowSat := by
  apply lowSatWith_pre pairedSatMem pairedSat_held
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

/-! ## `PairedLowVerified` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact selected batched low-part kernel, including all-path outputs,
strict norm return, restored ABI, and the shared public-input timing policy. -/
theorem pairedLow_verified : Verified target (selected .r0)
    (pairedLowContract (abi.withConsts pairedConsts)) :=
  ⟨pairedLow_correct,pairedLow_contract_ct,⟨lowSat,pairedLow_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCall` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_callee (S : Nat) : CalleeOk S (selected .r0)
    (pairedLowContract (abi.withConsts pairedConsts)) :=
  ⟨pairedLow_verified.1,pairedLow_verified.2.1,Nat.zero_le _⟩

abbrev pairedLowArgs (c secret out low work : Ptr) (g B : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr c),(.x1,.ptr secret),(.x2,.ptr out),(.x3,.ptr low),(.x4,.ptr work),(.x5,.imm g),(.x6,.imm B)]

structure PairedLowReady (c secret out low work : Ptr) (g B : Nat) (s : State) : Prop where
  cFit : (pa s c).toNat+1024≤2^64
  secretFit : (pa s secret).toNat+2048≤2^64
  outFit : (pa s out).toNat+2048≤2^64
  lowFit : (pa s low).toNat+2048≤2^64
  workFit : (pa s work).toNat+2176≤2^64
  held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64
  tableApart : ∀r∈[⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩],
    (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  cOut : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s out,2048⟩
  cLow : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s low,2048⟩
  cWork : (⟨pa s c,1024⟩:Region).Disjoint ⟨pa s work,2176⟩
  secretOut : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s out,2048⟩
  secretLow : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s low,2048⟩
  secretWork : (⟨pa s secret,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  outLow : (⟨pa s out,2048⟩:Region).Disjoint ⟨pa s low,2048⟩
  outWork : (⟨pa s out,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  lowWork : (⟨pa s low,2048⟩:Region).Disjoint ⟨pa s work,2176⟩
  products : pairedProductsReduced s.mem (pa s c) (pa s secret)
  canonical : ∀j<2,Reduced s.mem (pairPolyPtr (pa s out) j)
  gamma : g∈gamma2s
  boundPos : 1≤B
  boundMax : B≤524288
  readable : Covers [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩,
    ⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] (s.rd++s.wr)
  writable : Covers [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] s.wr

theorem PairedLowReady.gamma_lt {c secret out low work : Ptr} {g B : Nat} {s : State}
    (h : PairedLowReady c secret out low work g B s) : g<2^32 := by
  have hg := VG.Proof.MlDsa.AArch64.Round.isG_of_mem h.gamma
  rcases hg with rfl|rfl <;> decide

theorem pairedLowAt_pre {s s1 : State} {c secret out low work : Ptr} {g B : Nat}
    (h : PairedLowReady c secret out low work g B s)
    (h1 : Args (pairedLowArgs c secret out low work g B) s s1) (hy : s1.syms=s.syms) :
    (pairedLowContract (abi.withConsts pairedConsts)).pre
      (s1.callEntry.withRegions [⟨pa s c,1024⟩,⟨pa s secret,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
        [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩]) := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow]
  have h5 : s1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
  have h6 : s1.gpr .x6=BitVec.ofNat 64 B := h1.imm (by simp [pairedLowArgs])
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.r4 h1,h5,h6,
    Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  rw [hg,hB]
  exact ⟨trivial,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),h.tableApart _ (by simp),
    trivial,trivial,h.cOut,h.cLow,h.cWork,h.secretOut,h.secretLow,h.secretWork,h.outLow,h.outWork,h.lowWork,
    h.cFit,h.secretFit,h.outFit,h.lowFit,h.workFit,h.products,h.canonical,h.gamma,h.boundPos,h.boundMax⟩

theorem pairedLowArgs_ok {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok) :
    ∀x∈pairedLowArgs c secret out low work g B,x.2.Ok ∧ x.1∈argRegs := by
  simp only [pairedLowArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨hc,by simp⟩
  · exact ⟨hs,by simp⟩
  · exact ⟨ho,by simp⟩
  · exact ⟨hl,by simp⟩
  · exact ⟨hw,by simp⟩
  · exact ⟨trivial,by simp⟩
  · exact ⟨trivial,by simp⟩

def PairedLowPost (g B : Nat) (m m' : Mem) (c secret out low : Addr) (r : BitVec 32) : Prop :=
  (∀j<2,∀i<n,
    (coeffAt m' (pairPolyPtr out j) i).toNat=(highBits g (pairedDifference m c secret out j)[i]!).toNat ∧
    (coeffAt m' (pairPolyPtr low j) i).toInt=lowBits g (pairedDifference m c secret out j)[i]!) ∧
  r=if normRq ((List.range 2).map fun j => pairedLowPoly g (pairedDifference m c secret out j))<B then 1 else 0

theorem pairedLowAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State}
    {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok)
    (h : PairedLowReady c secret out low work g B s) :
    WP isa (callAt nm (selected .r0) (pairedLowArgs c secret out low work g B)) s fun t =>
      Post S s t [⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩] ∧
      PairedLowPost g B s.mem t.mem (pa s c) (pa s secret) (pa s out) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (callAtSyms_ok hS (pairedLow_callee S)
    (pairedLowArgs_ok hc hs ho hl hw) (by simp)
    (fun s1 h1 hy => pairedLowAt_pre h h1 hy) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ?_
  sig_post [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at hq
  have h5 : s1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
  have h6 : s1.gpr .x6=BitVec.ofNat 64 B := h1.imm (by simp [pairedLowArgs])
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,h5,h6,Args.mem h1] at hq
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by have := h.gamma_lt; bv_omega
  have hB : ((BitVec.ofNat 64 B).setWidth 32).toNat=B := by have := h.boundMax; bv_omega
  simpa only [PairedLowPost,Arg.val,hg,hB] using And.intro hP hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCallTiming` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLowAt_tr {S : Nat} {nm : String} {c secret out low work : Ptr} {g B : Nat}
    (hc : (Arg.ptr c).Ok) (hs : (Arg.ptr secret).Ok) (ho : (Arg.ptr out).Ok)
    (hl : (Arg.ptr low).Ok) (hw : (Arg.ptr work).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → PairedLowReady c secret out low work g B x ∧ PairedLowReady c secret out low work g B y ∧
      pa x c=pa y c ∧ pa x secret=pa y secret ∧ pa x out=pa y out ∧ pa x low=pa y low ∧
      pa x work=pa y work ∧ x.sp=y.sp ∧ x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR") :
    RelCT isa Q (callAt nm (selected .r0) (pairedLowArgs c secret out low work g B)) fun _ _=>True := by
  refine callAtSyms_tr (pairedLow_callee S) (pairedLowArgs_ok hc hs ho hl hw) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ec,es,eo,el,ew,esp,et⟩ := hQ x y hp
  refine ⟨[⟨pa x c,1024⟩,⟨pa x secret,2048⟩,⟨x.syms "VG_MLDSA_INV_PAIR",4096⟩],
    [⟨pa x out,2048⟩,⟨pa x low,2048⟩,⟨pa x work,2176⟩],
    pairedLowAt_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ec,es,eo,el,ew,et]
    exact pairedLowAt_pre ry h2 hy2
  · sig_pub [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
    have h5x : x1.gpr .x5=BitVec.ofNat 64 g := h1.imm (by simp [pairedLowArgs])
    have h5y : y1.gpr .x5=BitVec.ofNat 64 g := h2.imm (by simp [pairedLowArgs])
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,
      Args.r3 h1,Args.r3 h2,Args.r4 h1,Args.r4 h2,h5x,h5y,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,ec,es,eo,el,ew,rfl⟩
  · rw [ec,es,eo,el,ew,et]; exact ry.readable
  · rw [eo,el,ew]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowField` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem PairedLowPost.field {g B : Nat} {m m' : Mem} {c secret out low : Addr}
    {r : BitVec 32} {f : Nat → Poly}
    (hp : PairedLowPost g B m m' c secret out low r)
    (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hf : ∀j<2,pairedDifference m c secret out j=f j) :
    (∀j<2,NatPolyIs m' (pairPolyPtr out j) ((f j).map fun x=>(highBits g x).toNat) ∧
      SignedPolyIs m' (pairPolyPtr low j) (pairedLowPoly g (f j)) (-(g:Int)) g) ∧
    r=if normRq ((List.range 2).map fun j=>pairedLowPoly g (f j))<B then 1 else 0 := by
  refine ⟨?_,?_⟩
  · intro j hj
    refine ⟨?_,⟨?_,?_⟩⟩
    · apply Vector.ext
      intro i hi
      simp only [natPolyAt,Vector.getElem_ofFn,Vector.getElem_map]
      rw [(hp.1 j hj i hi).1,hf j hj,getElem!_eq _ hi]
    · intro i hi
      rw [(hp.1 j hj i hi).2]
      exact Response.lowBits_bounds hg _
    · intro i hi
      rw [(hp.1 j hj i hi).2,hf j hj]
      simp only [pairedLowPoly,getElem!_eq _ hi,Vector.getElem_map]
  · rw [hp.2]
    have he : ((List.range 2).map fun j=>pairedLowPoly g (pairedDifference m c secret out j))=
        ((List.range 2).map fun j=>pairedLowPoly g (f j)) := by
      apply List.map_congr_left
      intro j hj
      rw [hf j (List.mem_range.mp hj)]
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
