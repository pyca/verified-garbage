import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubLoop
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
import VerifiedGarbage.Spec.MlDsa.MontDot
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul

/-! ## From `MontDotState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep Lanes)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

structure Inv (s₀ : State) (v : Nat→Nat) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0=coeffAddr (s₀.gpr .x0) (4*i)
  x1 : s.gpr .x1=coeffAddr (s₀.gpr .x1) (4*i)
  x2 : s.gpr .x2=coeffAddr (s₀.gpr .x2) (4*i)
  consts : VConsts s
  keep : Keep [.x0,.x1,.x2,.x9,.x10,.x12] s₀ s
  frame : Frame [pR (s₀.gpr .x0)] s₀.mem s.mem
  coeff : ∀k<256,(coeffAt s.mem (s₀.gpr .x0) k).toNat=
    if k<4*i then v k else (coeffAt s₀.mem (s₀.gpr .x0) k).toNat

theorem inv_step {s₀ s t : State} {v : Nat→Nat} {i : Nat}
    (hi : i<64) (h : Inv s₀ v i s) {x : BitVec 128}
    (hm : t.mem=s.mem.write (s.gpr .x0) 16 x) (hx : Lanes x (fun e=>v (4*i+e)))
    (hc : VConsts t) (h0 : t.gpr .x0=s.gpr .x0+16)
    (h1 : t.gpr .x1=s.gpr .x1+16) (h2 : t.gpr .x2=s.gpr .x2+16)
    (hk : Keep [.x0,.x1,.x2,.x12] s t) : Inv s₀ v (i+1) t where
  x0 := by rw [h0,h.x0];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x0) (4*i) 4
  x1 := by rw [h1,h.x1];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x1) (4*i) 4
  x2 := by rw [h2,h.x2];simpa only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_eq_ofNat] using coeffAddr_add (s₀.gpr .x2) (4*i) 4
  consts := hc
  keep := (h.keep.trans hk).mono
  frame := by
    rw [hm,h.x0]
    exact h.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  coeff k hk := by
    rw [hm,h.x0,coeffAt_write16 _ _ (by omega) _ hk]
    by_cases he : 4*i≤k ∧ k<4*i+4
    · rw [ite_eq_left he,hx (k-4*i) (by omega),ite_eq_left (by omega)]
      exact congrArg v (by omega)
    · rw [ite_eq_right he,h.coeff k hk]
      have hh : (k<4*(i+1))=(k<4*i) := propext (by omega)
      simp only [hh]

theorem pro_ok (s₀ : State) (v : Nat→Nat) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.consts++([.movz .x .x12 64 0] : List Instr))) s₀
      fun s=>Inv s₀ v 0 s ∧ s.gpr .x12=BitVec.ofNat 64 64 := by
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₀) fun t ⟨hc,hm,hk⟩=>?_
  have scalar : WP isa (.block [.movz .x .x12 64 0]) t fun u=>
      u.gpr .x12=BitVec.ofNat 64 64 ∧ u.mem=t.mem ∧ u.v=t.v := by arun [State.write]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x12] scalar (by decide))
    fun u ⟨⟨h12,hum,huv⟩,ku⟩=>⟨?_,h12⟩
  have keep := hk.trans ku
  refine ⟨?_,?_,?_,?_,keep.mono,?_,?_⟩
  · rw [keep.get .x0];simp [coeffAddr]
  · rw [keep.get .x1];simp [coeffAddr]
  · rw [keep.get .x2];simp [coeffAddr]
  · exact ⟨by rw [huv];exact hc.q,by rw [huv];exact hc.qi⟩
  · rw [hum,hm];exact Frame.refl _ _
  · intro k _;rw [hum,hm];simp

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotReads.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- Each source polynomial is immutable and disjoint from the output. -/
structure Pre (n : Nat) (s : State) : Prop where
  output : pR (s.gpr .x0)∈s.wr
  input : ∀r∈[Reg.x1,.x2],∀j<n,InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (1024*j)) 1024
  apart : ∀r∈[Reg.x1,.x2],∀j<n,(pR (s.gpr r+BitVec.ofNat 64 (1024*j))).Disjoint (pR (s.gpr .x0))
  bound : ∀r∈[Reg.x1,.x2],∀j<n,∀k<256,
    (coeffAt s.mem (s.gpr r+BitVec.ofNat 64 (1024*j)) k).toNat<3*q

def inputWord (s : State) (r : Reg) (j k : Nat) : BitVec 32 :=
  coeffAt s.mem (s.gpr r+BitVec.ofNat 64 (1024*j)) k

theorem input_current {s₀ s : State} {v : Nat→Nat} {i n : Nat} (hi : i<64)
    (hp : Pre n s₀) (h : Inv s₀ v i s) {r : Reg} (hr : r∈[Reg.x1,.x2]) {j e : Nat}
    (hj : j<n) (he : e<4) : dotInput s r 0 j e=inputWord s₀ r j (4*i+e) := by
  have ha : s.gpr r=coeffAddr (s₀.gpr r) (4*i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.x1
    · exact h.x2
  have addr : s.gpr r+BitVec.ofNat 64 (1024*j+0)=
      coeffAddr (s₀.gpr r+BitVec.ofNat 64 (1024*j)) (4*i) := by
    rw [ha]
    simp only [coeffAddr,Nat.add_zero]
    bv_omega
  unfold dotInput inputWord
  rw [addr,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq]
  exact coeffAt_frame h.frame (by intro r' hr';have hh:=List.mem_singleton.mp hr';subst r';exact hp.apart r hr j hj) (by change 4*i+e<256;omega)

theorem reads {s₀ s : State} {v : Nat→Nat} {i n : Nat} (hi : i<64)
    (hp : Pre n s₀) (h : Inv s₀ v i s) {r : Reg} (hr : r∈[Reg.x1,.x2]) {j : Nat}
    (hj : j<n) : InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (1024*j)) 16 := by
  have ha : s.gpr r=coeffAddr (s₀.gpr r) (4*i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.x1
    · exact h.x2
  rw [h.keep.rd,h.keep.wr,ha]
  have addr : coeffAddr (s₀.gpr r) (4*i)+BitVec.ofNat 64 (1024*j)=
      coeffAddr (s₀.gpr r+BitVec.ofNat 64 (1024*j)) (4*i) := by
    simp only [coeffAddr];bv_omega
  rw [addr]
  exact VG.CallLay.inRegions_sub (off:=4*(4*i)) (l:=16) (hp.input r hr j hj) (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

def result (s : State) (n k : Nat) : Nat :=
  mont (dotNat (fun j=>inputWord s .x1 j k) (fun j=>inputWord s .x2 j k) n)%q

theorem result_current {s₀ s : State} {v : Nat→Nat} {i n e : Nat}
    (hi : i<64) (hn : n≤7) (he : e<4) (hp : Pre n s₀) (h : Inv s₀ v i s) :
    mont (dotAccum s 0 n e).toNat%q=result s₀ n (4*i+e) := by
  have ha (j : Nat) (hj : j<n) :=  input_current hi hp h (r:=Reg.x1) (by simp) (j:=j) hj he
  have hb (j : Nat) (hj : j<n) :=  input_current hi hp h (r:=Reg.x2) (by simp) (j:=j) hj he
  have halt : ∀j<n,(dotInput s .x1 0 j e).toNat<3*q := by
    intro j hj;rw [ha j hj];exact hp.bound .x1 (by simp) j hj _ (by omega)
  have hblt : ∀j<n,(dotInput s .x2 0 j e).toNat<3*q := by
    intro j hj;rw [hb j hj];exact hp.bound .x2 (by simp) j hj _ (by omega)
  rw [dotAccum,dotWord_nat _ _ hn halt hblt,dotNat_congr _ _ _ _ n ha hb]
  rfl

theorem run_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) (s₀ : State) (hp : Pre n s₀) :
    WP isa (Impl.MlDsa.AArch64.Optimized.MontDot.dot n) s₀ (Inv s₀ (result s₀ n) 64) := by
  unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
  refine WP.seq (WP.mono (pro_ok s₀ (result s₀ n)) fun s ⟨hs,hcnt⟩=>?_)
  refine VG.Proof.MlDsa.AArch64.Arith.wp_countdown (cnt:=.x12) (N:=64)
    (by decide) (by decide) (Inv s₀ _) (fun i hi s h _=>?_) hs hcnt
  have hr (j : Nat) (hj : j<n) :=  And.intro (reads hi hp h (r:=Reg.x1) (by simp) (j:=j) hj)
    (reads hi hp h (r:=Reg.x2) (by simp) (j:=j) hj)
  have ha : ∀j<n,∀e<4,(dotInput s .x1 0 j e).toNat<3*q := by
    intro j hj e he
    rw [input_current hi hp h (r:=Reg.x1) (by simp) (j:=j) hj he]
    exact hp.bound .x1 (by simp) j hj _ (by omega)
  have hb : ∀j<n,∀e<4,(dotInput s .x2 0 j e).toNat<3*q := by
    intro j hj e he
    rw [input_current hi hp h (r:=Reg.x2) (by simp) (j:=j) hj he]
    exact hp.bound .x2 (by simp) j hj _ (by omega)
  have hw : InRegions s.wr (s.gpr .x0) 16 := by
    rw [h.keep.wr,h.x0]
    exact ⟨_,hp.output,Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (body_ok hn hn7 h.consts hr ha hb hw) fun t ⟨x,hm,hx,hc,h0,h1,h2,h12,hk⟩=>?_
  refine ⟨inv_step hi h hm ?_ hc h0 h1 h2 hk,h12⟩
  intro e he
  exact (hx e he).trans (result_current hi hn7 he hp h)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

 theorem montCanonical_eq (a : Nat) : ofNat (mont a%q)=ofInt ((mont a:Int)-q) := by
  apply Fin.ext
  simp only [ofNat,Fin.val_ofNat,Nat.mod_mod]
  have h := VG.Proof.MlDsa.KeyGen.ofInt_val ((mont a:Int)-q)
  apply Int.ofNat_inj.mp
  rw [h,Int.natCast_emod]
  change (mont a:Int)%8380417=((mont a:Int)-8380417)%8380417
  omega

def value (s : State) (n : Nat) : Poly :=
  (dotNTT (fun j=>polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j=>polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) n).map (· * montgomeryRInv)

theorem result_field (s : State) {n : Nat} (hn : n≤7) (hp : Pre n s) {i : Nat} (hi : i<256) :
    ofNat (result s n i)=(value s n)[i]! := by
  have ha : ∀j<n,(inputWord s .x1 j i).toNat<3*q := fun j hj=>hp.bound .x1 (by simp) j hj i hi
  have hb : ∀j<n,(inputWord s .x2 j i).toNat<3*q := fun j hj=>hp.bound .x2 (by simp) j hj i hi
  have hf := centeredDot_field (fun j=>inputWord s .x1 j i) (fun j=>inputWord s .x2 j i)
    (fun j=>polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j=>polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) hn ha hb hi
    (fun j _=>by rw [ofInt_nat_eq];exact (polyAt_get _ _ hi).symm)
    (fun j _=>by rw [ofInt_nat_eq];exact (polyAt_get _ _ hi).symm)
  rw [centeredDot_int _ _ hn ha hb] at hf
  rw [result,montCanonical_eq]
  exact hf

theorem result_value (s : State) {n : Nat} (hn : n≤7) (hp : Pre n s) {i : Nat} (hi : i<256) :
    result s n i=((value s n)[i]!).val := by
  have h := congrArg Fin.val (result_field s hn hp hi)
  rw [ofNat,Fin.val_ofNat,Nat.mod_eq_of_lt (show result s n i<q from Nat.mod_lt _ (by decide))] at h
  exact h

theorem output_ok {s₀ s : State} {n : Nat} (hn : n≤7) (hp : Pre n s₀)
    (h : Inv s₀ (result s₀ n) 64 s) : PolyIs s.mem (s₀.gpr .x0) (value s₀ n) := by
  apply polyIs_of_toNat
  intro i hi
  rw [h.coeff i hi,ite_eq_left (by change i<256;exact hi)]
  exact result_value s₀ hn hp hi

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

def contract (n : Nat) : Contract isa where
  pre := Pre n
  post s t := PolyIs t.mem (s.gpr .x0) (value s n)
  pub s t := (∀r∈[Reg.x0,.x1,.x2],s.gpr r=t.gpr r) ∧ s.sp=t.sp

theorem pre {n : Nat} (hn : n≤7) {s : State} (h : (montDotContract abi n).pre s) : Pre n s := by
  sig_pre [montDotContract,montDotSig,abi,argRegs,stackBelow] at h
  have he : 256*n*4=1024*n := by omega
  rw [he] at h
  obtain ⟨hr,hw,ha,hb,_,_,_,hpa,hpb⟩ := h
  refine ⟨by rw [hw];simp [pR],?_,?_,?_⟩
  · intro r hr' j hj
    apply VG.CallLay.inRegions_sub (n:=1024*n) (off:=1024*j) (l:=1024)
    · refine ⟨⟨s.gpr r,1024*n⟩,?_,by simp [Region.Contains]⟩
      rw [hr]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
      rcases hr' with rfl|rfl <;> simp
    · omega
    · omega
  · intro r hr' j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact ha.symm.sub_left (Offset.sub_base _ (by omega))
    · exact hb.symm.sub_left (Offset.sub_base _ (by omega))
  · intro r hr' j hj i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact hpa j hj i hi
    · exact hpb j hj i hi

theorem correct {n : Nat} (hc : n=4∨n=5∨n=7) (s : State) (hp : (contract n).pre s) :
    ∃tr t,Exec isa (VG.Impl.MlDsa.AArch64.Optimized.MontDot.dot n) s tr t ∧
      abiPreserved s t ∧ (contract n).post s t := by
  obtain ⟨tr,t,he,hi⟩ := run_ok (by omega) (by omega) s hp
  refine ⟨tr,t,he,?_,output_ok (by omega) hp hi⟩
  rcases hc with rfl|rfl|rfl
  all_goals exact VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he (by decide +kernel)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end
