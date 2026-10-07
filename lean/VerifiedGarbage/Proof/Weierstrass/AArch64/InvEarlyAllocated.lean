import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarly
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.InvAllocated
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (inverseBatch)

abbrev invAllocatedCfg := p256.invN

def invAllocatedRegs : List Reg := .x19::allocatedRegs

def invAllocatedBatchW : List (Nat × Nat) := batchW invAllocatedCfg ++ [(7104,576)]

def invAllocatedW : List (Nat × Nat) := invW invAllocatedCfg ++ [(7104,576)]

private theorem wp_both {c : Prog isa} {s : State} {P Q : State → Prop}
    (hp : WP isa c s P) (hq : WP isa c s Q) : WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨tr,t,ht,hp⟩ := hp
  obtain ⟨tr',t',ht',hq⟩ := hq
  obtain ⟨rfl,rfl⟩ := ht.det ht'
  exact ⟨_,_,ht,hp,hq⟩

private theorem word_values {m m' : Mem} {base : Addr} {a n : Nat}
    (h : ∀ i<n,word m base (a+8*i)=word m' base (a+8*i)) :
    wordsVal m base a n=wordsVal m' base a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [wordsVal]
    rw [show word m base a=word m' base a by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by omega)]
    rw [ih (a:=a+8) (fun i hi => by rw [show a+8+8*i=a+8*(i+1) by omega]; exact h (i+1) (by omega))]

 theorem invAllocated_update_clob : ∀ r∈Forward.InvAllocated.optimized.flatMap Forward.instrClob,
    r∈allocatedRegs := by
  rw [Forward.InvAllocated.rightCode.lit_eq]
  decide +kernel

 theorem invAllocated_update_writes : ∀ w∈Forward.InvAllocated.optimized.flatMap Forward.instrWrites,
    ∃ w'∈invAllocatedBatchW,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [Forward.InvAllocated.rightCode.lit_eq]
  decide +kernel

/-- Allocating the update preserves the divstep invariant, delta and loop counter;
only the explicit allocator spill area and register set widen the internal frame. -/
theorem invAllocated_batch_ok {base : Addr} {size m : Nat} (hsize : 8192≤size)
    (hL : InvLay invAllocatedCfg size) {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size m s.mem base) {I : Divstep.IState}
    (hI : IInv invAllocatedCfg base I s)
    (hd : |I.d|≤2^30) (hf1 : I.f%2=1) (hf : |I.f|≤m) (hg : |I.g|≤m)
    (ha : |I.a|≤m) (hb : |I.b|≤m) {j : Nat} (hj : 1≤j) (hj' : j<2^64)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa inverseBatch s fun t =>
      IInv invAllocatedCfg base (Divstep.batch 59 m invAllocatedCfg.M.minv.toNat I) t ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedBatchW s.mem t.mem := by
  have hb0 := batch_ok hL hs hM hI hd hf1 hf hg ha hb hj hj' h19
  have hw := words_ok hL hs hI hd hf1 hj hj' h19
  rw [InvCfg.batch] at hb0
  rw [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.inverseBatch]
  refine WP.seq (WP.mono (wp_both (WP.seq_iff.mp hb0) hw) fun a ⟨qa,wa⟩ => ?_)
  refine WP.seq (WP.mono (wp_both (WP.seq_iff.mp qa) wa) fun b ⟨qb,wb⟩ => ?_)
  obtain ⟨bd,bu,bv,bq,br,b19,bmem,bkeep⟩ := wb
  have hsb := hs.of_keepRegs bkeep (by decide)
  refine WP.mono (Forward.InvAllocated.refine hsb hsize qb) fun t ⟨u,qu,hu,kt,ut⟩ => ?_
  obtain ⟨iu,u19,ku,uu⟩ := qu
  have heq : ∀ a∈[invAllocatedCfg.sF,invAllocatedCfg.sG,invAllocatedCfg.sA,invAllocatedCfg.sB],
      ∀ n≤5,wordsVal t.mem base a n=wordsVal u.mem base a n := by
    intro a ha n hn
    change a∈[2272,2312,2352,2384] at ha
    apply word_values
    intro i hi
    apply hu
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> change _<7104 ∨ 7680≤_ <;> left <;> omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hnot1 : Reg.x1∉Forward.InvAllocated.optimized.flatMap Forward.instrClob :=
    fun hr => (Forward.InvAllocated.keepsDeltaCounter _ hr).1 rfl
  have hnot19 : Reg.x19∉Forward.InvAllocated.optimized.flatMap Forward.instrClob :=
    fun hr => (Forward.InvAllocated.keepsDeltaCounter _ hr).2 rfl
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · rw [kt.gpr _ hnot1]
    simpa only [Divstep.batch] using bd
  · rw [heq _ (by simp) _ (by decide)]; exact iu.f
  · rw [heq _ (by simp) _ (by decide)]; exact iu.g
  · rw [heq _ (by simp) _ (by decide)]; exact iu.a
  · rw [heq _ (by simp) _ (by decide)]; exact iu.b
  · rw [kt.gpr _ hnot19]; exact b19
  · exact (bkeep.mono (by decide)).trans (kt.mono fun r hr => List.mem_cons_of_mem _ (invAllocated_update_clob r hr))
  · have h := ut.cover invAllocated_update_writes
    rw [bmem] at h
    exact h

/-- The inversion modulus lies outside both the arithmetic workspace and allocator spills. -/
theorem invAllocated_mod {base : Addr} {size m : Nat} {s t : State}
    (hs : Scr s base size) (hM : ModOkA invAllocatedCfg.M size m s.mem base)
    (hU : Unch base invAllocatedBatchW s.mem t.mem) : ModOkA invAllocatedCfg.M size m t.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red⟩
  rw [hU.wordsVal (by decide) (by omega_using [hM.mo,hs.nowrap])]
  exact hM.val

 theorem invAllocated_batch_frame {base : Addr} {s t : State}
    (hU : Unch base invAllocatedBatchW s.mem t.mem) : Unch base invAllocatedW s.mem t.mem := by
  apply hU.cover
  decide

 theorem invAllocated_loop_ok {base : Addr} {size m B : Nat} (hsize : 8192≤size)
    (hL : InvLay invAllocatedCfg size) {s : State} (hs : Scr s base size)
    (hM : ModOkA invAllocatedCfg.M size m s.mem base) {X : Nat} (hX : X<m)
    (hm2 : m%2=1) (hm1 : 1<m) (hB1 : 1≤B) (hB : B<2^16)
    (hI : IInv invAllocatedCfg base (Divstep.invRun 59 m invAllocatedCfg.M.minv.toNat X 0) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 B) :
    WP isa (.loop inverseBatch (.nonzero .x .x19)) s fun t =>
      IInv invAllocatedCfg base (Divstep.invRun 59 m invAllocatedCfg.M.minv.toNat X B) t ∧
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedBatchW s.mem t.mem := by
  have hmi : ((m : Int)*(invAllocatedCfg.M.minv.toNat : Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n:=B) (by omega)
    (Inv:=fun j t => IInv invAllocatedCfg base (Divstep.invRun 59 m invAllocatedCfg.M.minv.toNat X (B-j)) t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ Scr t base size ∧ ModOkA invAllocatedCfg.M size m t.mem base ∧
      KeepRegs invAllocatedRegs s t ∧ Unch base invAllocatedBatchW s.mem t.mem)
    (fun j t hj1 hjB ⟨it,xt,st,mt,kt,ut⟩ => ?_)
    (fun t ⟨it,_,_,_,kt,ut⟩ => ⟨by simpa only [Nat.sub_zero] using it,kt,ut⟩)
    hB1 ⟨by rw [Nat.sub_self]; exact hI,h19,hs,hM,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl _ _ _⟩
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=m) (m:=invAllocatedCfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2)
    (by exact_mod_cast hm1) hmi (by omega) (by exact_mod_cast hX) (B-j)
  refine WP.mono (invAllocated_batch_ok hsize hL st mt it (by
    have hh : ((59*(B-j) : Nat) : Int)≤59*2^16 := by exact_mod_cast (Nat.mul_le_mul_left 59 (by omega : B-j≤2^16))
    omega) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le)
    (by rw [abs_of_nonneg bb0]; exact bb1.le) hj1 (by omega) xt)
    fun u ⟨iu,xu,ku,uu⟩ => ⟨⟨?_,xu,st.of_keepRegs ku (by decide),invAllocated_mod st mt uu,
      kt.trans ku,fun x hx => (uu x hx).trans (ut x hx)⟩,xu⟩
  rw [show B-(j-1)=B-j+1 by omega]
  exact iu

end VG.Proof.Weierstrass.AArch64
