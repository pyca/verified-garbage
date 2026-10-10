import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalSlice
import VerifiedGarbage.Proof.MlDsa.Arith.Pairs

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlDsa.Pairs
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- A uniform signed bound for the eight logical SIMD registers. -/
def BankBound (v : Vector (BitVec 128) 8) (b : Int) : Prop :=
  ∀ i : Fin 8, ∀ e<4, -b≤(vword v[i.val] e).toInt ∧ (vword v[i.val] e).toInt≤b

theorem afterValues_eq (v : Vector (BitVec 128) 8) (ps : List (Fin 8 × Fin 8)) :
    afterValues v ps = pairsApply (fun a b => (VArr.s4.map2 (fun _ a b => a+b) a b,
      VArr.s4.map2 (fun _ a b => a-b) a b)) v ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => obtain ⟨i, j⟩ := p; exact ih _

/-- Entry `k` is the first of a pair of the group: its pair and which entries are products. -/
def LeftFacts (gap g : Nat) : Prop := ∀ k : Fin 8, 2*gap*g≤k.val ∧ k.val<2*gap*g+gap →
  pairOf (groupSteps gap g) k = some (k, ⟨(k.val+gap)%8, Nat.mod_lt _ (by decide)⟩) ∧ k.val+gap<8 ∧
  k ∉ (groupIndexedProducts gap g).map Prod.fst ∧
  (⟨(k.val+gap)%8, Nat.mod_lt _ (by decide)⟩ : Fin 8) ∈ (groupIndexedProducts gap g).map Prod.fst

/-- Entry `k` is the second of a pair of the group. -/
def RightFacts (gap g : Nat) : Prop := ∀ k : Fin 8, 2*gap*g+gap≤k.val ∧ k.val<2*gap*g+2*gap →
  pairOf (groupSteps gap g) k = some (⟨(k.val-gap)%8, Nat.mod_lt _ (by decide)⟩, k) ∧ gap≤k.val ∧
  (⟨(k.val-gap)%8, Nat.mod_lt _ (by decide)⟩ : Fin 8) ≠ k ∧
  (⟨(k.val-gap)%8, Nat.mod_lt _ (by decide)⟩ : Fin 8) ∉ (groupIndexedProducts gap g).map Prod.fst ∧
  k ∈ (groupIndexedProducts gap g).map Prod.fst

/-- Entry `k` is in no pair of the group. -/
def RestFacts (gap g : Nat) : Prop := ∀ k : Fin 8,
  ¬(2*gap*g≤k.val ∧ k.val<2*gap*g+gap) → ¬(2*gap*g+gap≤k.val ∧ k.val<2*gap*g+2*gap) →
  pairOf (groupSteps gap g) k = none ∧ k ∉ (groupIndexedProducts gap g).map Prod.fst

/-- Where each entry of a butterfly group comes from: finite facts for each valid group. -/
theorem groupFacts {gap g : Nat} (hg : ValidGroup gap g) : (entries (groupSteps gap g)).Nodup ∧
    LeftFacts gap g ∧ RightFacts gap g ∧ RestFacts gap g := by
  have h : ∀ p ∈ [(4,0),(2,0),(2,1),(1,0),(1,1),(1,2),(1,3)], (entries (groupSteps p.1 p.2)).Nodup ∧
      LeftFacts p.1 p.2 ∧ RightFacts p.1 p.2 ∧ RestFacts p.1 p.2 := by
    have h0 : ∀ p ∈ [(4,0),(2,0),(2,1),(1,0),(1,1),(1,2),(1,3)], (entries (groupSteps p.1 p.2)).Nodup := by
      decide +kernel
    have h1 : ∀ p ∈ [(4,0),(2,0),(2,1),(1,0),(1,1),(1,2),(1,3)], LeftFacts p.1 p.2 := by
      unfold LeftFacts; decide +kernel
    have h2 : ∀ p ∈ [(4,0),(2,0),(2,1),(1,0),(1,1),(1,2),(1,3)], RightFacts p.1 p.2 := by
      unfold RightFacts; decide +kernel
    have h3 : ∀ p ∈ [(4,0),(2,0),(2,1),(1,0),(1,1),(1,2),(1,3)], RestFacts p.1 p.2 := by
      unfold RestFacts; decide +kernel
    exact fun p hp => ⟨h0 p hp, h1 p hp, h2 p hp, h3 p hp⟩
  rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ | ⟨rfl,hg⟩
  · exact h (4,0) (by simp)
  · exact h (2,0) (by simp)
  · exact h (2,1) (by simp)
  · rcases (show g=0 ∨ g=1 ∨ g=2 ∨ g=3 by omega) with rfl|rfl|rfl|rfl
    · exact h (1,0) (by simp)
    · exact h (1,1) (by simp)
    · exact h (1,2) (by simp)
    · exact h (1,3) (by simp)

/-- Exact word result of one independent butterfly group. -/
theorem coreValues_word (v : Vector (BitVec 128) 8) {gap g : Nat} (hg : ValidGroup gap g)
    (z : Nat → Int) (i : Fin 8) {e : Nat} (he : e<4) :
    vword (coreValues v gap g z)[i.val] e =
      if 2*gap*g≤i.val ∧ i.val<2*gap*g+gap then
        vword v[i.val] e + fastMulWord (vword v[i.val+gap]! e) (z e)
      else if 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap then
        vword v[i.val-gap]! e - fastMulWord (vword v[i.val] e) (z e)
      else vword v[i.val] e := by
  obtain ⟨hd, hL, hR, hN⟩ := groupFacts hg
  rw [coreValues, afterValues_eq, pairsApply_get _ _ hd i]
  by_cases h1 : 2*gap*g≤i.val ∧ i.val<2*gap*g+gap
  · obtain ⟨hp, hlt, hni, hj⟩ := hL i h1
    simp only [Nat.mod_eq_of_lt hlt] at hp hj
    rw [hp]
    simp only [h1, and_self, ite_true, productValues, Vector.getElem_ofFn, hni, hj, ite_false, vword_map2 _ _ _ he,
      fastVector_word _ _ he, getElem!_pos v (i.val+gap) hlt]
  · simp only [h1, ite_false]
    by_cases h2 : 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap
    · obtain ⟨hp, hle, hne, hni, hj⟩ := hR i h2
      have hlt : i.val-gap<8 := by omega
      simp only [Nat.mod_eq_of_lt hlt] at hp hne hni
      rw [hp]
      simp only [h2, and_self, hne, ite_false, productValues, Vector.getElem_ofFn, hni, hj, ite_true, vword_map2 _ _ _ he,
        fastVector_word _ _ he, getElem!_pos v (i.val-gap) hlt]
    · obtain ⟨hp, hni⟩ := hN i h1 h2
      rw [hp]
      simp only [h2, productValues, Vector.getElem_ofFn, hni, ite_false]

theorem ValidGroup.bounds {gap g : Nat} (hg : ValidGroup gap g) :
    0<gap ∧ 2*gap*g+2*gap≤8 := by
  rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · decide
  · rcases hg with rfl | rfl <;> decide
  · omega

/-- The coarse group bound keeps every scalar addition exact as a signed word. -/
theorem coreValues_int (v : Vector (BitVec 128) 8) {gap g : Nat} (hg : ValidGroup gap g)
    (z : Nat → Int) {b : Int} (hb : 0≤b) (hs : b+16760834<2147483648)
    (hv : BankBound v b) (i : Fin 8) {e : Nat} (he : e<4) :
    (vword (coreValues v gap g z)[i.val] e).toInt =
      if 2*gap*g≤i.val ∧ i.val<2*gap*g+gap then
        (vword v[i.val] e).toInt + fastMul (vword v[i.val+gap]! e).toInt (z e)
      else if 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap then
        (vword v[i.val-gap]! e).toInt - fastMul (vword v[i.val] e).toInt (z e)
      else (vword v[i.val] e).toInt := by
  rw [coreValues_word v hg z i he]
  split
  · rename_i hi
    have ha := hv i e he
    have hm := fastMul_bounds (z := z e) (BitVec.le_toInt (vword v[i.val+gap]! e))
      (BitVec.toInt_lt (x := vword v[i.val+gap]! e))
    rw [addWord_int _ _ (by rw [fastMulWord_int]; omega) (by rw [fastMulWord_int]; omega), fastMulWord_int]
  · split
    · rename_i hi
      have hidx : i.val-gap<8 := by omega
      have ha := hv ⟨i.val-gap,hidx⟩ e he
      have hae : v[i.val-gap]! = v[i.val-gap] := getElem!_pos v _ hidx
      rw [← hae] at ha
      have hm := fastMul_bounds (z := z e) (BitVec.le_toInt (vword v[i.val] e))
        (BitVec.toInt_lt (x := vword v[i.val] e))
      rw [subWord_int _ _ (by rw [fastMulWord_int]; omega) (by rw [fastMulWord_int]; omega), fastMulWord_int]
    · rfl

theorem coreValues_bound (v : Vector (BitVec 128) 8) {gap g : Nat} (hg : ValidGroup gap g)
    (z : Nat → Int) {b : Int} (hb : 0≤b) (hs : b+16760834<2147483648)
    (hv : BankBound v b) : BankBound (coreValues v gap g z) (b+16760834) := by
  intro i e he
  rw [coreValues_int v hg z hb hs hv i he]
  split
  · have ha := hv i e he
    have hm := fastMul_bounds (z := z e) (BitVec.le_toInt (vword v[i.val+gap]! e))
      (BitVec.toInt_lt (x := vword v[i.val+gap]! e))
    omega
  · split
    · have hidx : i.val-gap<8 := by omega
      have ha := hv ⟨i.val-gap,hidx⟩ e he
      have hae : v[i.val-gap]! = v[i.val-gap] := getElem!_pos v _ hidx
      rw [← hae] at ha
      have hm := fastMul_bounds (z := z e) (BitVec.le_toInt (vword v[i.val] e))
        (BitVec.toInt_lt (x := vword v[i.val] e))
      omega
    · have ha := hv i e he; omega

open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Logical bank lanes represent the corresponding strided field coefficients. -/
def BankField (u : Nat) (v : Vector (BitVec 128) 8) (w : Poly) : Prop :=
  ∀ i : Fin 8, ∀ e<4, ofInt (vword v[i.val] e).toInt=w[Traversal.loc u i.val e]!

theorem coreValues_field (v : Vector (BitVec 128) 8) (w : Poly) {gap g u : Nat}
    (hg : ValidGroup gap g) (hu : u<8) (rootIndex : Nat) {b : Int}
    (hb : 0≤b) (hs : b+16760834<2147483648) (hv : BankBound v b) (hf : BankField u v w) :
    BankField u (coreValues v gap g (fun _ => (zetaNat rootIndex : Int)))
      (Traversal.run (Traversal.regGroupSchedule u (2*gap*g) gap rootIndex) w) := by
  intro i e he
  rw [coreValues_int v hg _ hb hs hv i he,Traversal.run_regGroup,
    Traversal.regBlock_get _ hg.bounds.1 hg.bounds.2 hu (Nat.le_refl _) _ i.isLt he,
    show 2*gap*g+gap+gap=2*gap*g+2*gap by omega]
  by_cases hl : 2*gap*g≤i.val ∧ i.val<2*gap*g+gap
  · rw [ite_eq_left hl,ite_eq_left hl,ofInt_add,fastMul_field,Traversal.ofInt_zetaNat,hf i e he]
    have hidx : i.val+gap<8 := by have := hg.bounds.2; omega
    have hae : v[i.val+gap]! = v[i.val+gap] := getElem!_pos v _ hidx
    rw [hae,hf ⟨i.val+gap,hidx⟩ e he,Fin.mul_comm]
  · rw [ite_eq_right hl,ite_eq_right hl]
    by_cases hr : 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap
    · rw [ite_eq_left hr,ite_eq_left hr,ofInt_sub,fastMul_field,Traversal.ofInt_zetaNat,hf i e he]
      have hidx : i.val-gap<8 := by omega
      have hae : v[i.val-gap]! = v[i.val-gap] := getElem!_pos v _ hidx
      rw [hae,hf ⟨i.val-gap,hidx⟩ e he,Fin.mul_comm]
    · rw [ite_eq_right hr,ite_eq_right hr,hf i e he]

def outerGroupSchedule (u : Nat) (p : Nat × Nat) : List Traversal.Op :=
  Traversal.regGroupSchedule u (2*p.1*p.2) p.1 (4/p.1+p.2)

theorem outerValues_field (v : Vector (BitVec 128) 8) (w : Poly) (ps : List (Nat × Nat))
    (hps : ∀ p∈ps,ValidGroup p.1 p.2) {u : Nat} (hu : u<8) {b : Int}
    (hb : 0≤b) (hs : b+16760834*(ps.length : Int)<2147483648)
    (hv : BankBound v b) (hf : BankField u v w) :
    BankBound (outerValues v (fun k => (zetaNat k : Int)) ps) (b+16760834*(ps.length : Int)) ∧
    BankField u (outerValues v (fun k => (zetaNat k : Int)) ps)
      (Traversal.run (ps.flatMap (outerGroupSchedule u)) w) := by
  induction ps generalizing v w b with
  | nil => simpa only [outerValues,List.length_nil,Int.natCast_zero,Int.mul_zero,Int.add_zero,
      List.flatMap_nil,Traversal.run,List.foldl_nil] using And.intro hv hf
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hs' : b+16760834<2147483648 := by
      simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs; omega
    have hb' := coreValues_bound v hp (fun _ => (zetaNat (4/p.1+p.2) : Int)) hb hs' hv
    have hf' := coreValues_field v w hp hu (4/p.1+p.2) hb hs' hv hf
    have hh := ih (coreValues v p.1 p.2 (fun _ => (zetaNat (4/p.1+p.2) : Int)))
      (Traversal.run (outerGroupSchedule u p) w) (fun a ha => hps a (by simp [ha]))
      (b := b+16760834) (by omega) (by
        simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs
        omega) hb' hf'
    simpa only [outerValues,List.length_cons,Int.natCast_add,Int.natCast_one,List.flatMap_cons,
      Traversal.run_append,show b+16760834*((ps.length : Int)+1)=
        (b+16760834)+16760834*(ps.length : Int) by omega] using hh

theorem outerGroupSchedule_eq (u : Nat) :
    outerSteps.flatMap (outerGroupSchedule u)=Traversal.outerSlice u := by
  simp [outerSteps,outerGroupSchedule,Traversal.regGroupSchedule,Traversal.outerSlice,
    Traversal.loc,List.range_succ,Nat.mul_add,Nat.add_assoc]

theorem outerThree_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : BankField u v w) :
    BankBound (outerValues v (fun k => (zetaNat k : Int)) outerSteps) (15*8380417) ∧
    BankField u (outerValues v (fun k => (zetaNat k : Int)) outerSteps)
      (Traversal.run (Traversal.outerSlice u) w) := by
  have h := outerValues_field v w outerSteps outerSteps_valid hu (by decide) (by decide) hv hf
  rw [outerGroupSchedule_eq] at h
  exact h

end VG.Proof.MlDsa.AArch64.Optimized
