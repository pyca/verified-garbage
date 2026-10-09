import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalSlice

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- A uniform signed bound for the eight logical SIMD registers. -/
def BankBound (v : Vector (BitVec 128) 8) (b : Int) : Prop :=
  ∀ i : Fin 8, ∀ e<4, -b≤(vword v[i.val] e).toInt ∧ (vword v[i.val] e).toInt≤b

/-- Exact word result of one independent butterfly group. -/
theorem coreValues_word (v : Vector (BitVec 128) 8) {gap g : Nat} (hg : ValidGroup gap g)
    (z : Nat → Int) (i : Fin 8) {e : Nat} (he : e<4) :
    vword (coreValues v gap g z)[i.val] e =
      if 2*gap*g≤i.val ∧ i.val<2*gap*g+gap then
        vword v[i.val] e + fastMulWord (vword v[i.val+gap]! e) (z e)
      else if 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap then
        vword v[i.val-gap]! e - fastMulWord (vword v[i.val] e) (z e)
      else vword v[i.val] e := by
  rcases i with ⟨i,hi⟩
  have hs : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,hg⟩ | ⟨rfl,hg⟩
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [coreValues,groupIndexedProducts,groupSteps,afterValues,pairValues,productValues,
        prodTemps,show (3 : Fin 8).val=3 from rfl,show (4 : Fin 8).val=4 from rfl,show (5 : Fin 8).val=5 from rfl,show (6 : Fin 8).val=6 from rfl,show (7 : Fin 8).val=7 from rfl, fastVector_word _ _ he, vword_map2 _ _ _ he]
  · rcases hg with rfl | rfl <;>
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [coreValues,groupIndexedProducts,groupSteps,afterValues,pairValues,productValues,
        prodTemps,show (3 : Fin 8).val=3 from rfl,show (4 : Fin 8).val=4 from rfl,show (5 : Fin 8).val=5 from rfl,show (6 : Fin 8).val=6 from rfl,show (7 : Fin 8).val=7 from rfl, fastVector_word _ _ he, vword_map2 _ _ _ he]
  · have hs' : g=0 ∨ g=1 ∨ g=2 ∨ g=3 := by omega
    rcases hs' with rfl | rfl | rfl | rfl <;>
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [coreValues,groupIndexedProducts,groupSteps,afterValues,pairValues,productValues,
        prodTemps,show (3 : Fin 8).val=3 from rfl,show (4 : Fin 8).val=4 from rfl,show (5 : Fin 8).val=5 from rfl,show (6 : Fin 8).val=6 from rfl,show (7 : Fin 8).val=7 from rfl, fastVector_word _ _ he, vword_map2 _ _ _ he]

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
