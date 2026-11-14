module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalSlice
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.AArch64.Optimized.InnerTraversal`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerLoc (u i e : Nat) : Nat := 32*u+4*i+e

def innerRegBlock (w : Poly) (base gap u : Nat) (z : Zq) (t : Nat) : Poly :=
  (List.range t).foldl (fun w j => blockN bfly w (4*gap) z (innerLoc u (base+j) 0) 4) w

/-- A register group's first t butterflies update exactly its selected register
pairs, independently in each of the four lanes. -/
theorem innerRegBlock_get (w : Poly) {base gap u t : Nat} (hgap : 0<gap)
    (hb : base+2*gap≤8) (hu : u<8) (ht : t≤gap) (z : Zq)
    {i e : Nat} (hi : i<8) (he : e<4) :
    (innerRegBlock w base gap u z t)[innerLoc u i e]! =
      if base≤i ∧ i<base+t then w[innerLoc u i e]! + z*w[innerLoc u (i+gap) e]!
      else if base+gap≤i ∧ i<base+gap+t then w[innerLoc u (i-gap) e]! - z*w[innerLoc u i e]!
      else w[innerLoc u i e]! := by
  induction t generalizing i with
  | zero =>
    simp only [innerRegBlock,List.range_zero,List.foldl_nil,Nat.add_zero]
    rw [ite_eq_right (by omega_using []),ite_eq_right (by omega_using [])]
  | succ t ih =>
    rw [innerRegBlock,foldl_range_succ]
    change (blockN bfly (innerRegBlock w base gap u z t) (4*gap) z (innerLoc u (base+t) 0) 4)[innerLoc u i e]! = _
    rw [blockPrefix_get _ (by omega_using [hgap]) (by omega_using [hgap]) (by unfold innerLoc n; omega_using [hb, hu, ht]) (by unfold innerLoc n; omega_using [hu, he, hi])]
    by_cases ha : i=base+t
    · subst i
      rw [ite_eq_left (by unfold innerLoc; omega_using [he]),
        show innerLoc u (base+t) e+4*gap=innerLoc u (base+t+gap) e by unfold innerLoc; omega_using [],
        ih (by omega_using [ht]) hi, ih (by omega_using [ht]) (by omega_using [hb, ht])]
      simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · by_cases hd : i=base+t+gap
      · subst i
        rw [ite_eq_right (by unfold innerLoc; omega_using [hgap]),ite_eq_left (by unfold innerLoc; omega_using [he]),
          show innerLoc u (base+t+gap) e-4*gap=innerLoc u (base+t) e by unfold innerLoc; omega_using [],
          ih (by omega_using [ht]) hi,ih (by omega_using [ht]) (by omega_using [hb, ht])]
        simp (disch := omega) only [ite_eq_left,ite_eq_right]
        rw [Nat.add_sub_cancel]
      · rw [ite_eq_right (by unfold innerLoc; omega_using [he, ha]),ite_eq_right (by unfold innerLoc; omega_using [he, hd]),ih (by omega_using [ht]) hi]
        have h1 : (base≤i ∧ i<base+t) ↔ (base≤i ∧ i<base+(t+1)) := by omega_using [ha]
        have h2 : (base+gap≤i ∧ i<base+gap+t) ↔ (base+gap≤i ∧ i<base+gap+(t+1)) := by omega_using [hd]
        simp only [h1,h2]

def innerRegGroupSchedule (u base gap rootIndex : Nat) : List Op :=
  (List.range gap).flatMap fun j => (List.range 4).map fun e =>
    ⟨innerLoc u (base+j) e,4*gap,rootIndex⟩

theorem run_innerRegGroup (w : Poly) (u base gap rootIndex : Nat) :
    run (innerRegGroupSchedule u base gap rootIndex) w=
      innerRegBlock w base gap u (zetas rootIndex) gap := by
  unfold run innerRegGroupSchedule innerRegBlock
  rw [List.foldl_flatMap]
  apply congrArg (fun f => (List.range gap).foldl f w)
  funext p j
  rw [List.foldl_map]
  unfold blockN
  rw [List.range'_eq_map_range,List.foldl_map]
  apply congrArg (fun f => (List.range 4).foldl f p)
  funext p e
  change bfly p (innerLoc u (base+j) e) (4*gap) (zetas rootIndex)=
    bfly p (innerLoc u (base+j) 0+e) (4*gap) (zetas rootIndex)
  rw [innerLoc,innerLoc,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Optimized.Traversal

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Logical bank lanes represent the corresponding strided field coefficients. -/
def InnerBankField (u : Nat) (v : Vector (BitVec 128) 8) (w : Poly) : Prop :=
  ∀ i : Fin 8, ∀ e<4, ofInt (vword v[i.val] e).toInt=w[Traversal.innerLoc u i.val e]!

theorem innerCoreValues_field (v : Vector (BitVec 128) 8) (w : Poly) {gap g u : Nat}
    (hg : ValidGroup gap g) (hu : u<8) (rootIndex : Nat) {b : Int}
    (hb : 0≤b) (hs : b+16760834<2147483648) (hv : BankBound v b) (hf : InnerBankField u v w) :
    InnerBankField u (coreValues v gap g (fun _ => (zetaNat rootIndex : Int)))
      (Traversal.run (Traversal.innerRegGroupSchedule u (2*gap*g) gap rootIndex) w) := by
  intro i e he
  rw [coreValues_int v hg _ hb hs hv i he,Traversal.run_innerRegGroup,
    Traversal.innerRegBlock_get _ hg.bounds.1 hg.bounds.2 hu (Nat.le_refl _) _ i.isLt he,
    show 2*gap*g+gap+gap=2*gap*g+2*gap by omega_using []]
  by_cases hl : 2*gap*g≤i.val ∧ i.val<2*gap*g+gap
  · rw [ite_eq_left hl,ite_eq_left hl,ofInt_add,fastMul_field,Traversal.ofInt_zetaNat,hf i e he]
    have hidx : i.val+gap<8 := by have := hg.bounds.2; omega_using [hl, this]
    have hae : v[i.val+gap]! = v[i.val+gap] := getElem!_pos v _ hidx
    rw [hae,hf ⟨i.val+gap,hidx⟩ e he,Fin.mul_comm]
  · rw [ite_eq_right hl,ite_eq_right hl]
    by_cases hr : 2*gap*g+gap≤i.val ∧ i.val<2*gap*g+2*gap
    · rw [ite_eq_left hr,ite_eq_left hr,ofInt_sub,fastMul_field,Traversal.ofInt_zetaNat,hf i e he]
      have hidx : i.val-gap<8 := by omega_using []
      have hae : v[i.val-gap]! = v[i.val-gap] := getElem!_pos v _ hidx
      rw [hae,hf ⟨i.val-gap,hidx⟩ e he,Fin.mul_comm]
    · rw [ite_eq_right hr,ite_eq_right hr,hf i e he]


def innerGroupSchedule (u : Nat) (root : Nat → Nat → Nat) (p : Nat × Nat) : List Traversal.Op :=
  Traversal.innerRegGroupSchedule u (2*p.1*p.2) p.1 (root p.1 p.2)

theorem innerValues_field (v : Vector (BitVec 128) 8) (w : Poly) (ps : List (Nat × Nat))
    (hps : ∀ p∈ps,ValidGroup p.1 p.2) (root : Nat → Nat → Nat) {u : Nat} (hu : u<8) {b : Int}
    (hb : 0≤b) (hs : b+16760834*(ps.length : Int)<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (innerValues v (fun gap g _ => (zetaNat (root gap g) : Int)) ps)
      (b+16760834*(ps.length : Int)) ∧
    InnerBankField u (innerValues v (fun gap g _ => (zetaNat (root gap g) : Int)) ps)
      (Traversal.run (ps.flatMap (innerGroupSchedule u root)) w) := by
  induction ps generalizing v w b with
  | nil => simpa only [innerValues,List.length_nil,Int.natCast_zero,Int.mul_zero,Int.add_zero,
      List.flatMap_nil,Traversal.run,List.foldl_nil] using And.intro hv hf
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hs' : b+16760834<2147483648 := by
      simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs; omega_using [hs]
    have hb' := coreValues_bound v hp (fun _ => (zetaNat (root p.1 p.2) : Int)) hb hs' hv
    have hf' := innerCoreValues_field v w hp hu (root p.1 p.2) hb hs' hv hf
    have hh := ih (coreValues v p.1 p.2 (fun _ => (zetaNat (root p.1 p.2) : Int)))
      (Traversal.run (innerGroupSchedule u root p) w) (fun a ha => hps a (by simp [ha]))
      (b := b+16760834) (by omega_using [hb]) (by
        simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs
        omega_using [hs]) hb' hf'
    simpa only [innerValues,List.length_cons,Int.natCast_add,Int.natCast_one,List.flatMap_cons,
      Traversal.run_append,show b+16760834*((ps.length : Int)+1)=
        (b+16760834)+16760834*(ps.length : Int) by omega_using []] using hh

end VG.Proof.MlDsa.AArch64.Optimized
