module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankField
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldStage
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseScale
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop

/-! ### `MlDsa.AArch64.Optimized.InverseMemory`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def firstMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues u (readBank m (coeffAddr p (32*u)) 16)) (coeffAddr p (32*u)) 16 m

def finalMemStep (m : Mem) (p : Addr) (q : BitVec 128) (u : Nat) : Mem :=
  writeBank (finalValues (readBank m (coeffAddr p (4*u)) 128) q) (coeffAddr p (4*u)) 128 m

theorem firstPassMem_step (m : Mem) (p : Addr) (u : Nat) :
    firstPassMem m p (u+1)=firstMemStep (firstPassMem m p u) p u := by
  simp only [firstPassMem,firstMemStep,coeffAddr,show 4*(32*u)=128*u by omega_using []]

theorem finalPassMem_step (m : Mem) (p : Addr) (q : BitVec 128) (u : Nat) :
    finalPassMem m p q (u+1)=finalMemStep (finalPassMem m p q u) p q u := by
  simp only [finalPassMem,finalMemStep,coeffAddr,show 4*(4*u)=16*u by omega_using []]

theorem firstMemStep_at (m : Mem) (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8)
    {e : Nat} (he : e<4) :
    coeffAt (firstMemStep m p u) p (32*u+4*i.val+e)=
      vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 32*u) (step := 4) (by decide) (by omega_using [hu]) i he

theorem firstMemStep_outside (m : Mem) (p : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k<32*u ∨ 32*(u+1)≤k) :
    coeffAt (firstMemStep m p u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 32*u) (step := 4) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hout]

theorem firstPass_untouched (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : 32*u≤k) :
    coeffAt (firstPassMem m p u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [firstPassMem_step,firstMemStep_outside _ _ (by omega_using [hu]) hk (Or.inr hbefore)]
    exact ih (by omega_using [hu]) (by omega_using [hbefore])

theorem finalMemStep_at (m : Mem) (p : Addr) (q : BitVec 128) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (finalMemStep m p q u) p (4*u+32*i.val+e)=
      vword (finalValues (readBank m (coeffAddr p (4*u)) 128) q)[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 4*u) (step := 32) (by decide) (by omega_using [hu]) i he

theorem finalMemStep_outside (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k%32/4≠u) :
    coeffAt (finalMemStep m p q u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 4*u) (step := 32) _ m p (by omega_using [hu]) hk
  intro i; omega_using [hu, hout]

theorem finalPass_untouched (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : u≤k%32/4) :
    coeffAt (finalPassMem m p q u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [finalPassMem_step,finalMemStep_outside _ _ _ (by omega_using [hu]) hk (by omega_using [hbefore])]
    exact ih (by omega_using [hu]) (by omega_using [hbefore])

/-- A later local block still reads the original, unexpanded input range. -/
theorem firstPass_bank_bound {m : Mem} {p : Addr} {u : Nat} {bound : Int}
    (hu : u<8) (h : ∀ k<n, -bound≤(coeffAt m p k).toInt ∧ (coeffAt m p k).toInt≤bound)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -bound≤(vword (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)[i.val] e).toInt ∧
      (vword (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)[i.val] e).toInt≤bound := by
  rw [readBank_coeff _ p (32*u) 4 i he]
  have hk : 32*u+4*i.val+e<n := by change 32*u+4*i.val+e<256; omega_using [hu, he]
  rw [firstPass_untouched m p (by omega_using [hu]) hk (by omega_using [])]
  exact h _ hk

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalBankFieldFold`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem scaleValues_word (v : Vector (BitVec 128) 8) (k : Fin 8) {e : Nat} (he : e<4) :
    vword (scaleValues v)[k.val] e=
      if k.val<4 then fastMulWord (vword v[k.val] e) 16382 else vword v[k.val] e := by
  simp only [scaleValues,Vector.getElem_ofFn]
  split
  · exact fastVector_word _ _ he
  · rfl

theorem final_sides (k : Fin 8) : (leftSide 6 k.val ↔ k.val<4) ∧ (rightSide 6 k.val ↔ ¬k.val<4) := by
  exact (show ∀ k : Fin 8, (leftSide 6 k.val ↔ k.val<4) ∧ (rightSide 6 k.val ↔ ¬k.val<4) by decide +kernel) k

theorem folded_root_field : ofInt (finalZ 6 0)=ofInt (negZetaNat 1 : Int)*ofInt 16382 := by decide +kernel

theorem folded_lane (v : Vector (BitVec 128) 8) (k : Fin 8) {e : Nat} (he : e<4) :
    let x := vword (scaleValues (stageValues 6 v (finalZ 6)))[k.val] e;
    -8380417<x.toInt ∧ x.toInt<2*8380417 ∧
      ofInt x.toInt=ofInt (vword (stageValues 6 v (fun _ => (negZetaNat 1 : Int)))[k.val] e).toInt*ofInt 16382 := by
  dsimp only
  rw [scaleValues_word _ _ he,stageValues_word _ _ _ _ he]
  simp only [(final_sides k).1,(final_sides k).2]
  by_cases hk : k.val<4
  · rw [ite_eq_left hk,ite_eq_left hk]
    have hb := fastMul_bounds (z := (16382 : Int))
      (BitVec.le_toInt (vword v[(leftSource 6 k).val] e+vword v[(rightSource 6 k).val] e))
      (BitVec.toInt_lt (x := vword v[(leftSource 6 k).val] e+vword v[(rightSource 6 k).val] e))
    rw [fastMulWord_int]
    refine ⟨hb.1,hb.2,?_⟩
    rw [fastMul_field,stageValues_word _ _ _ _ he,ite_eq_left ((final_sides k).1.mpr hk)]
  · rw [ite_eq_right hk,ite_eq_right hk,ite_eq_left hk]
    have hb := fastMul_bounds (z := finalZ 6 e)
      (BitVec.le_toInt (vword v[(leftSource 6 k).val] e-vword v[(rightSource 6 k).val] e))
      (BitVec.toInt_lt (x := vword v[(leftSource 6 k).val] e-vword v[(rightSource 6 k).val] e))
    rw [fastMulWord_int]
    refine ⟨hb.1,hb.2,?_⟩
    rw [fastMul_field,stageValues_word _ _ _ _ he,
      ite_eq_right (fun h => hk ((final_sides k).1.mp h)),ite_eq_left ((final_sides k).2.mpr hk),
      fastMulWord_int,fastMul_field]
    change _*ofInt (finalZ 6 0)=_
    rw [folded_root_field,Fin.mul_assoc]

theorem foldedStage_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : StageBound v 6 268173344) (hf : BankField u v w)
    (k : Fin 8) {e : Nat} (he : e<4) :
    let x := vword (scaleValues (stageValues 6 v (finalZ 6)))[k.val] e;
    -8380417<x.toInt ∧ x.toInt<2*8380417 ∧
      ofInt x.toInt=(InverseTraversal.run (stridedStageOps u 1 6) w)[InverseTraversal.stridedLoc u k.val e]!*ofInt 16382 := by
  have h := folded_lane v k he
  have hs := stridedStageValues_field (6 : Fin 7) v w hu 1 (by decide) (by decide) hv hf k e he
  exact ⟨h.1,h.2.1,h.2.2.trans (congrArg (·*ofInt 16382) hs)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseFinalBankFieldRun`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def finalIndex (i : Nat) : Nat := if i<4 then 7-i else if i<6 then 3-(i-4) else 1

def stridedRunOps (u i : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => stridedStageOps u (finalIndex i) i ++ stridedRunOps u (i+1) n

theorem finalZ_index {i : Nat} (hi : i<6) : finalZ i=(fun _ => (negZetaNat (finalIndex i) : Int)) := by
  funext e
  simp only [finalZ,finalValue,finalIndex]
  split
  · rfl
  · rfl

theorem runValues_final_six (i n : Nat) (hin : i+n≤6) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (hv : StageBound v i 268173344) (hf : BankField u v w) :
    StageBound (runValues finalZ i n v) (i+n) 268173344 ∧
      BankField u (runValues finalZ i n v) (InverseTraversal.run (stridedRunOps u i n) w) := by
  induction n generalizing i v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hi : i<6 := by omega_using [hin]
    have hp := stageValues_bound ⟨i,by omega_using [hin]⟩ v (finalZ i) (by decide) (by decide) hv
    have hfield := stridedStageValues_field ⟨i,by omega_using [hin]⟩ v w hu (finalIndex i) (by decide) (by decide) hv hf
    rw [← finalZ_index hi] at hfield
    have h := ih (i := i+1) (by omega_using [hin]) _ _ hp hfield
    simpa only [runValues,stridedRunOps,InverseTraversal.run_append,Nat.add_assoc,Nat.add_comm 1 n] using h

theorem stridedOps_eq {u : Nat} (hu : u<8) :
    stridedRunOps u 0 6 ++ stridedStageOps u 1 6=InverseTraversal.stridedSlice u := by
  exact (show ∀ u : Fin 8,
    stridedRunOps u.val 0 6 ++ stridedStageOps u.val 1 6=InverseTraversal.stridedSlice u.val
    by decide +kernel) ⟨u,hu⟩

theorem runValues_split_last (v : Vector (BitVec 128) 8) :
    runValues finalZ 0 7 v=stageValues 6 (runValues finalZ 0 6 v) (finalZ 6) := rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

/-! ### `MlDsa.AArch64.Optimized.InverseMemoryFinalField`, which only this module used -/

section

/-! ## From `InverseMemoryFinalValues.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem finalPass_bank_original (m : Mem) (p : Addr) (q : BitVec 128) {u : Nat} (hu : u<8) :
    readBank (finalPassMem m p q u) (coeffAddr p (4*u)) 128=
      readBank m (coeffAddr p (4*u)) 128 := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he,readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he]
  exact finalPass_untouched m p q (by omega_using [hu]) (by change 4*u+32*i+e<256; omega_using [hu, hi, he]) (by omega_using [hu, he])

/-- A completed coefficient is the canonical result of its own strided bank,
evaluated on the original pass input. -/
theorem finalPass_processed (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hp : k%32/4<u) :
    coeffAt (finalPassMem m p q u) p k=
      vword (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) q)[k/32]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [finalPassMem_step]
    by_cases he : k%32/4=u
    · have hi : k/32<8 := by change k<256 at hk; omega_using [hk]
      have hidx : 4*u+32*(k/32)+k%4=k := by omega_using [he]
      have hx := finalMemStep_at (finalPassMem m p q u) p q (by omega_using [hu] : u<8)
        ⟨k/32,hi⟩ (e := k%4) (by omega_using [])
      rw [hidx,finalPass_bank_original m p q (by omega_using [hu])] at hx
      simpa only [he,getElem!_pos (finalValues (readBank m (coeffAddr p (4*u)) 128) q) (k/32) hi] using hx
    · rw [finalMemStep_outside _ _ _ (by omega_using [hu]) hk he]
      exact ih (by omega_using [hu]) (by omega_using [hp, he])

theorem finalPass_all_values (m : Mem) (p : Addr) (q : BitVec 128) {k : Nat} (hk : k<n) :
    coeffAt (finalPassMem m p q 8) p k=
      vword (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) q)[k/32]! (k%4) :=
  finalPass_processed m p q (by decide) hk (by omega_using [])

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryFinalField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Canonical bank outputs with folded scaling establish the complete final
memory pass's field result, independently of the order of disjoint slices. -/
theorem finalPass_field_of_banks {m : Mem} {p : Addr} {qv : BitVec 128} {w : Poly}
    (hb : ∀ u<8, ∀ i : Fin 8, ∀ e<4,
      (vword (finalValues (readBank m (coeffAddr p (4*u)) 128) qv)[i.val] e).toNat<q)
    (hv : ∀ u<8, ∀ i : Fin 8, ∀ e<4,
      ofInt (vword (finalValues (readBank m (coeffAddr p (4*u)) 128) qv)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382) :
    PolyIs (finalPassMem m p qv 8) p ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have hout (k : Nat) (hk : k<n) :
      (coeffAt (finalPassMem m p qv 8) p k).toNat<q ∧
      ofInt (coeffAt (finalPassMem m p qv 8) p k).toInt=
        (InverseTraversal.run InverseTraversal.stridedSchedule w)[k]! * 16382 := by
    have hi : k/32<8 := by change k<256 at hk; omega_using [hk]
    have hu : k%32/4<8 := by omega_using []
    have he : k%4<4 := by omega_using []
    rw [finalPass_all_values m p qv hk,getElem!_pos (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) qv) (k/32) hi]
    refine ⟨hb _ hu ⟨k/32,hi⟩ _ he,?_⟩
    have hh := hv _ hu ⟨k/32,hi⟩ _ he
    have hidx : 4*(k%32/4)+32*(k/32)+k%4=k := by omega_using []
    rw [hidx] at hh
    rw [InverseTraversal.strided_coordinate w hk]
    exact hh
  refine ⟨fun k hk => (hout k hk).1,ext_getElem! fun k hk => ?_⟩
  rw [polyAt_get _ _ hk,map_mul_get _ _ hk]
  have hh := hout k hk
  have hint : (coeffAt (finalPassMem m p qv 8) p k).toInt=
      ((coeffAt (finalPassMem m p qv 8) p k).toNat : Int) := by
    apply BitVec.toInt_eq_toNat_of_lt
    have hq : q=8380417 := rfl
    omega
  rw [hint,ofInt_nat_eq] at hh
  exact hh.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

end


/-! ## From `InverseFinalBankFieldCanonical.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa

/-- The final store's existing correction preserves each field value and
produces its canonical representative, given the strict Barrett range. -/
theorem canonicalValues_lane (v : Vector (BitVec 128) 8) (qv : BitVec 128)
    (i : Fin 8) {e : Nat} (he : e<4) (hq : vword qv e=8380417#32)
    (hl : -8380417<(vword v[i.val] e).toInt)
    (hh : (vword v[i.val] e).toInt<2*8380417) :
    (vword (canonicalValues v qv)[i.val] e).toNat<8380417 ∧
      ofInt (vword (canonicalValues v qv)[i.val] e).toInt=ofInt (vword v[i.val] e).toInt := by
  simp only [canonicalValues,Vector.getElem_ofFn]
  rw [canonicalVector_word _ _ he hq]
  exact ⟨canonicalWord_bounds _ hl hh,canonicalWord_field _ hl hh⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Lift a resident local bank's arithmetic result into the global polynomial
invariant, preserving all coefficients outside that bank. -/
theorem firstMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} {bound : Int}
    (hu : u<8) (h : SignedPolyIs m p w (-bound) bound)
    (hb : ∀ i : Fin 8, ∀ e<4,
      -bound≤(vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt ∧
      (vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt≤bound)
    (hv : ∀ i : Fin 8, ∀ e<4,
      ofInt (vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.localSlice u) w)[32*u+4*i.val+e]!) :
    SignedPolyIs (firstMemStep m p u) p
      (InverseTraversal.run (InverseTraversal.localSlice u) w) (-bound) bound := by
  constructor
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega_using []
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega_using [hs]
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega_using [])
      rw [he] at hx
      rw [hx]
      exact hb ⟨(k%32)/4,hi⟩ _ (by omega_using [])
    · rw [firstMemStep_outside m p hu hk (by omega_using [hs])]
      exact h.bound k hk
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega_using []
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega_using [hs]
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega_using [])
      rw [he] at hx
      rw [hx]
      simpa only [he] using hv ⟨(k%32)/4,hi⟩ (k%4) (by omega_using [])
    · rw [firstMemStep_outside m p hu hk (by omega_using [hs]),h.value k hk,
        InverseTraversal.run_outside _ _ _ (InverseTraversal.local_supported ⟨u,hu⟩) w hk hs]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryFirstPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem firstPass_field_prefix {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) {u : Nat} (hu : u≤8) :
    SignedPolyIs (firstPassMem m p u) p
      (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w)
      (-268173344) 268173344 := by
  induction u with
  | zero => exact h.mono (by decide) (by decide)
  | succ u ih =>
    have hp := ih (by omega_using [hu])
    have hf : InnerBankField u
        (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)
        (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w) := by
      intro i e he
      rw [readBank_coeff _ p (32*u) 4 i he]
      exact hp.value _ (by change 32*u+4*i.val+e<256; omega_using [hu, he])
    have hb : BankBound (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16) 8380417 :=
      fun i e he => firstPass_bank_bound (by omega_using [hu]) h.bound i he
    have hs := fiveValues_field _ _ (by omega_using [hu] : u<8) hb hf
    have hm := firstMemStep_field (by omega_using [hu] : u<8) hp hs.1 hs.2
    simpa only [firstPassMem_step,List.range_succ,List.flatMap_append,
      List.flatMap_singleton,InverseTraversal.run_append] using hm

/-- All eight local blocks implement the first five inverse layers, retaining
bounded signed representatives for the subsequent strided pass. -/
theorem firstPass_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) :
    SignedPolyIs (firstPassMem m p 8) p
      (InverseTraversal.run InverseTraversal.localSchedule w) (-268173344) 268173344 :=
  firstPass_field_prefix h (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseFinalBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The selected strided final pass returns canonical coefficients and applies
exactly the last three inverse layers with the folded Montgomery scale. -/
theorem finalValues_field (v : Vector (BitVec 128) 8) (qv : BitVec 128) (w : Poly)
    {u : Nat} (hu : u<8) (hv : BankBound v 268173344) (hf : BankField u v w)
    (hq : ∀ e<4, vword qv e=8380417#32) (i : Fin 8) {e : Nat} (he : e<4) :
    (vword (finalValues v qv)[i.val] e).toNat<8380417 ∧
      ofInt (vword (finalValues v qv)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382 := by
  have hp := runValues_final_six 0 6 (by decide) v w hu
    ((stageBound_zero v 268173344).mpr hv) hf
  have hl := foldedStage_field _ _ hu hp.1 hp.2 i he
  have hc := canonicalValues_lane _ qv i he (hq e he) hl.1 hl.2.1
  rw [finalValues,runValues_split_last]
  refine ⟨hc.1,hc.2.trans ?_⟩
  simpa only [← InverseTraversal.run_append,stridedOps_eq hu,
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega_using [],
    show ofInt (16382 : Int)=(16382 : Zq) by decide +kernel] using hl.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseMemoryCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem finalPass_field {m : Mem} {p : Addr} {w : Poly} {qv : BitVec 128}
    (h : SignedPolyIs m p w (-268173344) 268173344)
    (hq : ∀ e<4, vword qv e=8380417#32) :
    PolyIs (finalPassMem m p qv 8) p ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have bank (u : Nat) (hu : u<8) := fun (i : Fin 8) (e : Nat) (he : e<4) =>
    finalValues_field (readBank m (coeffAddr p (4*u)) 128) qv w hu
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        exact h.bound _ (by change 4*u+32*j.val+e<256; omega_using [hu, he]))
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          h.value (4*u+32*j.val+e) (by change 4*u+32*j.val+e<256; omega_using [hu, he])) hq i he
  exact finalPass_field_of_banks (fun u hu i e he => (bank u hu i e he).1)
    (fun u hu i e he => (bank u hu i e he).2)

/-- Exact selected two-pass inverse, valid also for centered raw products. -/
theorem inverseMem_field_signed {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) :
    PolyIs (inverseMem m p) p (montgomeryNttInv w) := by
  have hp := finalPass_field (firstPass_field h) (qv := HighPack.repeatedWord 8380417)
    (fun e he => HighPack.repeatedWord_lane _ he)
  simpa only [inverseMem,InverseTraversal.traversal_montgomery] using hp

theorem inverseMem_field {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    PolyIs (inverseMem m p) p (montgomeryNttInv w) := by
  apply inverseMem_field_signed
  constructor
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_int _ (h.1 k hk)]
    have hb := h.1 k hk
    change (coeffAt m p k).toNat<8380417 at hb
    omega_using [hb]
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_field _ (h.1 k hk),← polyAt_get _ _ hk,h.2]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
