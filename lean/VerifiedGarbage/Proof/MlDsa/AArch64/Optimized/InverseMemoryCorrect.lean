import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryFinalField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass

/-! ## From `InverseFinalBankFieldCanonical.lean` -/

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
    · have hi : (k%32)/4<8 := by omega
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega)
      rw [he] at hx
      rw [hx]
      exact hb ⟨(k%32)/4,hi⟩ _ (by omega)
    · rw [firstMemStep_outside m p hu hk (by omega)]
      exact h.bound k hk
  · intro k hk
    by_cases hs : k/32=u
    · have hi : (k%32)/4<8 := by omega
      have he : 32*u+4*((k%32)/4)+k%4=k := by omega
      have hx := firstMemStep_at m p hu ⟨(k%32)/4,hi⟩ (e := k%4) (by omega)
      rw [he] at hx
      rw [hx]
      simpa only [he] using hv ⟨(k%32)/4,hi⟩ (k%4) (by omega)
    · rw [firstMemStep_outside m p hu hk (by omega),h.value k hk,
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
    have hp := ih (by omega)
    have hf : InnerBankField u
        (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)
        (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w) := by
      intro i e he
      rw [readBank_coeff _ p (32*u) 4 i he]
      exact hp.value _ (by change 32*u+4*i.val+e<256; omega)
    have hb : BankBound (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16) 8380417 :=
      fun i e he => firstPass_bank_bound (by omega) h.bound i he
    have hs := fiveValues_field _ _ (by omega : u<8) hb hf
    have hm := firstMemStep_field (by omega : u<8) hp hs.1 hs.2
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
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega,
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
        exact h.bound _ (by change 4*u+32*j.val+e<256; omega))
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          h.value (4*u+32*j.val+e) (by change 4*u+32*j.val+e<256; omega)) hq i he
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
    omega
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_field _ (h.1 k hk),← polyAt_get _ _ hk,h.2]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
