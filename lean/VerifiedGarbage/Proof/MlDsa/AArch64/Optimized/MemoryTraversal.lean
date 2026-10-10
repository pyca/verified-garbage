import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Core

/-! ## From `MemoryInner.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

private theorem positive_toInt {x : BitVec 32} (h : x.toNat<3*8380417) :
    x.toInt=(x.toNat : Int) := by
  have ht := BitVec.toInt_eq_toNat_cond x
  split at ht <;> omega

private theorem ofInt_nat (n : Nat) : ofInt (n : Int)=ofNat n := by
  apply Fin.ext
  simp only [ofInt,ofNat,Fin.val_ofNat,← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

def fiveMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues (readBank m (coeffAddr p (32*u)) 16) (innerRoot u) (tailRoot u))
    (coeffAddr p (32*u)) 16 m

theorem readInner_bank {m : Mem} {p : Addr} {w : Poly} {u : Nat} (hu : u<8)
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) :
    BankBound (readBank m (coeffAddr p (32*u)) 16) (15*8380417) ∧
      InnerBankField u (readBank m (coeffAddr p (32*u)) 16) w := by
  constructor
  · intro i e he
    rw [readBank_coeff m p (32*u) 4 i he]
    exact h.bound _ (by unfold n; omega)
  · intro i e he
    rw [readBank_coeff m p (32*u) 4 i he]
    exact h.value _ (by unfold n; omega)

theorem fiveMemStep_at (m : Mem) (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8)
    {e : Nat} (he : e<4) :
    coeffAt (fiveMemStep m p u) p (32*u+4*i.val+e)=
      vword (fiveValues (readBank m (coeffAddr p (32*u)) 16) (innerRoot u) (tailRoot u))[i.val] e := by
  unfold fiveMemStep
  exact writeBank_coeff_at _ m p (start := 32*u) (step := 4) (by decide) (by omega) i he

theorem fiveMemStep_outside (m : Mem) (p : Addr) {u k : Nat} (hu : u<8) (hk : k<256)
    (ho : k/32≠u) : coeffAt (fiveMemStep m p u) p k=coeffAt m p k := by
  unfold fiveMemStep
  exact writeBank_coeff_outside _ m p (start := 32*u) (step := 4) (by omega) hk (fun i => by omega)

/-- One contiguous slice preserves the signed representation globally and
normalizes its own 32 coefficients into the positive range. -/
theorem fiveMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} (hu : u<8)
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) :
    SignedPolyIs (fiveMemStep m p u) p (Traversal.run (Traversal.innerSlice u) w)
      (-15*8380417) (15*8380417) ∧
    (∀ k<256, k/32=u → (coeffAt (fiveMemStep m p u) p k).toNat<3*8380417) := by
  have hb := readInner_bank hu h
  have hv := fiveValues_field _ w hu hb.1 hb.2
  have hAt (k : Nat) (hk : k<256) (he : k/32=u) :
      (coeffAt (fiveMemStep m p u) p k).toNat<3*8380417 ∧
      ofNat (coeffAt (fiveMemStep m p u) p k).toNat=
        (Traversal.run (Traversal.innerSlice u) w)[k]! := by
    let i : Fin 8 := ⟨k%32/4,by omega⟩
    have heq : k=32*u+4*i.val+k%4 := by dsimp only [i]; omega
    rw [heq,fiveMemStep_at m p hu i (by omega)]
    exact ⟨hv.1 i _ (by omega),hv.2 i _ (by omega)⟩
  constructor
  · constructor
    · intro k hk
      by_cases he : k/32=u
      · have hv := (hAt k hk he).1
        rw [positive_toInt hv]
        omega
      · rw [fiveMemStep_outside m p hu hk he]
        exact h.bound k hk
    · intro k hk
      by_cases he : k/32=u
      · have hv := hAt k hk he
        rw [positive_toInt hv.1,ofInt_nat]
        exact hv.2
      · rw [fiveMemStep_outside m p hu hk he,
          Traversal.run_outside _ _ _ (Traversal.inner_supported ⟨u,hu⟩) w hk he]
        exact h.value k hk
  · intro k hk he
    exact (hAt k hk he).1

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `MemoryInnerPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerFieldPass (w : Poly) : Nat → Poly
  | 0 => w
  | u+1 => Traversal.run (Traversal.innerSlice u) (innerFieldPass w u)

theorem innerFieldPass_eq (w : Poly) (N : Nat) :
    innerFieldPass w N=Traversal.run ((List.range N).flatMap Traversal.innerSlice) w := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [innerFieldPass,ih,List.range_succ,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,Traversal.run_append]

theorem fivePassMem_step (m : Mem) (p : Addr) (u : Nat) :
    fivePassMem m p innerRoot tailRoot (u+1)=
      fiveMemStep (fivePassMem m p innerRoot tailRoot u) p u := by
  simp only [fivePassMem,fiveMemStep,coeffAddr,show 128*u=4*(32*u) by omega]

theorem fivePassMem_field_prefix {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) {N : Nat} (hn : N≤8) :
    SignedPolyIs (fivePassMem m p innerRoot tailRoot N) p (innerFieldPass w N)
      (-15*8380417) (15*8380417) ∧
    (∀ k<32*N, (coeffAt (fivePassMem m p innerRoot tailRoot N) p k).toNat<3*8380417) := by
  induction N with
  | zero => exact ⟨h,fun k hk => by omega⟩
  | succ N ih =>
    have hi := ih (by omega)
    have hs := fiveMemStep_field (u := N) (by omega) hi.1
    rw [fivePassMem_step]
    refine ⟨hs.1,?_⟩
    intro k hk
    by_cases he : k/32=N
    · exact hs.2 k (by omega) he
    · rw [fiveMemStep_outside _ _ (by omega) (by omega) he]
      exact hi.2 k (by omega)

/-- All eight slices finish in the positive internal representation, with the
same field polynomial as the exact inner NTT traversal. -/
theorem fivePassMem_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) :
    PosPolyIs (fivePassMem m p innerRoot tailRoot 8) p
      (Traversal.run Traversal.innerSchedule w) := by
  have hp := fivePassMem_field_prefix h (N := 8) (by decide)
  rw [innerFieldPass_eq] at hp
  constructor
  · intro k hk
    exact hp.2 k hk
  · apply ext_getElem!
    intro k hk
    rw [polyAt_get _ _ hk]
    have hb := hp.2 k hk
    have hv := hp.1.value k hk
    have ht := BitVec.toInt_eq_toNat_cond
      (coeffAt (fivePassMem m p innerRoot tailRoot 8) p k)
    have he : (coeffAt (fivePassMem m p innerRoot tailRoot 8) p k).toInt=
        ((coeffAt (fivePassMem m p innerRoot tailRoot 8) p k).toNat : Int) := by
      split at ht <;> omega
    rw [he] at hv
    have hc (j : Nat) : ofInt (j : Int)=ofNat j := by
      apply Fin.ext
      simp only [ofInt,ofNat,Fin.val_ofNat,← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]
    rw [hc] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `MemoryTraversal.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The exact stored result of the complete selected machine schedule is the
standard forward NTT, represented by positive words below three times q. -/
theorem nttMemory_field {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    PosPolyIs (nttMemory m p ordinaryRoot innerRoot tailRoot) p (ntt w) := by
  have ho := outerPass_all h
  have hi := fivePassMem_field (by
    simpa only [Int.neg_mul] using ho)
  have hz : ordinaryRoot=(fun k => (zetaNat k : Int)) := rfl
  simpa only [nttMemory,hz,Traversal.traversal_ntt] using hi

end VG.Proof.MlDsa.AArch64.Optimized

end
