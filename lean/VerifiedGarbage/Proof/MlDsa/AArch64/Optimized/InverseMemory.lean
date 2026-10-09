import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def firstMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues u (readBank m (coeffAddr p (32*u)) 16)) (coeffAddr p (32*u)) 16 m

def finalMemStep (m : Mem) (p : Addr) (q : BitVec 128) (u : Nat) : Mem :=
  writeBank (finalValues (readBank m (coeffAddr p (4*u)) 128) q) (coeffAddr p (4*u)) 128 m

theorem firstPassMem_step (m : Mem) (p : Addr) (u : Nat) :
    firstPassMem m p (u+1)=firstMemStep (firstPassMem m p u) p u := by
  simp only [firstPassMem,firstMemStep,coeffAddr,show 4*(32*u)=128*u by omega]

theorem finalPassMem_step (m : Mem) (p : Addr) (q : BitVec 128) (u : Nat) :
    finalPassMem m p q (u+1)=finalMemStep (finalPassMem m p q u) p q u := by
  simp only [finalPassMem,finalMemStep,coeffAddr,show 4*(4*u)=16*u by omega]

theorem firstMemStep_at (m : Mem) (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8)
    {e : Nat} (he : e<4) :
    coeffAt (firstMemStep m p u) p (32*u+4*i.val+e)=
      vword (fiveValues u (readBank m (coeffAddr p (32*u)) 16))[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 32*u) (step := 4) (by decide) (by omega) i he

theorem firstMemStep_outside (m : Mem) (p : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k<32*u ∨ 32*(u+1)≤k) :
    coeffAt (firstMemStep m p u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 32*u) (step := 4) _ m p (by omega) hk
  intro i; omega

theorem firstPass_untouched (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : 32*u≤k) :
    coeffAt (firstPassMem m p u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [firstPassMem_step,firstMemStep_outside _ _ (by omega) hk (Or.inr hbefore)]
    exact ih (by omega) (by omega)

theorem finalMemStep_at (m : Mem) (p : Addr) (q : BitVec 128) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (finalMemStep m p q u) p (4*u+32*i.val+e)=
      vword (finalValues (readBank m (coeffAddr p (4*u)) 128) q)[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 4*u) (step := 32) (by decide) (by omega) i he

theorem finalMemStep_outside (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k%32/4≠u) :
    coeffAt (finalMemStep m p q u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 4*u) (step := 32) _ m p (by omega) hk
  intro i; omega

theorem finalPass_untouched (m : Mem) (p : Addr) (q : BitVec 128) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : u≤k%32/4) :
    coeffAt (finalPassMem m p q u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [finalPassMem_step,finalMemStep_outside _ _ _ (by omega) hk (by omega)]
    exact ih (by omega) (by omega)

/-- A later local block still reads the original, unexpanded input range. -/
theorem firstPass_bank_bound {m : Mem} {p : Addr} {u : Nat} {bound : Int}
    (hu : u<8) (h : ∀ k<n, -bound≤(coeffAt m p k).toInt ∧ (coeffAt m p k).toInt≤bound)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -bound≤(vword (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)[i.val] e).toInt ∧
      (vword (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)[i.val] e).toInt≤bound := by
  rw [readBank_coeff _ p (32*u) 4 i he]
  have hk : 32*u+4*i.val+e<n := by change 32*u+4*i.val+e<256; omega
  rw [firstPass_untouched m p (by omega) hk (by omega)]
  exact h _ hk

/-- Earlier strided slices do not expand a later slice's input range. -/
theorem finalPass_bank_bound {m : Mem} {p : Addr} {u : Nat} {bound : Int} (q : BitVec 128)
    (hu : u<8) (h : ∀ k<n, -bound≤(coeffAt m p k).toInt ∧ (coeffAt m p k).toInt≤bound)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -bound≤(vword (readBank (finalPassMem m p q u) (coeffAddr p (4*u)) 128)[i.val] e).toInt ∧
      (vword (readBank (finalPassMem m p q u) (coeffAddr p (4*u)) 128)[i.val] e).toInt≤bound := by
  rw [readBank_coeff _ p (4*u) 32 i he]
  have hk : 4*u+32*i.val+e<n := by change 4*u+32*i.val+e<256; omega
  rw [finalPass_untouched m p q (by omega) hk (by omega)]
  exact h _ hk

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
