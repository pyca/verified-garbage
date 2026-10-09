import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def rawFinalMemStep (m : Mem) (p : Addr) (u : Nat) : Mem :=
  writeBank (rawFinalValues (readBank m (coeffAddr p (4*u)) 128)) (coeffAddr p (4*u)) 128 m

theorem rawFinalPassMem_step (m : Mem) (p : Addr) (u : Nat) :
    rawFinalPassMem m p (u+1)=rawFinalMemStep (rawFinalPassMem m p u) p u := by
  simp only [rawFinalPassMem,rawFinalMemStep,coeffAddr,show 4*(4*u)=16*u by omega]

theorem rawFinalMemStep_at (m : Mem) (p : Addr) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (rawFinalMemStep m p u) p (4*u+32*i.val+e)=
      vword (rawFinalValues (readBank m (coeffAddr p (4*u)) 128))[i.val] e := by
  exact writeBank_coeff_at _ m p (start := 4*u) (step := 32) (by decide) (by omega) i he

theorem rawFinalMemStep_outside (m : Mem) (p : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k%32/4≠u) :
    coeffAt (rawFinalMemStep m p u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start := 4*u) (step := 32) _ m p (by omega) hk
  intro i; omega

theorem rawFinalPass_untouched (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : u≤k%32/4) :
    coeffAt (rawFinalPassMem m p u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [rawFinalPassMem_step,rawFinalMemStep_outside _ _ (by omega) hk (by omega)]
    exact ih (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
