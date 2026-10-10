import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank

/-! ## From `InverseRawMemory.lean` -/

section

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

end

/-! ## From `InverseRawMemoryValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem rawFinalPass_bank_original (m : Mem) (p : Addr) {u : Nat} (hu : u<8) :
    readBank (rawFinalPassMem m p u) (coeffAddr p (4*u)) 128=
      readBank m (coeffAddr p (4*u)) 128 := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he,readBank_coeff _ p (4*u) 32 ⟨i,hi⟩ he]
  exact rawFinalPass_untouched m p (by omega) (by change 4*u+32*i+e<256; omega) (by omega)

/-- A completed coefficient is the raw result of its own strided bank,
evaluated on the original pass input. -/
theorem rawFinalPass_processed (m : Mem) (p : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hp : k%32/4<u) :
    coeffAt (rawFinalPassMem m p u) p k=
      vword (rawFinalValues (readBank m (coeffAddr p (4*(k%32/4))) 128))[k/32]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [rawFinalPassMem_step]
    by_cases he : k%32/4=u
    · have hi : k/32<8 := by change k<256 at hk; omega
      have hidx : 4*u+32*(k/32)+k%4=k := by omega
      have hx := rawFinalMemStep_at (rawFinalPassMem m p u) p (by omega : u<8)
        ⟨k/32,hi⟩ (e := k%4) (by omega)
      rw [hidx,rawFinalPass_bank_original m p (by omega)] at hx
      simpa only [he,getElem!_pos (rawFinalValues (readBank m (coeffAddr p (4*u)) 128)) (k/32) hi] using hx
    · rw [rawFinalMemStep_outside _ _ (by omega) hk he]
      exact ih (by omega) (by omega)

theorem rawFinalPass_all_values (m : Mem) (p : Addr) {k : Nat} (hk : k<n) :
    coeffAt (rawFinalPassMem m p 8) p k=
      vword (rawFinalValues (readBank m (coeffAddr p (4*(k%32/4))) 128))[k/32]! (k%4) :=
  rawFinalPass_processed m p (by decide) hk (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
