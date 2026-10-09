import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemory

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
  exact finalPass_untouched m p q (by omega) (by change 4*u+32*i+e<256; omega) (by omega)

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
    · have hi : k/32<8 := by change k<256 at hk; omega
      have hidx : 4*u+32*(k/32)+k%4=k := by omega
      have hx := finalMemStep_at (finalPassMem m p q u) p q (by omega : u<8)
        ⟨k/32,hi⟩ (e := k%4) (by omega)
      rw [hidx,finalPass_bank_original m p q (by omega)] at hx
      simpa only [he,getElem!_pos (finalValues (readBank m (coeffAddr p (4*u)) 128) q) (k/32) hi] using hx
    · rw [finalMemStep_outside _ _ _ (by omega) hk he]
      exact ih (by omega) (by omega)

theorem finalPass_all_values (m : Mem) (p : Addr) (q : BitVec 128) {k : Nat} (hk : k<n) :
    coeffAt (finalPassMem m p q 8) p k=
      vword (finalValues (readBank m (coeffAddr p (4*(k%32/4))) 128) q)[k/32]! (k%4) :=
  finalPass_processed m p q (by decide) hk (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
