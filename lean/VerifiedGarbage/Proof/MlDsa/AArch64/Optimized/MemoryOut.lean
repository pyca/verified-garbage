import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OutCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A disjoint source polynomial is unchanged throughout the outer pass. -/
theorem outerOutPass_source {m : Mem} {p src : Addr} {z : Nat → Int} {u : Nat}
    (hu : u≤8) (hd : (polyRegion src).Disjoint (polyRegion p))
    {k : Nat} (hk : k<n) :
    coeffAt (outerOutPassMem m p src z u) src k=coeffAt m src k := by
  have hf : Frame [outputRegion p] m (outerOutPassMem m p src z u) :=
    outerOutPass_frame (fun v hv i => outer_contains p (by omega) i)
  exact coeffAt_frame hf (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hd) hk

/-- The next source bank equals the corresponding in-place input bank. -/
theorem outerOutPass_bank {m : Mem} {p src : Addr} {z : Nat → Int} {u : Nat}
    (hu : u<8) (hd : (polyRegion src).Disjoint (polyRegion p)) :
    readBank (outerOutPassMem m p src z u) (coeffAddr src (4*u)) 128 =
      readBank (outerPassMem m src z u) (coeffAddr src (4*u)) 128 := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [readBank_coeff _ src (4*u) 32 ⟨i,hi⟩ he,
    readBank_coeff _ src (4*u) 32 ⟨i,hi⟩ he]
  have hk : 4*u+32*i+e<n := by change 4*u+32*i+e<256; omega
  rw [outerOutPass_source (by omega) hd hk,
    outerPass_untouched m src z (by omega) hk (by omega)]

/-- Every completed slice agrees word-for-word with the in-place reference. -/
theorem outerOutPass_processed {m : Mem} {p src : Addr} {z : Nat → Int}
    (hd : (polyRegion src).Disjoint (polyRegion p)) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hprocessed : k%32/4<u) :
    coeffAt (outerOutPassMem m p src z u) p k=
      coeffAt (outerPassMem m src z u) src k := by
  induction u with
  | zero => omega
  | succ u ih =>
    have hp (a : Addr) : a+BitVec.ofNat 64 (16*u)=coeffAddr a (4*u) := by
      simp only [coeffAddr,show 4*(4*u)=16*u by omega]
    simp only [outerOutPassMem,outerPassMem,outerOutMemStep,outerMemStep,hp]
    rw [outerOutPass_bank (by omega) hd]
    by_cases he : k%32/4=u
    · have ki : k/32<8 := by change k<256 at hk; omega
      have ke : k=4*u+32*(k/32)+k%4 := by omega
      rw [ke,writeBank_coeff_at (start := 4*u) (step := 32) (e := k%4) _ _ p (by decide) (by omega) ⟨k/32,ki⟩ (by omega),
        writeBank_coeff_at (start := 4*u) (step := 32) (e := k%4) _ _ src (by decide) (by omega) ⟨k/32,ki⟩ (by omega)]
    · have hout : ∀ i : Fin 8, ¬(4*u+32*i.val≤k ∧ k<4*u+32*i.val+4) := by
        intro i; omega
      rw [writeBank_coeff_outside (step := 32) _ _ p (by omega) hk hout,
        writeBank_coeff_outside (step := 32) _ _ src (by omega) hk hout]
      exact ih (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized
