import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductPassMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def productMemStep (initial current : Mem) (p a b : Addr) (u : Nat) : Mem :=
  writeBank (fiveValues u (productValues initial a b u)) (coeffAddr p (32*u)) 16 current

theorem productPassMem_step (m : Mem) (p a b : Addr) (u : Nat) :
    productPassMem m p a b (u+1)=productMemStep m (productPassMem m p a b u) p a b u := by
  simp only [productPassMem,productMemStep,coeffAddr,show 4*(32*u)=128*u by omega]

theorem productMemStep_at (m current : Mem) (p a b : Addr) {u : Nat}
    (hu : u<8) (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (productMemStep m current p a b u) p (32*u+4*i.val+e)=
      vword (fiveValues u (productValues m a b u))[i.val] e := by
  exact writeBank_coeff_at _ current p (start := 32*u) (step := 4) (by decide) (by omega) i he

theorem productMemStep_outside (m current : Mem) (p a b : Addr) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k/32≠u) :
    coeffAt (productMemStep m current p a b u) p k=coeffAt current p k := by
  apply writeBank_coeff_outside (start := 32*u) (step := 4) _ current p (by omega) hk
  intro i; omega

theorem productPass_processed (m : Mem) (p a b : Addr) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hp : k/32<u) :
    coeffAt (productPassMem m p a b u) p k=
      vword (fiveValues (k/32) (productValues m a b (k/32)))[k%32/4]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [productPassMem_step]
    by_cases he : k/32=u
    · have hi : k%32/4<8 := by omega
      have hidx : 32*u+4*(k%32/4)+k%4=k := by omega
      have hx := productMemStep_at m (productPassMem m p a b u) p a b (by omega : u<8)
        ⟨k%32/4,hi⟩ (e := k%4) (by omega)
      rw [hidx] at hx
      simpa only [he,getElem!_pos (fiveValues u (productValues m a b u)) (k%32/4) hi] using hx
    · rw [productMemStep_outside _ _ _ _ _ (by omega) hk he]
      exact ih (by omega) (by omega)

theorem productPass_all_values (m : Mem) (p a b : Addr) {k : Nat} (hk : k<n) :
    coeffAt (productPassMem m p a b 8) p k=
      vword (fiveValues (k/32) (productValues m a b (k/32)))[k%32/4]! (k%4) :=
  productPass_processed m p a b (by decide) hk (by change k<256 at hk; omega)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
