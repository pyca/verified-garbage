import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

theorem dotMemoryBank_word (m : Mem) (a b : Addr) (count : Nat) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (dotMemoryBank m a b count)[j.val] e=dotMemoryWord m a b count (16*j.val) e := by
  simp only [dotMemoryBank,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem dotMemoryWord_offset (m : Mem) (a b : Addr) (count u j e : Nat) (he : e<4) :
    dotMemoryWord m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count (16*j) e=
      centeredDot (fun k => coeffAt m (a+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e))
        (fun k => coeffAt m (b+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e)) count := by
  unfold dotMemoryWord
  congr 1 <;> funext k <;>
    rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he] <;>
    simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add] <;> congr 3 <;> omega

theorem dotPass_bank_original {m : Mem} {p a b : Addr} {count u : Nat} (hu : u<8)
    (ha : ∀k<count,(polyRegion (a+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p))
    (hb : ∀k<count,(polyRegion (b+BitVec.ofNat 64 (1024*k))).Disjoint (polyRegion p)) :
    dotMemoryBank (dotPassMem m p a b count u) (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) count=
    dotMemoryBank m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) count := by
  apply Vector.ext
  intro i hi
  apply vec_ext
  intro e he
  rw [dotMemoryBank_word _ _ _ _ ⟨i,hi⟩ he,dotMemoryBank_word _ _ _ _ ⟨i,hi⟩ he,
    dotMemoryWord_offset _ _ _ _ _ _ _ he,dotMemoryWord_offset _ _ _ _ _ _ _ he]
  apply centeredDot_congr
  · intro k hk
    exact coeffAt_frame (dotPass_frame (by omega)) (by
      intro r hr; have hr' := List.mem_singleton.mp hr; subst r; exact ha k hk)
      (by change 32*u+4*i+e<256; omega)
  · intro k hk
    exact coeffAt_frame (dotPass_frame (by omega)) (by
      intro r hr; have hr' := List.mem_singleton.mp hr; subst r; exact hb k hk)
      (by change 32*u+4*i+e<256; omega)

def dotMemStep (m : Mem) (p a b : Addr) (count u : Nat) : Mem :=
  writeBank (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
    (b+BitVec.ofNat 64 (128*u)) count)) (coeffAddr p (32*u)) 16 m

theorem dotPassMem_step (m : Mem) (p a b : Addr) (count u : Nat) :
    dotPassMem m p a b count (u+1)=dotMemStep (dotPassMem m p a b count u) p a b count u := by
  simp only [dotPassMem,dotMemStep,coeffAddr,show 4*(32*u)=128*u by omega]

theorem dotMemStep_at (m : Mem) (p a b : Addr) (count : Nat) {u : Nat} (hu : u<8)
    (i : Fin 8) {e : Nat} (he : e<4) :
    coeffAt (dotMemStep m p a b count u) p (32*u+4*i.val+e)=
      vword (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
        (b+BitVec.ofNat 64 (128*u)) count))[i.val] e := by
  exact writeBank_coeff_at _ m p (start:=32*u) (step:=4) (by decide) (by omega) i he

theorem dotMemStep_outside (m : Mem) (p a b : Addr) (count : Nat) {u k : Nat}
    (hu : u<8) (hk : k<n) (hout : k<32*u ∨ 32*(u+1)≤k) :
    coeffAt (dotMemStep m p a b count u) p k=coeffAt m p k := by
  apply writeBank_coeff_outside (start:=32*u) (step:=4) _ m p (by omega) hk
  intro i; omega

theorem dotPass_processed {m : Mem} {p a b : Addr} {count u k : Nat}
    (ha : ∀j<count,(polyRegion (a+BitVec.ofNat 64 (1024*j))).Disjoint (polyRegion p))
    (hb : ∀j<count,(polyRegion (b+BitVec.ofNat 64 (1024*j))).Disjoint (polyRegion p))
    (hu : u≤8) (hk : k<n) (hp : k/32<u) :
    coeffAt (dotPassMem m p a b count u) p k=
      vword (fiveValues (k/32) (dotMemoryBank m (a+BitVec.ofNat 64 (128*(k/32)))
        (b+BitVec.ofNat 64 (128*(k/32))) count))[(k%32)/4]! (k%4) := by
  induction u with
  | zero => omega
  | succ u ih =>
    rw [dotPassMem_step]
    by_cases he : k/32=u
    · have hi : (k%32)/4<8 := by omega
      have hidx : 32*u+4*((k%32)/4)+k%4=k := by omega
      have hx := dotMemStep_at (dotPassMem m p a b count u) p a b count (by omega : u<8)
        ⟨(k%32)/4,hi⟩ (e:=k%4) (by omega)
      rw [hidx,dotPass_bank_original (by omega) ha hb] at hx
      simpa only [he,
        getElem!_pos (fiveValues u (dotMemoryBank m (a+BitVec.ofNat 64 (128*u))
          (b+BitVec.ofNat 64 (128*u)) count)) ((k%32)/4) hi] using hx
    · rw [dotMemStep_outside _ _ _ _ _ (by omega) hk (by omega)]
      exact ih (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
