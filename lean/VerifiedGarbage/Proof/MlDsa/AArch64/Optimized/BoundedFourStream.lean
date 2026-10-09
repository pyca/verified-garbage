import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem Rate136.keep {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate136 m p A) (hf : Frame rs m m') (hd : ∀r∈rs,(rateR p).Disjoint r) :
    Rate136 m' p A := by
  intro i hi
  rw [hf.readW (rate_contains p hi) hd (by decide)]
  exact h i hi

theorem pairAt_keep {m m' : Mem} {p : Addr} {A B : Spec.Sha3.State} {rs : List Region}
    (h : PairAt m p A B) (hf : Frame rs m m') (hd : ∀r∈rs,(pairR p).Disjoint r) :
    PairAt m' p A B := by
  intro i hi
  rw [hf.read (pair_contains p hi) hd (by decide)]
  exact h i hi

def Stream136 (m : Mem) (p : Addr) (j : Nat) (A : Spec.Sha3.State) : Prop :=
 ∀i<j,Rate136 m (p+BitVec.ofNat 64 (136*i)) (Resident.permuted A (i+1))

theorem stream136_zero (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Stream136 m p 0 A := by
  intro i hi; omega

theorem Stream136.keep {m m' : Mem} {p : Addr} {j : Nat} {A : Spec.Sha3.State} {rs : List Region}
    (h : Stream136 m p j A) (hf : Frame rs m m')
    (hd : ∀i<j,∀r∈rs,(rateR (p+BitVec.ofNat 64 (136*i))).Disjoint r) :
    Stream136 m' p j A := fun i hi=>(h i hi).keep hf (hd i hi)

theorem Stream136.succ {m : Mem} {p : Addr} {j : Nat} {A : Spec.Sha3.State}
    (h : Stream136 m p j A)
    (hl : Rate136 m (p+BitVec.ofNat 64 (136*j)) (Spec.Sha3.keccakF (Resident.permuted A j))) :
    Stream136 m p (j+1) A := by
  intro i hi
  by_cases he : i=j
  · subst i; exact hl
  · exact h i (by omega)

theorem stream136_byte {m : Mem} {p : Addr} {j : Nat} {A : Spec.Sha3.State}
    (h : Stream136 m p j A) {i : Nat} (hi : i<136*j) :
    m (p+BitVec.ofNat 64 i)=Proof.Sha3.byteOf (Resident.permuted A (i/136+1)) (i%136) := by
  have he:=(h (i/136) (by omega)).byte (j := i%136) (by omega)
  rw [BitVec.add_assoc,←BitVec.ofNat_add,show 136*(i/136)+i%136=i by omega] at he
  exact he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
