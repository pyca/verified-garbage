module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Tail
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitMemory

/-! # Exact padded matrix-seed state -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def seedState (m : Mem) (seed : Addr) (a k : Nat) : Spec.Sha3.State := Vector.ofFn fun i : Fin 25 =>
 if i.val<4 then m.readW (seed+BitVec.ofNat 64 (8*i.val)) 64
 else if i.val=4 then suffix (BitVec.ofNat 16 (a%k+256*(a/k)))
 else if i.val=20 then 0x8000000000000000 else 0

theorem seedState_get (m : Mem) (p : Addr) (a k : Nat) {i : Nat} (hi : i<25) :
 (seedState m p a k)[i]! = if i<4 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
 else if i=4 then suffix (BitVec.ofNat 16 (a%k+256*(a/k)))
 else if i=20 then 0x8000000000000000 else 0 := by
 rw [getElem!_pos _ i hi]
 unfold seedState
 rw [Vector.getElem_ofFn]

theorem tail_pair {m input : Mem} {p seed : Addr} {a b k : Nat}
    (h : Noise.SeedWords m input p seed) :
    PairAt ((m.write (wordAddr p 4) 16
      (ofVDwords (suffix (BitVec.ofNat 16 (a%k+256*(a/k))))
        (suffix (BitVec.ofNat 16 (b%k+256*(b/k)))))).write
      (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (seedState input seed a k) (seedState input seed b k) := by
  intro i hi
  rw [Noise.read_write_word _ _ _ hi (by decide),Noise.read_write_word _ _ _ hi (by decide),h i hi,
    seedState_get input seed a k hi,seedState_get input seed b k hi]
  by_cases h4 : i<4
  · simp only [ite_eq_left h4,ite_eq_right (by omega : ¬i=20),ite_eq_right (by omega : ¬i=4)]
  · by_cases he4 : i=4
    · subst i; simp
    · by_cases he20 : i=20
      · subst i; simp
      · simp only [ite_eq_right h4,ite_eq_right he4,ite_eq_right he20]; rfl

end VG.Proof.MlKem.AArch64.Paired
