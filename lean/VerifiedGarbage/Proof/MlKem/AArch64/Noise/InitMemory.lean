module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Memory shape after paired seed initialization -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem read_write_word (m : Mem) (p : Addr) (v : BitVec 128) {i j : Nat}
    (hi : i < 25) (hj : j < 25) :
    (m.write (wordAddr p j) 16 v).read (wordAddr p i) 16 =
      if i = j then v else m.read (wordAddr p i) 16 := by
  by_cases he : i = j
  · subst i; rw [read_write16,ite_eq_left rfl]
  · rw [ite_eq_right he]
    have hs : Mem.Sep (wordAddr p i) 16 (wordAddr p j) 16 :=
      Offset.sep p (d := 16*i) (e := 16*j) (n := 16) (k := 16) (by omega) (by omega) (by omega)
    exact Mem.read_write_sep hs (by decide)

def SeedWords (m input : Mem) (p seed : Addr) : Prop :=
 ∀ i < 25, m.read (wordAddr p i) 16 = if i < 4 then
   ofVDwords (input.readW (seed+BitVec.ofNat 64 (8*i)) 64)
    (input.readW (seed+BitVec.ofNat 64 (8*i)) 64) else 0

theorem seedWords_of_zero {z m input : Mem} {p seed : Addr}
    (hz : ∀ i < 25, z.read (wordAddr p i) 16 = 0)
    (hf : Frame [⟨p,64⟩] z m)
    (hv : ∀ i < 4, m.read (wordAddr p i) 16 =
      ofVDwords (input.readW (seed+BitVec.ofNat 64 (8*i)) 64)
        (input.readW (seed+BitVec.ofNat 64 (8*i)) 64)) : SeedWords m input p seed := by
  intro i hi
  by_cases h4 : i < 4
  · rw [ite_eq_left h4]; exact hv i h4
  · rw [ite_eq_right h4]
    rw [hf.read (Region.contains_self (wordAddr p i) 16) (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base p (d := 16*i) (n := 16) (k := 64) (by omega) (by omega)) (by decide)]
    exact hz i hi

theorem tail_pair {m input : Mem} {p seed : Addr} {n : Nat}
    (h : SeedWords m input p seed) :
    PairAt ((m.write (wordAddr p 4) 16
      (ofVDwords (BitVec.ofNat 64 (n+0x1f00)) (BitVec.ofNat 64 (n+1+0x1f00)))).write
      (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (seedState input seed n) (seedState input seed (n+1)) := by
  intro i hi
  rw [read_write_word _ _ _ hi (by decide),read_write_word _ _ _ hi (by decide),h i hi,
    seedState_get input seed n hi,seedState_get input seed (n+1) hi]
  by_cases h4 : i < 4
  · simp only [ite_eq_left h4,ite_eq_right (by omega : ¬i=16),ite_eq_right (by omega : ¬i=4)]
  · by_cases he4 : i = 4
    · subst i; simp
    · by_cases he16 : i = 16
      · subst i; simp
      · simp only [ite_eq_right h4,ite_eq_right he4,ite_eq_right he16]
        rfl

end VG.Proof.MlKem.AArch64.Noise
