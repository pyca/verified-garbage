import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentWords

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- Padding changes only the two padding words of each packed state. -/
theorem part_pad {m src : Mem} {p a b : Addr} (h : PartAt m p src a b 8) :
    PairAt ((m.write (wordAddr p 8) 16 (ofVDwords (tailWord src a) (tailWord src b))).write
      (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (seedState src a) (seedState src b) := by
  intro i hi
  rw [seedState_get src a hi,seedState_get src b hi]
  by_cases h16 : i = 16
  · subst i
    rw [read_write16]
    simp (disch := omega) only [ite_true,ite_eq_right]
  · have hs16 : Mem.Sep (wordAddr p i) 16 (wordAddr p 16) 16 :=
      Offset.sep p (d := 16*i) (e := 16*16) (n := 16) (k := 16) (by omega) (by omega) (by omega)
    rw [Mem.read_write_sep hs16 (by decide)]
    by_cases h8 : i = 8
    · subst i
      rw [read_write16]
      simp (disch := omega) only [ite_true,ite_eq_right]
    · have hs4 : Mem.Sep (wordAddr p i) 16 (wordAddr p 8) 16 :=
        Offset.sep p (d := 16*i) (e := 16*8) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs4 (by decide),h i hi]
      by_cases hl : i < 8
      · simp only [ite_eq_left hl]
        rfl
      · simp only [ite_eq_right hl,ite_eq_right h8,ite_eq_right h16]
        rfl

theorem seed_byte_frame {m m' : Mem} {p a : Addr} (hf : Frame [pairR p] m m')
    (hd : (seedR a).Disjoint (pairR p)) {j : Nat} (hj : j < 66) :
    m' (a+BitVec.ofNat 64 j) = m (a+BitVec.ofNat 64 j) :=
  hf _ (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd _ (Offset.contains_base a (by omega) (by omega)))

theorem tailWord_frame {m m' : Mem} {p a : Addr} (hf : Frame [pairR p] m m')
    (hd : (seedR a).Disjoint (pairR p)) : tailWord m' a = tailWord m a := by
  unfold tailWord lastWord
  rw [show a+64 = a+BitVec.ofNat 64 64 from rfl,show a+65 = a+BitVec.ofNat 64 65 from rfl,
    seed_byte_frame hf hd (by decide : 64 < 66),seed_byte_frame hf hd (by decide : 65 < 66)]
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
