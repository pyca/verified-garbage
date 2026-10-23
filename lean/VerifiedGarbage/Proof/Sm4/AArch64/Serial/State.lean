module

public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem

/-! # The memory prepared for the single-block SM4 core -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial

/-- Prepared data remains entirely in the core's scratch region. -/
structure Ready (m : Mem) (B : Addr) (k : Spec.Sm4.Schedule) : Prop where
  sbox : ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0
  keys : ∀ i < 32, m.readW (B + BitVec.ofNat 64 (256+4*i)) 32 = k.getD i 0

theorem schedule_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 32) :
    m.readW (p + BitVec.ofNat 64 (4*i)) 32 = (Spec.Sm4.scheduleAt m p).getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [VG.Proof.Aes.getD_eq _ hi,getLsbD_readW32 m p i hj]
  have h := VG.Proof.Sm4.getLsbD_scheduleAt m p (i := i) (c := j/8) (j := j%8)
    hi (by omega) (by omega)
  rw [show 8*(j/8)+j%8 = j by omega] at h
  rw [h]
  rw [show (32*i+j)/8 = 4*i+j/8 by omega,show (32*i+j)%8 = j%8 by omega]

theorem copied_schedule {m m' : Mem} {p q : Addr}
    (h : ∀ j < 128, m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j)) :
    Spec.Sm4.scheduleAt m' q = Spec.Sm4.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt,Vector.getElem_ofFn,List.range,List.range.loop,List.foldl]
  rw [h (4*i+0) (by omega),h (4*i+1) (by omega),h (4*i+2) (by omega),h (4*i+3) (by omega)]

theorem Ready.frame {s s' : State} {B : Addr} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready s.mem B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (Modes.AArch64.coreRegion core B) r ∨
      Region.Sub r (Modes.AArch64.bufRegion core B)) : Ready s'.mem B k := by
  have tableDisjoint : ∀ r ∈ rs, Region.Disjoint ⟨B,256⟩ r := by
    intro r hr
    rcases hd r hr with h | h
    · exact h.sub_left (VG.Region.sub_prefix (by decide))
    · exact (VG.Offset.base_disjoint B (by decide : 256 ≤ 768)
        (by decide : 768+16 ≤ 2^64)).sub_right h
  have keysDisjoint : ∀ r ∈ rs, Region.Disjoint ⟨(B + BitVec.ofNat 64 256),128⟩ r := by
    intro r hr
    rcases hd r hr with h | h
    · exact h.sub_left (VG.Offset.sub_base B (by decide : 256+128 ≤ 3168))
    · exact (VG.Offset.disjoint B (Or.inl (by decide : 256+128 ≤ 768))
        (by decide : 256+128 ≤ 2^64) (by decide : 768+16 ≤ 2^64)).sub_right h
  refine ⟨fun j hj => ?_,fun i hi => ?_⟩
  · rw [hf.bytes tableDisjoint (by decide : 256 ≤ 2^64) hj]
    exact h.sbox j hj
  · rw [← VG.Offset.add_add B 256 (4*i)]
    rw [hf.readW (w := 32) (VG.Offset.contains_base ((B + BitVec.ofNat 64 256)) (d := 4*i) (n := 4) (k := 128)
      (by omega) (by omega)) keysDisjoint (by decide)]
    rw [VG.Offset.add_add]
    exact h.keys i hi

end VG.Proof.Sm4.AArch64.Serial
