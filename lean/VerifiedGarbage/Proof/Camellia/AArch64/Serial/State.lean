module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The single-block core's prepared table and raw expanded schedule -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial

structure Ready (m : Mem) (B : Addr) (k : Nat × List (BitVec 64)) : Prop where
  rounds : k.1 = 18 ∨ k.1 = 24
  sbox : ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0
  keys : ∀ i < Spec.Camellia.scheduleLength k.1,
    Spec.Camellia.wordAt m (B + BitVec.ofNat 64 (256+8*i)) = k.2.getD i 0

theorem readBE (m : Mem) (p : Addr) : rev64 (m.readW p 64) = Spec.Camellia.wordAt m p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show rev64 = byteRev64 from rfl,byteRev64_getLsbD _ hi,
    VG.Proof.Camellia.getLsbD_wordAt m p hi]
  simp only [Mem.readW,BitVec.getLsbD_setWidth,
    show 8*(7-i/8)+i%8 < 64 by omega,decide_true,Bool.true_and]
  rw [getLsbD_read m 8 p _ (by omega),
    show (8*(7-i/8)+i%8)/8 = 7-i/8 by omega,
    show (8*(7-i/8)+i%8)%8 = i%8 by omega]

theorem Ready.frame {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready s.mem B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (Modes.AArch64.coreRegion core B) r ∨
      Region.Sub r (Modes.AArch64.bufRegion core B)) : Ready s'.mem B k := by
  have tableDisjoint : ∀ r ∈ rs, Region.Disjoint ⟨B,256⟩ r := by
    intro r hr
    rcases hd r hr with h | h
    · exact h.sub_left (VG.Region.sub_prefix (by decide))
    · exact (VG.Offset.base_disjoint B (by decide : 256 ≤ 768)
        (by decide : 768+16 ≤ 2^64)).sub_right h
  have keysDisjoint : ∀ r ∈ rs, Region.Disjoint ⟨B+BitVec.ofNat 64 256,272⟩ r := by
    intro r hr
    rcases hd r hr with h | h
    · exact h.sub_left (VG.Offset.sub_base B (by decide : 256+272 ≤ 3152))
    · exact (VG.Offset.disjoint B (Or.inl (by decide : 256+272 ≤ 768))
        (by decide : 256+272 ≤ 2^64) (by decide : 768+16 ≤ 2^64)).sub_right h
  refine ⟨h.rounds,fun j hj => ?_,fun i hi => ?_⟩
  · rw [hf.bytes tableDisjoint (by decide : 256 ≤ 2^64) hj]
    exact h.sbox j hj
  · have hn : i < 34 := by
      have := h.rounds
      simp only [Spec.Camellia.scheduleLength] at hi
      omega
    rw [← readBE,← VG.Offset.add_add B 256 (8*i)]
    rw [hf.readW (w := 64) (VG.Offset.contains_base (B+BitVec.ofNat 64 256)
      (d := 8*i) (n := 8) (k := 272) (by omega) (by omega)) keysDisjoint (by decide)]
    rw [VG.Offset.add_add,readBE]
    exact h.keys i hi

end VG.Proof.Camellia.AArch64.Serial
