import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackLoad
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

def storePacked (width : Nat) (m : Mem) (a : Addr) (x : BitVec 128) : Mem :=
  let lo := m.writeW a (x.extractLsb' 0 64)
  if width=4 then lo else lo.writeW (a+8) (x.extractLsb' 64 32)

/-- Both packing formats write only the exact eight- or twelve-byte block. -/
theorem storePacked_frame (m : Mem) (a : Addr) (x : BitVec 128) {width : Nat}
    (hw : width=4 ∨ width=6) : Frame [⟨a,2*width⟩] m (storePacked width m a x) := by
  have h8 : 8≤2*width := by omega
  have h0 : (Region.mk a (2*width)).Contains a 8 := by
    simpa only [BitVec.add_zero] using
      (Offset.contains_base a (d := 0) h8 (by decide))
  have h := (Frame.refl [⟨a,2*width⟩] m).writeW (List.mem_singleton_self _) (x.extractLsb' 0 64) h0
  rcases hw with rfl | rfl
  · exact h
  · exact h.writeW (List.mem_singleton_self _) (x.extractLsb' 64 32)
      (Offset.contains_base a (d := 8) (by decide) (by decide))

private theorem storeSlice_byte (m : Mem) (a : Addr) (x : BitVec 128)
    {start count i : Nat} (hi : i<count) (hc : count<2^64) :
    m.writeW a (x.extractLsb' start (8*count)) (a+BitVec.ofNat 64 i)=
      x.extractLsb' (start+8*i) 8 := by
  simp only [Mem.writeW,show 8*count/8=count by omega,Mem.write,
    Mem.sub_ofNat_toNat a (Nat.lt_trans hi hc),hi,ite_true]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
  have hb' : 8*i+b<8*count := by omega
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',
    show 8*i+b<8*(8*count/8) by omega,hb',decide_true,Bool.true_and]
  congr 1
  omega

/-- The stored bytes are exactly the low bytes of the vector, including
unaligned output addresses and modular address arithmetic. -/
theorem storePacked_byte (m : Mem) (a : Addr) (x : BitVec 128) {width i : Nat}
    (hw : width=4 ∨ width=6) (hi : i<2*width) :
    storePacked width m a x (a+BitVec.ofNat 64 i)=vbyte x i := by
  rcases hw with rfl | rfl
  · simpa only [storePacked,ite_true,vbyte,Nat.zero_add] using
      storeSlice_byte m a x (start := 0) (count := 8) hi (by decide)
  · by_cases h8 : i<8
    · unfold storePacked
      simp only [show ¬(6:Nat)=4 by decide,ite_false]
      have ho : ¬((a+BitVec.ofNat 64 i)-(a+8)).toNat<4 := by bv_omega
      change Mem.write _ (a+8) 4 _ _ = _
      rw [Mem.write_apply ho]
      simpa only [vbyte,Nat.zero_add] using
        storeSlice_byte m a x (start := 0) (count := 8) h8 (by decide)
    · have ha : a+BitVec.ofNat 64 i=(a+8)+BitVec.ofNat 64 (i-8) := by bv_omega
      unfold storePacked
      simp only [show ¬(6:Nat)=4 by decide,ite_false]
      rw [ha,storeSlice_byte _ _ x (start := 64) (count := 4) (by omega) (by decide)]
      change x.extractLsb' (64+8*(i-8)) 8=x.extractLsb' (8*i) 8
      congr 1
      omega

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
