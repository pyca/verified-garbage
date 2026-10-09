import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitEntry
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

theorem initEntryMemory_eq (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    initEntryMemory m p mask=
      (m.write (p+BitVec.ofNat 64 (6000+64*mask)) 16 (shuffleWord mask)).writeW
        (p+BitVec.ofNat 64 (6000+64*mask+32)) (BitVec.ofNat 64 (acceptedIndices mask).length) := by
  rw [←init_words hm,write16_dwords]
  simp only [initEntryMemory,BitVec.add_assoc,←BitVec.ofNat_add]

theorem initEntryMemory_frame (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    Frame [⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩] m (initEntryMemory m p mask) := by
  rw [initEntryMemory_eq m p hm]
  have h16 : (⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ : Region).Contains
      (p+BitVec.ofNat 64 (6000+64*mask)) 16 := Offset.contains p (by omega) (by omega) (by omega)
  have h32 : (⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ : Region).Contains
      (p+BitVec.ofNat 64 (6000+64*mask+32)) 8 := Offset.contains p (by omega) (by omega) (by omega)
  exact ((Frame.refl _ m).write (by simp) _ h16).writeW (by simp) _ h32

theorem initEntryMemory_read (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    (initEntryMemory m p mask).read (p+BitVec.ofNat 64 (6000+64*mask)) 16=shuffleWord mask ∧
    (initEntryMemory m p mask).readW (p+BitVec.ofNat 64 (6000+64*mask+32)) 64=
      BitVec.ofNat 64 (acceptedIndices mask).length := by
  rw [initEntryMemory_eq m p hm]
  constructor
  · rw [Mem.writeW,Mem.read_write_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
    have hs := Mem.readW_writeW_self m (p+BitVec.ofNat 64 (6000+64*mask)) 16 (shuffleWord mask) (by decide)
    simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using hs
  · exact Mem.readW_writeW_self64 _ _ _

theorem initEntryMemory_other (m : Mem) (p : Addr) {mask other : Nat}
    (hm : mask<16) (ho : other<16) (hne : other≠mask) :
    (initEntryMemory m p mask).read (p+BitVec.ofNat 64 (6000+64*other)) 16=
      m.read (p+BitVec.ofNat 64 (6000+64*other)) 16 ∧
    (initEntryMemory m p mask).readW (p+BitVec.ofNat 64 (6000+64*other+32)) 64=
      m.readW (p+BitVec.ofNat 64 (6000+64*other+32)) 64 := by
  have hf := initEntryMemory_frame m p hm
  have hd : (⟨p+BitVec.ofNat 64 (6000+64*other),64⟩ : Region).Disjoint
      ⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ := Offset.disjoint p (by omega) (by omega) (by omega)
  constructor
  · exact hf.read (Offset.contains p (e := 6000+64*other) (k := 64) (by omega) (by omega) (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)
  · exact hf.readW (Offset.contains p (e := 6000+64*other) (k := 64) (by omega) (by omega) (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
