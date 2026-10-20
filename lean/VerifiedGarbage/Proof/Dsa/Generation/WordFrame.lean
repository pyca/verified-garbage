module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! # Unchanged frame words imply unchanged frame bytes -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

theorem words_preserve_byte {m m' : Mem} {B : Addr} {count i : Nat}
    (hw : ∀ k < count, m'.readW (off B (8 * k)) 64 = m.readW (off B (8 * k)) 64)
    (hi : i < 8 * count) : m' (off B i) = m (off B i) := by
  have he : off B (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) = off B i := by
    simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 8 * (i / 8) + i % 8 = i by omega]
  have h := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * (i % 8)) 8)
    (hw (i / 8) (by omega))
  change (m'.read (off B (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 =
    (m.read (off B (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 at h
  rw [Mem.extractLsb'_read m' _ (by omega), Mem.extractLsb'_read m _ (by omega), he] at h
  exact h

theorem frame_without_words {m m' : Mem} {B : Addr} {count : Nat} {rs : List Region}
    (hf : Frame (⟨B, 8 * count⟩ :: rs) m m')
    (hw : ∀ k < count, m'.readW (off B (8 * k)) 64 = m.readW (off B (8 * k)) 64) :
    Frame rs m m' := by
  intro x hx
  by_cases hB : (⟨B, 8 * count⟩ : Region).Contains x 1
  · have hi : (x - B).toNat < 8 * count := by
      change (x - B).toNat + 1 ≤ 8 * count at hB
      omega
    have he : off B (x - B).toNat = x := by
      simp only [off, BitVec.ofNat_toNat]
      bv_omega
    simpa only [he] using words_preserve_byte hw hi
  · apply hf x
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hB
    · exact hx r hr

end VG.Proof.Dsa.Generation
