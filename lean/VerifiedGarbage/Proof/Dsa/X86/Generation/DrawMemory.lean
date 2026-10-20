module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyStep
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.KeyCopy

/-! # Byte-copy and counter-store frames for witness draws -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem copyOutside_frame {p : Addr} {len : Nat} {s t : Mem} (O : Outside p 0 len s t) :
    Frame [⟨p, len⟩] s t := by
  intro x hx
  have outside := hx ⟨p, len⟩ (by simp)
  change ¬ (ofs p x + 1 ≤ len) at outside
  exact O x (.inr (by omega))

theorem drawStore_frame (s : Mem) (base : Addr) (value : BitVec 32) :
    Frame [⟨off base primeUsed, 4⟩] s (s.writeW (off base primeUsed) value) := by
  exact (Frame.refl _ _).writeW (by simp) value (Region.contains_self _ 4)

theorem drawFrame_bytes {s t : Mem} {rs : List Region} {p : Addr} {len : Nat}
    (O : Frame rs s t) (apart : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (fit : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t p len = Spec.Rsa.bytesAt s p len := by
  apply List.map_congr_left
  intro i hi
  exact O.bytes apart fit (List.mem_range.mp hi)

theorem copied_unmasked {s t : State} {src out : BitVec 32} {len : Nat}
    (I : KeyCopyInv src out len len (BitVec.allOnes 32) s t) :
    Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = Spec.Rsa.bytesAt s.mem (src.setWidth 64) len := by
  rw [I.result]
  simp only [BitVec.and_allOnes, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
  exact List.map_id _
end VG.Proof.Dsa.X86.Generation
