import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Cmac.Block32

/-!
# CBC: blocks moved as 32-bit words

On the 32-bit targets, a block is XORed into another in place, a word at a
time (`Cmac.xor4Mem m c c q`), and copied as a zeroed block XORed with the
source (`copy4Mem`), on every 32-bit target.
-/

namespace VG.Proof.AesCbc

open VG
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (xor4Mem zero4 Sep4)

/-- The block at `q` copied to `c`: `c` zeroed, then XORed with `q`. -/
def copy4Mem (m : Mem) (c q : Addr) : Mem := xor4Mem (zero4 m c) c c q

theorem zeros_xor {x : List Byte} (hx : x.length = 16) : Spec.Cmac.xor (Spec.Cmac.zeros 16) x = x := by
  apply List.ext_getElem (by simp [Spec.Cmac.xor, Spec.Cmac.zeros, hx])
  intro i h₁ h₂
  simp only [Spec.Cmac.xor, Spec.Cmac.zeros, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.zero_xor

theorem zero4_frame (m : Mem) (c : Addr) : Frame [⟨c, 16⟩] m (zero4 m c) := Proof.Cmac.frame_store4 c 0 0 0 0

theorem copy4Mem_frame (m : Mem) (c q : Addr) : Frame [⟨c, 16⟩] m (copy4Mem m c q) :=
  (zero4_frame m c).trans (Proof.Cmac.xor4Mem_frame _ _ _ _)

theorem copy4Mem_bytes (m : Mem) {c q : Addr} (hcq : (⟨c, 16⟩ : Region).Disjoint ⟨q, 16⟩) :
    bytesAt (copy4Mem m c q) c 16 = bytesAt m q 16 := by
  rw [copy4Mem, Proof.Cmac.xor4Mem_bytes _ (Sep4.self c) (Sep4.of_disjoint hcq), Proof.Cmac.zero4_bytes,
    Proof.Cmac.bytesAt_frame (zero4_frame m c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hcq.symm) (by decide),
    zeros_xor (by simp [bytesAt])]

/-- The block at `q` XORed into the block at `c`. -/
theorem xorIn4_bytes (m : Mem) {c q : Addr} (hcq : (⟨c, 16⟩ : Region).Disjoint ⟨q, 16⟩) :
    bytesAt (xor4Mem m c c q) c 16 = Spec.Cbc.xor (bytesAt m c 16) (bytesAt m q 16) :=
  Proof.Cmac.xor4Mem_bytes _ (Sep4.self c) (Sep4.of_disjoint hcq)

end VG.Proof.AesCbc
