import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM: the key context under frames, and bytes written

Untrusted: everything here is checked by Lean. Facts the functions that call
`vg_aes_gcm_seal` on every target share: the key context is what it was
through writes apart from it (`ctx_frame`), and the bytes written at an
address are there (`bytesAt_writeBytes_self`).
-/

namespace VG.Proof.AesGcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH)

/-- The key context, through a frame of regions apart from it. -/
theorem ctx_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 256⟩ : Region).Disjoint r) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R ∧ ctxH m' K = ctxH m K := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  refine ⟨?_, ?_⟩
  · simp only [ctxCiph]
    rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
  · simp only [ctxH, Spec.Gcm.blockAt]
    exact congrArg _ (Proof.Cmac.bytesAt_frame hf (p := K + BitVec.ofNat 64 240) (fun r hr => (hd r hr).sub_left
      (Offset.sub_base K (show 240 + 16 ≤ 256 by decide))) (by decide))

/-- The bytes written at `q` are there. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₂, ite_true]
    simp [List.getD_eq_getElem?_getD, h₂]

end VG.Proof.AesGcm
