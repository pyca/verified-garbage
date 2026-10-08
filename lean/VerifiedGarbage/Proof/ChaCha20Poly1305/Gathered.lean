import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ChaCha20-Poly1305 out of place: the slices

Untrusted: everything here is checked by Lean. The slices of
`vg_chacha20_poly1305_seal_gather` are read as those of
`vg_aes_gcm_seal_gather` (the same definitions over bytes read the same
way), so its code gathers them with AES-GCM's, proven against `Spec.Gcm`'s.
The bytes of the key, the nonce and the additional data are what they were
through writes apart from them (`bytesAt_frame`), and the bytes gathered are
at `dst` (`bytesAt_writeBytes_self`).
-/

namespace VG.Proof.ChaCha20Poly1305

theorem bytesAt_eq_aes : Spec.Poly1305.bytesAt = Spec.Aes.bytesAt := rfl

theorem gathered_eq_gcm : Spec.ChaCha20Poly1305.gathered = Spec.Gcm.gathered := rfl

theorem gatheredLen_eq_gcm : Spec.ChaCha20Poly1305.gatheredLen = Spec.Gcm.gatheredLen := rfl

open VG VG.WriteBytes
open VG.Spec.Poly1305 (bytesAt)

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₂, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

end VG.Proof.ChaCha20Poly1305
