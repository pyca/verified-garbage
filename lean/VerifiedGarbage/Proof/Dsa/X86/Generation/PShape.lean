module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ShapeWorkspace
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.StoredHashes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The shared byte shaper turns stored hash contributions into the exact modulus-search X. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.Generation

theorem p_hashes_value {m : Mem} {base : Addr} {digestLen count offset : Nat} {seed : List Byte}
    (hashes : ∀ j < count + 1, Spec.Rsa.bytesAt m (off base (Layout.hashes + (count - j) * digestLen)) digestLen =
      Spec.Dsa.seedHash (8 * digestLen) (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j)))) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off base Layout.hashes) ((count + 1) * digestLen)) =
      contributions (8 * digestLen) (pDigest (8 * digestLen) seed offset) (count + 1) := by
  have stored := stored_hash_value m (off base Layout.hashes) digestLen count
    (fun j => Spec.Dsa.seedHash (8 * digestLen) (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j))))
    (by intro j hj; rw [VG.Proof.Bignum.off_off]; exact hashes j hj)
  have digestEq : (fun j => Spec.Dsa.decodeBE (Spec.Dsa.seedHash (8 * digestLen)
      (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j))))) =
      pDigest (8 * digestLen) seed offset := by
    funext j
    unfold pDigest
    rw [Nat.add_assoc]
  rw [digestEq] at stored
  exact stored

theorem p_shape {s : State} {base : Addr} {bytes digestLen count pLen offset : Nat} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (lower : 2 ≤ pLen)
    (room : pLen ≤ (count + 1) * digestLen) (fit : (count + 1) * digestLen ≤ 384)
    (hashes : ∀ j < count + 1, Spec.Rsa.bytesAt s.mem (off base (Layout.hashes + (count - j) * digestLen)) digestLen =
      Spec.Dsa.seedHash (8 * digestLen) (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j)))) :
    WP isa (pShape digestLen count pLen) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off base Layout.shaped) pLen) =
        Spec.Ffdh.candidateOf (8 * pLen) (contributions (8 * digestLen)
          (pDigest (8 * digestLen) seed offset) (count + 1)) ∧
      Frame [⟨off base Layout.shaped, pLen⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  let bs := Spec.Rsa.bytesAt s.mem (off base (Layout.hashes + ((count + 1) * digestLen - pLen))) pLen
  have size : bs.length = pLen := by simp only [bs, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  unfold pShape
  refine WP.mono (shape_workspace (bs := bs) scr lower size
    (by unfold Layout.hashes; omega) (by unfold Layout.shaped; omega)
    (.inl (by unfold Layout.hashes Layout.shaped; omega)) rfl) fun t ⟨shaped, F, K⟩ => ?_
  refine ⟨?_, F, K⟩
  rw [shaped, VG.Proof.Dsa.decodeBE_os2ip,
    VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value
      (by intro h; rw [h] at size; simp only [List.length_nil] at size; omega) (by decide : 7 < 8)
      (by omega : 8 * pLen = 8 * (bs.length - 1) + 7 + 1)]
  have suffix := bytesAt_suffix_value s.mem (off base Layout.hashes) ((count + 1) * digestLen - pLen) pLen
  rw [Nat.sub_add_cancel room, p_hashes_value hashes, VG.Proof.Bignum.pow256_eq, VG.Proof.Bignum.off_off] at suffix
  change Spec.Ffdh.candidateOf (8 * pLen) (Spec.Dsa.decodeBE bs) = _
  rw [← suffix, candidateOf_mod_width (by omega) (Nat.le_refl _)]

end VG.Proof.Dsa.X86.Generation
