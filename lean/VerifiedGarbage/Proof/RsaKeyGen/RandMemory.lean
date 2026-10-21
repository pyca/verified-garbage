module

public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Byte segments of the entropy buffer, independently of the machine target -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG

theorem seg_bytesAt (m : Mem) (p : Addr) {a n k : Nat} (h : a + n ≤ k) :
    seg (Spec.Rsa.bytesAt m p k) a n = Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) n := by
  unfold seg Spec.Rsa.bytesAt
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rand_bytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem frame_bytesAt {m m' : Mem} {rs : List Region} {p : Addr} {n : Nat}
    (F : Frame rs m m') (apart : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (fit : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact F.bytes apart fit (List.mem_range.mp hi)

end VG.Proof.RsaKeyGen
