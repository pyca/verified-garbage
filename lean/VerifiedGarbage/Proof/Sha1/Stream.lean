module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Streaming SHA-1: facts about the specification

How `Repr` evolves as bytes are buffered and blocks compressed, and how the
padded message decomposes, independently of any target.
-/

@[expose] public section

namespace VG.Proof.Sha1.Stream

open VG.Spec.Sha1

theorem compressList_zero (H : HashValue) (p : List Byte) : compressList H p 0 = H := by
  simp only [compressList, List.range_zero, List.foldl_nil]

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr} (h : ∀ i < 20, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    stateAt mem' p = stateAt mem p := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  apply Mem.readW_congr
  intro i hi
  rw [show p + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (4 * k + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]]
  exact h _ (by omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    bytesAt mem' p n = bytesAt mem p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- `Repr` only depends on the 84 bytes of the state. -/
theorem repr_congr {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 84, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha1.Repr mem p m) : Spec.Sha1.Repr mem' p m := by
  refine ⟨by rw [stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply bytesAt_congr
  intro i hi
  have := h (20 + i) (by omega)
  rwa [show p + 20 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (20 + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]

export VG.WriteBytes (writeBytes writeBytes_nil writeW8_apply writeBytes_snoc writeBytes_before writeBytes_frame write_eq_writeBytes writeBytes_append)

/-! ## `Repr` -/

theorem repr_nil {mem : Mem} {p : Addr} (h : stateAt mem p = H0) : Spec.Sha1.Repr mem p [] := by
  simp [Spec.Sha1.Repr, h, compressList_zero, bytesAt]

/-! ## Padding -/

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < 64, f k = g k) : parseBlock f = parseBlock g := by
  funext j
  have := j.isLt
  simp only [parseBlock]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

end VG.Proof.Sha1.Stream
