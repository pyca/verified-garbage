module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.PolicyMemory
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Util.CompileInductive

/-! Updating packed native fields preserves every unrelated complete policy word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch

theorem fields_word (m : Mem) (base : BitVec 32) (values : List (Nat × BitVec 32))
    (bounds : ∀ e ∈ values, e.1 < 16) {j : Nat} (hj : j < 16)
    (absent : ∀ e ∈ values, j ≠ e.1) :
    (writeLow m base values).readW (off (State.addr base) (8 * j)) 64 =
      m.readW (off (State.addr base) (8 * j)) 64 := by
  apply word_eq
  · rw [lowWord_writeLow _ _ _ bounds j hj, lowValue_unchanged _ _ _ absent]
  · exact highWord_writeLow _ _ _ bounds j hj

theorem counter_store_low (m : Mem) (base : BitVec 32) (value : BitVec 64) {j : Nat}
    (positive : 0 < j) (bound : j < 16) :
    lowWord (m.writeW (State.addr base) value) base j = lowWord m base j := by
  unfold lowWord
  exact Mem.readW_writeW_sep (fun x hx hy => VG.Offset.sep_base (State.addr base) (by omega : 8 ≤ 8 * j)
    (by omega : 8 * j + 4 ≤ 2 ^ 64) x hy hx) (by decide)

theorem counter_store_word (m : Mem) (base : BitVec 32) (value : BitVec 64) {j : Nat}
    (positive : 0 < j) (bound : j < 16) :
    (m.writeW (State.addr base) value).readW (off (State.addr base) (8 * j)) 64 =
      m.readW (off (State.addr base) (8 * j)) 64 := by
  exact Mem.readW_writeW_sep (fun x hx hy => VG.Offset.sep_base (State.addr base) (by omega : 8 ≤ 8 * j)
    (by omega : 8 * j + 8 ≤ 2 ^ 64) x hy hx) (by decide)

theorem counter_store_frame (m : Mem) (base : BitVec 32) (value : BitVec 64) :
    Frame [⟨State.addr base, 128⟩] m (m.writeW (State.addr base) value) := by
  apply (Frame.refl _ _).writeW (List.mem_singleton_self _)
  simpa only [off, BitVec.add_zero] using
    (Offset.contains_base (State.addr base) (by decide : 0 + 8 ≤ 128) (by decide : 0 < 2 ^ 64))

end VG.Proof.Ffdh.Arm.ParameterSearch
