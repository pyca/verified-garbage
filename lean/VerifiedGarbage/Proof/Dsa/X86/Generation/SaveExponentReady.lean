module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SavedContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferValues
import VerifiedGarbage.Proof.Mont.Words32Offset
import VerifiedGarbage.Proof.Mont.Words32Parts
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Save the prepared exponent and one-hot while retaining all Montgomery constants. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem save_exponent_ready {s : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (C : PrimeContext base n candidate s)
    (upper : n ≤ 48)
    (exponent : val32 s.mem (off base Layout.arithmetic) 160 (2 * n) = Spec.MillerRabin.exponent candidate)
    (tail : (word s.mem (off base Layout.arithmetic) 64).toNat =
      2 ^ ((Spec.Rsa.splitTwos (candidate - 1)).1 % 64)) :
    WP isa (transferWords (saveExponentTransfers n)) s fun t =>
      SavedContext base n candidate t ∧ Frame [⟨base, montgomeryBytes⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (save_exponent scr upper capacity) fun t ⟨value, hot, F, K⟩ => ?_
  have bound := slot_bound (n := n) (i := 8) (by decide)
  have size := C.parent.size_le
  have ranges : ∀ r ∈ transferRanges (saveExponentTransfers n),
      slot n 8 ≤ r.1 ∧ r.1 + r.2 ≤ slot n 8 + 8 * n + 8 := by
    intro r hr
    simp only [transferRanges, saveExponentTransfers, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> constructor <;> omega
  have out : Outside base (slot n 8) (8 * n + 8) s.mem t.mem :=
    F.enclose (by intro r hr; have := ranges r hr; omega)
  have s08 := slot_le (n := n) (i := 0) (j := 8) (by decide)
  have parent := C.parent.outside_keep K (by decide) (by decide) out
    (.inl (by unfold stride at s08; omega)) (by have := slot_header n 8; omega)
  have same : ∀ j < 8, wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    intro j hj
    have apart := slot_le (n := n) hj
    have bj := slot_bound (n := n) (i := j) (by omega)
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact out.val32 (.inl (by unfold stride at apart; omega)) (by
      unfold stride at bj; unfold montgomeryBytes at size; omega)
  refine ⟨⟨⟨parent, (same 3 (by decide)).trans C.ordinary, (same 4 (by decide)).trans C.square,
    (same 6 (by decide)).trans C.one, (same 7 (by decide)).trans C.minus⟩, ?_, ?_⟩, ?_, K⟩
  · rw [wordsVal_eq_val32, value, ← val32_off]; exact exponent
  · apply BitVec.eq_of_toNat_eq
    rw [word_toNat_val32, hot, ← val32_off, ← word_toNat_val32, tail,
      BitVec.toNat_twoPow_of_lt (Nat.mod_lt _ (by decide : 0 < 64))]
  · exact F.frame (by
      intro r hr; have := ranges r hr; unfold stride at bound; omega)

end VG.Proof.Dsa.X86.Generation
