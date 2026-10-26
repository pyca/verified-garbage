module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive

/-! # Run a small inverse without disturbing a modulus-width RSA workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

theorem inverse_end_le {k n j : Nat} (width : k ≤ n) (persistent : 15 ≤ j) :
    arr k 15 ≤ arr n j := by
  have small : arr k 15 ≤ arr n 15 := by unfold arr S; omega
  exact Nat.le_trans small (arr_mono persistent)

theorem inverse_workspace {s : State} {B : Addr} {Z n k : Nat} (h : Ws s B Z n 32)
    (positive : 0 < k) (width : k ≤ n) : Ws s B Z k 15 :=
  ⟨h.workspace, Nat.le_trans (inverse_end_le width (by decide)) h.fits,
    positive, Nat.le_trans width h.wle⟩

theorem inverse_array_layout {s : State} {B : Addr} {Z n k a b : Nat}
    (h : Ws s B Z n 32) (width : k ≤ n) (ha : a < 32) (hb : b < 32)
    (pa : 15 ≤ a) (pb : 15 ≤ b) : InverseLayout Z k (arr n a) (arr n b) := by
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  refine ⟨?_, ?_, Or.inr (inverse_end_le width pa), Or.inr (inverse_end_le width pb)⟩
  · unfold S at fa
    omega
  · unfold S at fb
    omega

theorem inverse_preserves_num {m m' : Mem} {B : Addr} {n k j : Nat}
    (width : k ≤ n) (persistent : 15 ≤ j) (fit : arr n j + S n ≤ 2 ^ 64)
    (changed : Outs B (inverseRanges k invSlots) m m') : num m' B n j = num m B n j := by
  apply changed.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have endBound := inverse_end_le width persistent
    have endEq : arr k 15 = hdr + 4 * (15 * (k + 2)) := by unfold arr S; omega
    rw [endEq] at endBound
    exact Or.inr endBound
  all_goals have lower : hdr ≤ arr n j := Nat.le_add_right ..
  all_goals simp only [sOdd, sB, sC, hdr] at lower ⊢
  all_goals omega

theorem inverse_preserves_slot {m m' : Mem} {B : Addr} {k d : Nat}
    (bound : d + 4 ≤ 100) (changed : Outs B (inverseRanges k invSlots) m m') :
    slot m' B d = slot m B d := by
  have value : val32 m' B d 1 = val32 m B d 1 := by
    apply changed.val32 _ (by omega)
    intro r hr
    simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals simp only [sOdd, sB, sC, hdr]
    all_goals omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

end VG.Proof.RsaKeyGen.X86.Key
