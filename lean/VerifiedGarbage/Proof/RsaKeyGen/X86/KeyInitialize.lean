module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyZero
import VerifiedGarbage.Proof.Rsa.X86.KeyWord
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # Initialize the complete native key bank before reading any temporary -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem clearArrays_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (clearArrays n) s fun t =>
      Ws t B Z n 32 ∧ Outs B [(hdr, 32 * S n)] s.mem t.mem ∧
      num t.mem B n aOne = 1 ∧ (∀ j, j < 32 → j ≠ aOne → num t.mem B n j = 0) ∧
      Keeps [.eax, .ebp, .edx] s t := by
  unfold clearArrays nArr
  refine WP.seq (WP.mono (zero_arrays h (by decide)) fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have lowZero (j : Nat) (hj : j < 32) : num u.mem B n j = 0 := by
    have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zero j hj) (a := 0) (c := n) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using H
  refine WP.mono (setOne_ok hu (by decide)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  rw [lowZero aOne (by decide), Nat.zero_div, Nat.mul_zero, Nat.add_zero] at value
  refine ⟨ht, ?_, value, ?_, Ku.trans (Kt.mono (by decide))⟩
  · have first : Outs B [(hdr, 32 * S n)] s.mem u.mem :=
      Outs.of_outside Ou (by simp only [S, Nat.mul_left_comm, List.mem_singleton])
    have last : Outs B [(hdr, 32 * S n)] u.mem t.mem := by
      apply VG.Proof.Rsa.outs_cover Ot
      intro r hr
      change r ∈ [(arr n aOne, S n)] at hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨(hdr, 32 * S n), by simp, Nat.le_add_right .., ?_⟩
      exact arr_end (w := n) (by decide : aOne < 32)
    exact first.trans last
  · intro j hj different
    exact (Ot.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact Ne.symm different) (by simp) (h.fit64 hj)).trans (lowZero j hj)

end VG.Proof.RsaKeyGen.X86.Key
