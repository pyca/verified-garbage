module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Clear
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Small
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # Every array cleared and one set, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (arr S num)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (aOne)

/-- `Key.clearArrays_ok` at the run-time width. -/
theorem clearInputs_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa clearInputs s fun t =>
      Ws t B Z n 32 ∧ Outs B [(VG.Impl.Rsa.X86.Keys.hdr, 32 * S n)] s.mem t.mem ∧
      num t.mem B n aOne = 1 ∧ (∀ j, j < 32 → j ≠ aOne → num t.mem B n j = 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  have oneFit := h.arr_fit (j := aOne) (by decide)
  unfold S at oneFit
  unfold clearInputs
  refine WP.seq (WP.mono (clear_ok h .modulus (by decide) (k := 32) (by decide) (by decide))
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have lowZero (j : Nat) (hj : j < 32) : num u.mem B n j = 0 := by
    have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zero j hj) (a := 0) (c := n) (by simp only [Width.words]; omega)
    simp only [Nat.mul_zero, Nat.add_zero] at H
    exact H
  refine WP.mono (small_ok hu .modulus 1 (j := aOne) (by change arr n aOne + _ ≤ Z; simp only [Width.words]; omega))
    fun t ⟨ht, Ot, value, Kt⟩ => ?_
  change Outside B (arr n aOne) (4 * (n + 2)) u.mem t.mem at Ot
  change val32 t.mem B (arr n aOne) (n + 2) = 1 at value
  have outer : Outside B VG.Impl.Rsa.X86.Keys.hdr (4 * (32 * (n + 2))) s.mem u.mem := by
    simpa only [Width.words] using Ou
  refine ⟨ht, ?_, ?_, ?_, Ku.trans (Kt.mono (by decide))⟩
  · refine (Outs.of_outside (outer.mono (Nat.le_refl _) (by unfold S; omega)) (List.mem_singleton_self _)).trans
      (Outs.of_outside (Ot.mono (o' := VG.Impl.Rsa.X86.Keys.hdr) (n' := 32 * S n) ?_ ?_) (List.mem_singleton_self _))
    · unfold VG.Proof.Rsa.X86.Keys.arr; omega
    · unfold VG.Proof.Rsa.X86.Keys.arr S aOne; omega
  · change val32 t.mem B (arr n aOne) n = 1
    rw [VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2)
      (by rw [value]; exact Nat.one_lt_two_pow (by have := h.size; omega)), value]
  · intro j hj different
    change val32 t.mem B (arr n j) n = 0
    have D := VG.Proof.Rsa.X86.Keys.arr_disj (w := n) different
    have fit := h.arr_fit hj
    unfold S at D fit
    rw [Ot.val32 (by omega) (by omega)]
    exact lowZero j hj

end VG.Proof.RsaKeyGen.X86.KeyRuntime
