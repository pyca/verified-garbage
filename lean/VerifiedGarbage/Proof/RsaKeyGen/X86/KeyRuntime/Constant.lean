module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Small
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Framework.Omega

/-! # Small constants in the persistent runtime-width bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr S)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem constant_ok {s : State} {B : Addr} {Z n N j : Nat}
    (h : Ws s B Z n N) (hj : j < N) (x : BitVec 32) :
    WP isa (cn j x) s fun t => Ws t B Z n N ∧ Keep B n [j] [] s.mem t.mem ∧
      num t.mem B n j = x.toNat ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.arr_fit hj
  refine WP.mono (small_ok h .modulus x (by
    simpa only [offset_array, Width.words, S] using fit)) fun t ⟨ht, O, V, K⟩ => ?_
  simp only [offset_array, Width.words] at O V
  have bound : val32 t.mem B (arr n j) (n + 2) < 2 ^ (32 * n) := by
    rw [V]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by have := h.wpos; omega))
  exact ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O)
      (by simp only [S]; omega) (by simp),
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2) bound).trans V, K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
