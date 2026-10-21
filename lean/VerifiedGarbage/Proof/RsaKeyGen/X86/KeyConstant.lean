module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # Exact constants in the native RSA key workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem constArray_ok {s : State} {B : Addr} {Z n N j x : Nat}
    (h : Ws s B Z n N) (hj : j < N) (bound : x < 2 ^ (32 * n)) :
    WP isa (constArray n j x) s fun t =>
      Ws t B Z n N ∧ Keep B n [j] [] s.mem t.mem ∧ num t.mem B n j = x ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have fit := h.arr_fit hj
  have larger : x < 2 ^ (32 * (n + 2)) :=
    Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
  unfold constArray
  refine WP.mono (setConstW_ok h.workspace (by omega)
    (by change arr n j + 4 * (n + 2) ≤ Z; exact fit) larger) fun t ⟨V, K, O⟩ => ?_
  change val32 t.mem B (arr n j) (n + 2) = x at V
  change Outside B (arr n j) (4 * (n + 2)) s.mem t.mem at O
  refine ⟨h.rest K, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O)
    (by unfold S; omega) (by simp), ?_, K⟩
  exact (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2)
    (by rw [V]; exact bound)).trans V

end VG.Proof.RsaKeyGen.X86.Key
