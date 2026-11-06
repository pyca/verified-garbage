module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseLoad
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop

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

end VG.Proof.RsaKeyGen.X86.Key
