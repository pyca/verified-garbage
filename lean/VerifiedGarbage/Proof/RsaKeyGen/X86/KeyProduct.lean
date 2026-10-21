module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductCorrect

/-! # Prime products in the native RSA key workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem product_ok {s : State} {B : Addr} {Z n N out a b k : Nat}
    (h : Ws s B Z n N) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (ho : out < N) (ha : a < N) (hb : b < N) (oa : out ≠ a) (ob : out ≠ b) :
    WP isa (primeProduct n out a b) s fun t =>
      Ws t B Z n N ∧ Keep B n [out] [kProduct] s.mem t.mem ∧
      val32 t.mem B (arr n out) (n + 2) =
        val32 s.mem B (arr n a) k * val32 s.mem B (arr n b) k ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have sa := arr_disj (w := n) oa
  have sb := arr_disj (w := n) ob
  have head := h.hdr_le
  have L : Product.Layout Z k k (arr n out) (arr n a) (arr n b) kProduct := by
    refine ⟨positive, positive, even, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [S, arr, VG.Impl.Rsa.X86.Keys.hdr, kProduct] at *
    all_goals omega
  unfold primeProduct
  change WP isa (Impl.RsaKeyGen.X86.Product.code (n / 2) (n / 2)
    (arr n out) (arr n a) (arr n b) kProduct) s _
  have nk : n / 2 = k := by omega
  rw [nk]
  refine WP.mono (Product.correct h.workspace L) fun t ⟨O, V, K⟩ => ?_
  refine ⟨h.rest K, ?_, ?_, K⟩
  · intro x hx
    apply O x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx _ (by simp [ranges])
    · have H := hx (arr n out, S n) (by simp [ranges])
      simpa only [S, width, Nat.two_mul] using H
  · simpa only [width, Nat.two_mul, Nat.add_assoc] using V

end VG.Proof.RsaKeyGen.X86.Key
