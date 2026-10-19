module

public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Framework.Omega

/-! Workspace headers survive writes to disjoint output byte buffers. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

theorem workspace_of_words {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hm : ∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = B) : Ws t B Z w := by
  have hz := h.h256
  exact ⟨h.scr.congr hwr, h0,
    (hm _ (by simp only [sW]; omega)).trans h.hw,
    (hm _ (by simp only [sStride, sFn]; omega)).trans h.hS,
    fun j hj => (hm _ (by simp only [sArr]; omega)).trans (h.harr j hj), h.hZ, h.w1, h.w2⟩

end VG.Proof.Dsa.AArch64.Generation
