import VerifiedGarbage.Proof.Weierstrass.X86.InvSet
import VerifiedGarbage.Proof.Mont.X86.Ops

/-! # Zero-extending the inputs and initializing a coefficient to one -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem copyPad_ok {s : State} {base : Addr} {size dst src : Nat}
    (hs : Scr s base size) (hd : dst + 36 ≤ size) (ha : src + 32 ≤ size)
    (sep : dst ≤ src ∨ src + 32 ≤ dst) :
    WP isa (.block (copyPad dst src)) s fun z =>
      val32 z.mem base dst 9 = val32 s.mem base src 8 ∧
      Keeps [.eax] s z ∧ Outside base dst 36 s.mem z.mem := by
  have hn := hs.nowrap
  unfold copyPad
  refine WP.block_append (WP.mono (copy_ok 8 hs (by omega) ha sep) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)
  refine WP.mono (zeros_ok (hs.of_keeps K₁ (by decide)) (acc := dst + 32) (k := 1) (by omega))
    fun z ⟨O₂, V₂, K₂⟩ => ⟨?_, K₁.trans K₂, ?_⟩
  · simp only [val32, Nat.mul_zero, Nat.add_zero] at V₂
    rw [val32_succ, O₂.val32 (by omega) (by omega), V₁]
    change _ + 2 ^ (32 * 8) * w32 z.mem base (dst + 32) = _
    rw [V₂, Nat.mul_zero, Nat.add_zero]
  · intro x hx
    rw [O₂ x (by omega), O₁ x (by omega)]

theorem one8_ok {s : State} {base : Addr} {size dst : Nat}
    (hs : Scr s base size) (hd : dst + 32 ≤ size) :
    WP isa (.block (one8 dst)) s fun z =>
      val32 z.mem base dst 8 = 1 ∧ Keeps [.eax] s z ∧ Outside base dst 32 s.mem z.mem := by
  have hn := hs.nowrap
  unfold one8
  refine WP.block_append (WP.mono (zeros_ok hs hd) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  refine WP.mono (setWord_ok 1 (hs.of_keeps K₁ (by decide)) (by omega))
    fun z ⟨V₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂, ?_⟩
  · have Vtail : val32 s₁.mem base (dst + 4) 7 = 0 := by
      change w32 s₁.mem base dst + 2 ^ 32 * val32 s₁.mem base (dst + 4) 7 = 0 at V₁
      omega
    change w32 z.mem base dst + 2 ^ 32 * val32 z.mem base (dst + 4) 7 = 1
    rw [V₂, O₂.val32 (by omega) (by omega), Vtail]
    rfl
  · intro x hx
    rw [O₂ x (by omega), O₁ x hx]

end VG.Proof.Weierstrass.X86.Inv
