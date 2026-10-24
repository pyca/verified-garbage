module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # The low words and identity matrix for an RSA GCD batch -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

theorem start_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size) :
    WP isa (.block (VG.Impl.Rsa.X86.GcdBatch.start n)) s fun u =>
      wordState u.mem base (offset n 3) =
        ⟨s.mem.readW (off base (offset n 3)) 32, s.mem.readW (off base (offset n 4)) 32,
          s.mem.readW (off base (offset n 5)) 32, 1, 0, 0, 1⟩ ∧
      Keeps [.eax] s u ∧ Outside base ((offset n 3) + 4) 24 s.mem u.mem := by
  have nowrap := hs.nowrap
  unfold VG.Impl.Rsa.X86.GcdBatch.start
  refine WP.block_append (WP.block_append (WP.mono
    (copy_ok 1 hs (o := (offset n 3) + 4) (a := (offset n 4)) (by apart) (by apart) (by apart))
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_))
  simp only [val32, Nat.mul_zero, Nat.add_zero] at F₁
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copy_ok 1 hs₁ (o := (offset n 3) + 8) (a := (offset n 5)) (by apart) (by apart) (by apart))
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  simp only [val32, Nat.mul_zero, Nat.add_zero] at G₂
  rw [O₁.w32 (by apart) (by apart)] at G₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (setMatrix_ok hs₂ (dst := (offset n 3) + 12) (by apart))
    fun u ⟨U, V, Q, R, K₃, O₃⟩ => ⟨?_, (K₁.trans K₂).trans K₃, ?_⟩
  · have D : w32 u.mem base (offset n 3) = w32 s.mem base (offset n 3) := by
      rw [O₃.w32 (by apart) (by apart), O₂.w32 (by apart) (by apart), O₁.w32 (by apart) (by apart)]
    have F : w32 u.mem base ((offset n 3) + 4) = w32 s.mem base (offset n 4) := by
      rw [O₃.w32 (by apart) (by apart), O₂.w32 (by apart) (by apart), F₁]
    have G : w32 u.mem base ((offset n 3) + 8) = w32 s.mem base (offset n 5) := by
      rw [O₃.w32 (by apart) (by apart), G₂]
    simp only [wordState, atWord, Divstep.W32.WSt.mk.injEq, Nat.reduceMul, Nat.add_zero]
    refine ⟨BitVec.eq_of_toNat_eq D, BitVec.eq_of_toNat_eq F, BitVec.eq_of_toNat_eq G,
      BitVec.eq_of_toNat_eq U, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base ((offset n 3) + 16) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using V
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base ((offset n 3) + 20) = 0
      simpa only [Nat.add_assoc, Nat.reduceAdd] using Q
    · apply BitVec.eq_of_toNat_eq
      change w32 u.mem base ((offset n 3) + 24) = 1
      simpa only [Nat.add_assoc, Nat.reduceAdd] using R
  · intro x hx
    rw [O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Rsa.X86.GcdBatch
