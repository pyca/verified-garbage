module

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Row
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # Applying both thirty-step matrix rows -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

local macro "apart" : tactic => `(tactic|
  (dsimp only [offset] at *; omega))

/-- Both full-width values are updated before either source is overwritten. -/
theorem update_ok {s : State} {base : Addr} {size n p : Nat} {u v q r f g : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hu : s.mem.readW (VG.Proof.Mont.off base (offset n 3+12)) 32 = BitVec.ofInt 32 u)
    (hv : s.mem.readW (VG.Proof.Mont.off base (offset n 3+16)) 32 = BitVec.ofInt 32 v)
    (hq : s.mem.readW (VG.Proof.Mont.off base (offset n 3+20)) 32 = BitVec.ofInt 32 q)
    (hr : s.mem.readW (VG.Proof.Mont.off base (offset n 3+24)) 32 = BitVec.ofInt 32 r)
    (huv : |u|+|v| ≤ 2^30) (hqr : |q|+|r| ≤ 2^30)
    (hf : (val32 s.mem base (offset n 4) (n+1) : Int) % 2^(32*(n+1)) = f % 2^(32*(n+1)))
    (hg : (val32 s.mem base (offset n 5) (n+1) : Int) % 2^(32*(n+1)) = g % 2^(32*(n+1)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2^(32*n+1))
    (hdivF : 2^30 ∣ u*f+v*g) (hdivG : 2^30 ∣ q*f+r*g) :
    WP isa (.block (update n)) s fun z =>
      (val32 z.mem base (offset n 4) (n+1) : Int) % 2^(32*(n+1)) =
        ((u*f+v*g)/2^30) % 2^(32*(n+1)) ∧
      (val32 z.mem base (offset n 5) (n+1) : Int) % 2^(32*(n+1)) =
        ((q*f+r*g)/2^30) % 2^(32*(n+1)) ∧
      Keeps clob s z ∧ Unch base (writes n) s.mem z.mem := by
  have nowrap := hs.nowrap
  unfold VG.Impl.Rsa.X86.GcdBatch.update
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (row_ok (r:=0) hs hn hz (by decide) (by simpa using hu) (by simpa using hv)
      huv hf hg hfb hgb hp hdivF) fun s₁ ⟨F₁,K₁,O₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have q₁ : s₁.mem.readW (VG.Proof.Mont.off base (offset n 3+20)) 32 = BitVec.ofInt 32 q := by
    rw [read32_unch O₁ (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart) (by apart)]
    exact hq
  have r₁ : s₁.mem.readW (VG.Proof.Mont.off base (offset n 3+24)) 32 = BitVec.ofInt 32 r := by
    rw [read32_unch O₁ (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart) (by apart)]
    exact hr
  refine WP.mono (row_ok (r:=1) hs₁ hn hz (by decide) (by simpa using q₁) (by simpa using r₁) hqr
    (by rw [Outs.val32 O₁ (by
          intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
          rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart) (by apart)]; exact hf)
    (by rw [Outs.val32 O₁ (by
          intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
          rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart) (by apart)]; exact hg)
    hfb hgb hp hdivG) fun s₂ ⟨G₂,K₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.copy_ok (n+1) hs₂
    (o:=offset n 4) (a:=offset n 6) (by apart) (by apart) (by apart)) fun s₃ ⟨F₃,K₃,O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.copy_ok (n+1) hs₃
    (o:=offset n 5) (a:=offset n 7) (by apart) (by apart) (by apart)) fun z ⟨G₄,K₄,O₄⟩ => ?_
  refine ⟨?_,?_,((K₁.trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide)),?_⟩
  · rw [O₄.val32 (by apart) (by apart),F₃,Outs.val32 O₂ (by
      intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart) (by apart)]
    exact F₁
  · rw [G₄,O₃.val32 (by apart) (by apart)]
    exact G₂
  · intro x hx
    have hx4 := hx (offset n 4,4*(4*n+8)) (by simp [writes])
    have hx11 := hx (offset n 11,3*(4*n+8)) (by simp [writes])
    rw [O₄ x (by dsimp only at *; apart),O₃ x (by dsimp only at *; apart),
      O₂ x (by
        intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart),
      O₁ x (by
        intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl | rfl <;> dsimp only <;> apart)]

end VG.Proof.Rsa.X86.GcdBatch
