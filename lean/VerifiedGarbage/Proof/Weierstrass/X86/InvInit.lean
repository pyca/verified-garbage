import VerifiedGarbage.Proof.Weierstrass.X86.InvInitWords
import VerifiedGarbage.Proof.Weierstrass.X86.InvState

/-! # Initial state of the 256-bit divstep inversion -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

local macro "apart" : tactic => `(tactic|
  ((try simp only [InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sW, InvCfg.sCount]) <;> omega))

theorem init_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat}
    (hs : Scr s base size) (L : InvLay P size) (hm : val32 s.mem base P.M.mo 8 = p) :
    WP isa (.block P.init) s fun z =>
      StateAt P base ⟨1, p, val32 s.mem base P.base 8, 0, 1⟩ z ∧
      w32 z.mem base P.sCount = 20 ∧ Keeps [.eax] s z ∧ Outside base P.tbl 320 s.mem z.mem := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hmod := L.mod_bound; have hbase := L.base_bound
  have htm := L.tbl_mod; have hbt := L.base_tbl
  unfold InvCfg.init
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.mono
    (copyPad_ok hs (dst := P.sF) (src := P.M.mo) (by apart) hmod (by apart))
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_)))))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copyPad_ok hs₁ (dst := P.sG) (src := P.base) (by apart) hbase (by apart))
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (zeros_ok hs₂ (acc := P.sA) (k := 8) (by apart)) fun s₃ ⟨O₃, A₃, K₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (one8_ok hs₃ (dst := P.sB) (by apart)) fun s₄ ⟨B₄, K₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.mono (setWord_ok 1 hs₄ (dst := P.sW) (by apart)) fun s₅ ⟨D₅, K₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  refine WP.mono (setWord_ok 20 hs₅ (dst := P.sCount) (by apart)) fun z ⟨C₆, K₆, O₆⟩ =>
    ⟨?_, C₆, ((((K₁.trans K₂).trans K₃).trans K₄).trans K₅).trans K₆, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 z.mem base P.sW = 1
      rw [O₆.w32 (by apart) (by apart), D₅]
      rfl
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart),
        O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
        O₂.val32 (by apart) (by apart), F₁, hm]
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart),
        O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart), G₂,
        O₁.val32 (by apart) (by apart)]
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart),
        O₄.val32 (by apart) (by apart), A₃]
      rfl
    · rw [O₆.val32 (by apart) (by apart), O₅.val32 (by apart) (by apart), B₄]
      rfl
  · intro x hx
    rw [O₆ x (by apart), O₅ x (by apart), O₄ x (by apart), O₃ x (by apart),
      O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv
