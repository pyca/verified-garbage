import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf

/-! # Applying both matrix rows to the signed divstep values -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT, InvCfg.sU, InvCfg.sW]) <;> omega))

theorem fgUpdate_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat} {T : Divstep.MSt} {f g : Int}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hT : MatrixAt P base T s)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hf : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = f % 2 ^ 288)
    (hg : (val32 s.mem base P.sG 9 : Int) % 2 ^ 288 = g % 2 ^ 288)
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ 256)
    (hdivF : 2 ^ 30 ∣ T.u * f + T.v * g) (hdivG : 2 ^ 30 ∣ T.q * f + T.r * g) :
    WP isa (.block P.fgUpdate) s fun z =>
      (val32 z.mem base P.sF 9 : Int) % 2 ^ 288 = ((T.u * f + T.v * g) / 2 ^ 30) % 2 ^ 288 ∧
      (val32 z.mem base P.sG 9 : Int) % 2 ^ 288 = ((T.q * f + T.r * g) / 2 ^ 30) % 2 ^ 288 ∧
      Keeps clob s z ∧ Outside base P.tbl 288 s.mem z.mem ∧
      val32 z.mem base P.sA 8 = val32 s.mem base P.sA 8 ∧
      val32 z.mem base P.sB 8 = val32 s.mem base P.sB 8 := by
  have hn := hs.nowrap
  have L₁ : LinearLay size (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using fgLayout ht (row := 0) (by decide)
  have L₂ : LinearLay size (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 := by
    simpa only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using fgLayout ht (row := 1) (by decide)
  unfold InvCfg.fgUpdate
  rw [show VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++
      VG.Impl.Weierstrass.X86.Inv.shr30 P.sNF P.sT 9 ++
      VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++
      VG.Impl.Weierstrass.X86.Inv.shr30 P.sNG P.sT 9 =
      (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++
       VG.Impl.Weierstrass.X86.Inv.shr30 P.sNF P.sT 9) ++
      (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++
       VG.Impl.Weierstrass.X86.Inv.shr30 P.sNG P.sT 9) by simp only [List.append_assoc]]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (fHalf_ok hs L₁ (dst := P.sNF) (by apart) (by apart) hT.u hT.v huv hf hg hfb hgb hp hdivF)
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have q₁ : s₁.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q := by
    rw [read32_unch O₁ (by apart) (by apart), hT.q]
  have r₁ : s₁.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r := by
    rw [read32_unch O₁ (by apart) (by apart), hT.r]
  refine WP.mono (fHalf_ok hs₁ L₂ (dst := P.sNG) (by apart) (by apart) q₁ r₁ hqr
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hf)
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hg) hfb hgb hp hdivG)
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (copy_ok 9 hs₂ (o := P.sF) (a := P.sNF) (by apart) (by apart) (by apart))
    fun s₃ ⟨F₃, K₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (copy_ok 9 hs₃ (o := P.sG) (a := P.sNG) (by apart) (by apart) (by apart))
    fun z ⟨G₄, K₄, O₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₄.val32 (by apart) (by apart), F₃, Outs.val32 O₂ (by apart) (by apart)]
    exact F₁
  · rw [G₄, O₃.val32 (by apart) (by apart)]
    exact G₂
  · exact ((K₁.trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · have H₁ : Outside base P.tbl 288 s.mem s₁.mem := O₁.outside (by apart)
    have H₂ : Outside base P.tbl 288 s₁.mem s₂.mem := O₂.outside (by apart)
    exact ((H₁.trans H₂).trans (O₃.mono (by apart) (by apart))).trans (O₄.mono (by apart) (by apart))

  · rw [O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
      Outs.val32 O₂ (by apart) (by apart), Outs.val32 O₁ (by apart) (by apart)]
  · rw [O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
      Outs.val32 O₂ (by apart) (by apart), Outs.val32 O₁ (by apart) (by apart)]

end VG.Proof.Weierstrass.X86.Inv
