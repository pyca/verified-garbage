import VerifiedGarbage.Proof.Weierstrass.X86.InvFg
import VerifiedGarbage.Proof.Weierstrass.X86.InvAb
import VerifiedGarbage.Proof.Weierstrass.X86.InvCount

/-! # A complete thirty-step inversion batch -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sW, InvCfg.sCount]) <;> omega))

theorem batch_ok {P : InvCfg} {s : State} {base : Addr} {size p j : Nat} {I : Divstep.W32.IState}
    (hs : Scr s base size) (L : WorkLay P size) (hI : StateAt P base I s)
    (hd : |I.d| + 64 < 2 ^ 30) (hf : I.f % 2 = 1)
    (hfb : |I.f| ≤ p) (hgb : |I.g| ≤ p) (hab : |I.a| ≤ p) (hbb : |I.b| ≤ p)
    (hp : 0 < p) (hp256 : p < 2 ^ 256) (hm : val32 s.mem base P.M.mo 8 = p)
    (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (hj : 1 ≤ j) (hj32 : j < 2 ^ 32) (hc : w32 s.mem base P.sCount = j)
    (hbound : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
      |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30)
    (hdiv : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
      2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g) :
    WP isa P.batch s fun z =>
      StateAt P base (Divstep.W32.batch 30 p (minv32 P.M).toNat I) z ∧
      w32 z.mem base P.sCount = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem z.mem := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hmod := L.mod_bound; have htmp := L.tmp_bound
  have htm := L.tbl_mod; have htt := L.tbl_tmp
  let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
  change |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30 at hbound
  change 2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g at hdiv
  unfold InvCfg.batch
  refine WP.seq (WP.mono (words_ok hs ht hI hd hf) fun s₁ ⟨Mat₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.block_append (WP.block_append (WP.mono
    (fgUpdate_ok hs₁ ht Mat₁ hbound.1 hbound.2
      (by rw [O₁.val32 (by apart) (by apart)]; exact hI.f)
      (by rw [O₁.val32 (by apart) (by apart)]; exact hI.g) hfb hgb hp256 hdiv.1 hdiv.2)
    fun s₂ ⟨F₂, G₂, K₂, O₂, A₂, B₂⟩ => ?_))
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have Mat₂ : MatrixAt P base T s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.d
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.u
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.v
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.q
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.r
  refine WP.mono (abUpdate_ok hs₂ L Mat₂ hbound.1 hbound.2 hp
    (by rw [O₂.val32 (by apart) (by apart), O₁.val32 (by apart) (by apart), hm]) hinv
    (by rw [A₂, O₁.val32 (by apart) (by apart)]; exact hI.a)
    (by rw [B₂, O₁.val32 (by apart) (by apart)]; exact hI.b) hab hbb)
    fun s₃ ⟨A₃, B₃, K₃, O₃, F₃, G₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  have Count : w32 s₃.mem base P.sCount = j := by
    rw [word_unch O₃ (by apart) (by apart), O₂.w32 (by apart) (by apart),
      O₁.w32 (by apart) (by apart), hc]
  refine WP.mono (batchEnd_ok hs₃ ht hj hj32 Count) fun z ⟨C₄, Z₄, K₄, O₄⟩ =>
    ⟨?_, C₄, Z₄, ((K₁.trans (K₂.mono (by decide))).trans K₃).trans (K₄.mono (by decide)), ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [read32_unch O₄.unch (by apart) (by apart), read32_unch O₃ (by apart) (by apart)]
      rw [Divstep.W32.batch_d]
      exact Mat₂.d
    · rw [O₄.val32 (by apart) (by apart), F₃]
      exact F₂
    · rw [O₄.val32 (by apart) (by apart), G₃]
      exact G₂
    · rw [O₄.val32 (by apart) (by apart)]
      rw [Divstep.W32.batch_a]
      exact A₃
    · rw [O₄.val32 (by apart) (by apart)]
      rw [Divstep.W32.batch_b]
      exact B₃
  · intro x hx
    have ht' := hx (P.tbl, 320) (by simp)
    have hm' := hx (P.M.tmp, 32) (by simp)
    rw [O₄ x (by apart), O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv
