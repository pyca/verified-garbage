import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout

/-! # Applying both matrix rows to the reduced inverse coefficients -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sT, InvCfg.sU, InvCfg.sW]) <;> omega))

theorem abUpdate_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat} {T : Divstep.MSt} {a b : Int}
    (hs : Scr s base size) (L : WorkLay P size) (hT : MatrixAt P base T s)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hp : 0 < p) (hm : val32 s.mem base P.M.mo 8 = p)
    (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (ha : (val32 s.mem base P.sA 8 : Int) = a) (hb : (val32 s.mem base P.sB 8 : Int) = b)
    (hab : |a| ≤ p) (hbb : |b| ≤ p) :
    WP isa (.block P.abUpdate) s fun z =>
      (val32 z.mem base P.sA 8 : Int) = Divstep.W32.mred p (minv32 P.M).toNat (T.u * a + T.v * b) ∧
      (val32 z.mem base P.sB 8 : Int) = Divstep.W32.mred p (minv32 P.M).toNat (T.q * a + T.r * b) ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 288), (P.M.tmp, 32)] s.mem z.mem ∧
      val32 z.mem base P.sF 9 = val32 s.mem base P.sF 9 ∧
      val32 z.mem base P.sG 9 = val32 s.mem base P.sG 9 := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hmod := L.mod_bound; have htmp := L.tmp_bound
  have htm := L.tbl_mod; have htt := L.tbl_tmp; have hmt := L.mod_tmp
  have L₁ : LinearLay size (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using abLayout ht (row := 0) (by decide)
  have L₂ : LinearLay size (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7 := by
    simpa only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using abLayout ht (row := 1) (by decide)
  unfold InvCfg.abUpdate
  rw [List.append_assoc
    (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 ++
      VG.Impl.Weierstrass.X86.Inv.reduce P.M P.sT P.sU P.sNF)
    (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7)]
  refine WP.block_append (WP.block_append (WP.mono
    (abHalf_ok hs L₁ (redLayout L (.inl rfl)) hp hm hinv hT.u hT.v huv ha hb hab hbb)
    fun s₁ ⟨A₁, K₁, O₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  have q₁ : s₁.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q := by
    rw [read32_unch O₁ (by apart) (by apart), hT.q]
  have r₁ : s₁.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r := by
    rw [read32_unch O₁ (by apart) (by apart), hT.r]
  refine WP.mono (abHalf_ok hs₁ L₂ (redLayout L (.inr rfl)) hp
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hm) hinv q₁ r₁ hqr
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact ha)
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hb) hab hbb)
    fun s₂ ⟨B₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (copy_ok 8 hs₂ (o := P.sA) (a := P.sNF) (by apart) (by apart) (by apart))
    fun z ⟨A₃, K₃, O₃⟩ => ⟨?_, ?_, (K₁.trans K₂).trans (K₃.mono (by decide)), ?_, ?_, ?_⟩
  · rw [A₃, Outs.val32 O₂ (by apart) (by apart)]
    exact A₁
  · rw [O₃.val32 (by apart) (by apart)]
    exact B₂
  · intro x hx
    have ht' := hx (P.tbl, 288) (by simp)
    have hm' := hx (P.M.tmp, 32) (by simp)
    rw [O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

  · rw [O₃.val32 (by apart) (by apart), Outs.val32 O₂ (by apart) (by apart),
      Outs.val32 O₁ (by apart) (by apart)]
  · rw [O₃.val32 (by apart) (by apart), Outs.val32 O₂ (by apart) (by apart),
      Outs.val32 O₁ (by apart) (by apart)]

end VG.Proof.Weierstrass.X86.Inv
