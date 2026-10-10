import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
import VerifiedGarbage.Proof.Weierstrass.X86.InvRed
import VerifiedGarbage.Proof.Weierstrass.X86.InvState

/-! ## `InvCoeff` -/

section

/-! # Updating an inverse coefficient from one divstep matrix row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass VG.Impl.Mont

theorem abHalf_ok {s : State} {base : Addr} {size u v acc a b tmp out k p : Nat}
    {M : Mod} {cu cv x y : Int} (hs : Scr s base size)
    (L : LinearLay size u v acc a b tmp (k + 1) k) (R : RedLay M size acc tmp out (k + 1))
    (hp : 0 < p) (hm : val32 s.mem base M.mo (k + 1) = p)
    (hinv : (p * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hu : s.mem.readW (off base u) 32 = BitVec.ofInt 32 cu)
    (hv : s.mem.readW (off base v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hx : (val32 s.mem base a (k + 1) : Int) = x) (hy : (val32 s.mem base b (k + 1) : Int) = y)
    (hxb : |x| ≤ p) (hyb : |y| ≤ p) :
    WP isa (.block (linear u v acc a b tmp (k + 1) k ++ reduce M acc tmp out)) s fun z =>
      (val32 z.mem base out (k + 1) : Int) = Divstep.W32.mred p (minv32 M).toNat (cu * x + cv * y) ∧
      Keeps wordClob s z ∧
      Unch base [(acc, 4 * (k + 1 + 2)), (tmp, 4 * (k + 1 + 1)),
        (M.tmp, 4 * (k + 1)), (out, 4 * (k + 1))] s.mem z.mem := by
  have hn := hs.nowrap
  have hmod := R.mod_bound; have ham := R.am; have htm := R.tm
  refine WP.block_append (WP.mono (linear_ok hs L) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), hx, hy] at V₁
  have hm₁ : val32 s₁.mem base M.mo (k + 1) = p := by
    rw [Outs.val32 O₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega), hm]
  have bound : |cu * x + cv * y| ≤ 2 ^ 31 * p := by
    have H := Divstep.W32.comb_le huv hxb hyb
    have hp' : (0 : Int) ≤ p := Int.natCast_nonneg _
    omega
  refine WP.mono (reduce_ok (hs.of_keeps K₁ (by decide)) R hp hm₁ hinv bound V₁)
    fun z ⟨O₂, K₂, V₂⟩ => ⟨V₂, (K₁.mono (by decide)).trans K₂, ?_⟩
  intro q hq
  rw [O₂ q hq]
  apply O₁ q
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hq (acc, 4 * (k + 1 + 2)) (by simp)
  · have := hq (tmp, 4 * (k + 1 + 1)) (by simp)
    simp only
    omega

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvLayout` -/

section

/-! # Arithmetic layouts for the two rows of a 256-bit divstep batch -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem read32_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (U : Unch base W m m') {d : Nat}
    (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hb : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  BitVec.eq_of_toNat_eq (word_unch U hd hb)

theorem fgLayout {P : InvCfg} {size row : Nat} (ht : P.tbl + 320 ≤ size) (hr : row ≤ 1) :
    LinearLay size (P.sW + 12 + 8 * row) (P.sW + 16 + 8 * row)
      P.sT P.sF P.sG P.sU 9 7 := by
  constructor <;> (try dsimp only [InvCfg.sW, InvCfg.sT, InvCfg.sF, InvCfg.sG, InvCfg.sU]) <;> omega

theorem abLayout {P : InvCfg} {size row : Nat} (ht : P.tbl + 320 ≤ size) (hr : row ≤ 1) :
    LinearLay size (P.sW + 12 + 8 * row) (P.sW + 16 + 8 * row)
      P.sT P.sA P.sB P.sU 8 7 := by
  constructor <;> (try dsimp only [InvCfg.sW, InvCfg.sT, InvCfg.sA, InvCfg.sB, InvCfg.sU]) <;> omega

theorem redLayout {P : InvCfg} {size out : Nat} (L : WorkLay P size) (ho : out = P.sNF ∨ out = P.sB) :
    RedLay P.M size P.sT P.sU out 8 := by
  have ht := L.tbl_bound; have hm := L.mod_bound; have htmp := L.tmp_bound
  have htm := L.tbl_mod; have htt := L.tbl_tmp; have hmt := L.mod_tmp
  constructor
  · simp only [VG.Impl.Mont.X86.words, L.n4]
  · decide
  all_goals rcases ho with rfl | rfl <;>
    (try dsimp only [InvCfg.sT, InvCfg.sU, InvCfg.sNF, InvCfg.sB]) <;> omega

end VG.Proof.Weierstrass.X86.Inv

end
