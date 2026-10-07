import VerifiedGarbage.Proof.Weierstrass.X86.InvState
import VerifiedGarbage.Proof.Weierstrass.X86.InvCoeff

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
