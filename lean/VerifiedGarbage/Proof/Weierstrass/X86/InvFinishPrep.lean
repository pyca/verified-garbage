module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Weierstrass.X86.MontBody
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.State

/-! ### `Weierstrass.X86.InvState`, which this module and modules that import it used -/

section

/-! # Memory layout and state of the 256-bit divstep inversion -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure WorkLay (P : InvCfg) (size : Nat) : Prop where
  n4 : P.M.n = 4
  tbl_bound : P.tbl + 320 ≤ size
  mod_bound : P.M.mo + 32 ≤ size
  tmp_bound : P.M.tmp + 32 ≤ size
  tbl_mod : P.tbl + 320 ≤ P.M.mo ∨ P.M.mo + 32 ≤ P.tbl
  tbl_tmp : P.tbl + 320 ≤ P.M.tmp ∨ P.M.tmp + 32 ≤ P.tbl
  mod_tmp : P.M.mo + 32 ≤ P.M.tmp ∨ P.M.tmp + 32 ≤ P.M.mo

structure InvLay (P : InvCfg) (size : Nat) : Prop extends WorkLay P size where
  base_bound : P.base + 32 ≤ size
  base_tbl : P.base + 32 ≤ P.tbl ∨ P.tbl + 320 ≤ P.base
  out_bound : P.out + 32 ≤ size
  out_tmp : P.out + 32 ≤ P.M.tmp ∨ P.M.tmp + 32 ≤ P.out
  size_eq : size = 8192
  tbl_own : P.tbl + 320 ≤ Mont.own 4
  out_own : P.out + 32 ≤ Mont.own 4

structure StateAt (P : InvCfg) (base : Addr) (I : Divstep.W32.IState) (s : State) : Prop where
  d : s.mem.readW (off base P.sW) 32 = BitVec.ofInt 32 I.d
  f : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = I.f % 2 ^ 288
  g : (val32 s.mem base P.sG 9 : Int) % 2 ^ 288 = I.g % 2 ^ 288
  a : (val32 s.mem base P.sA 8 : Int) = I.a
  b : (val32 s.mem base P.sB 8 : Int) = I.b

structure MatrixAt (P : InvCfg) (base : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (off base P.sW) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (off base (P.sW + 12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (off base (P.sW + 16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r

/-- The mathematical bounds and exact divisions required by one batch. -/
structure BatchFacts (I : Divstep.W32.IState) (p : Nat) : Prop where
  delta : |I.d| + 64 < 2 ^ 30
  odd : I.f % 2 = 1
  f : |I.f| ≤ p
  g : |I.g| ≤ p
  a : |I.a| ≤ p
  b : |I.b| ≤ p
  matrix : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
    |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30
  division : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
    2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g

end VG.Proof.Weierstrass.X86.Inv

end

end

/-! # Selecting the final Montgomery correction from the sign of f -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [InvCfg.sF, InvCfg.sNF, InvCfg.sNG]) <;> omega))

theorem finishPrep_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size)
    (hC : P.C < 2 ^ 256) (hCn : P.Cn < 2 ^ 256) :
    WP isa (.block (setConst 4 P.sNF P.C ++ setConst 4 P.sNG P.Cn ++
      VG.Impl.Weierstrass.X86.Inv.maskOf P.sF ++ sel 8 P.sNF P.sNF P.sNG)) s fun z =>
      val32 z.mem base P.sNF 8 = (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) ∧
      Keeps clob s z ∧ Outside base P.sNF 68 s.mem z.mem := by
  have hn := hs.nowrap
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (setConst_ok hs (o := P.sNF) (by apart) hC) fun s₁ ⟨C₁, K₁, O₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (setConst_ok hs₁ (o := P.sNG) (by apart) hCn) fun s₂ ⟨C₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (maskOf_ok hs₂ (coefficient := P.sF) (by apart)) fun s₃ ⟨C₃, K₃, M₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  rw [O₂.w32 (by apart) (by apart), O₁.w32 (by apart) (by apart)] at C₃
  refine WP.mono (sel_ok (decide (2 ^ 31 ≤ w32 s.mem base P.sF)) 8 hs₃
    (by simpa only [decide_eq_true_eq] using C₃) (o := P.sNF) (a := P.sNF) (b := P.sNG)
    (by apart) (by apart) (by apart) (by apart) (by apart)) fun z ⟨V, K₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · rw [wordsVal_eq_val32] at C₁ C₂
    rw [V, M₃, C₂, O₂.val32 (by apart) (by apart), C₁]
    simp only [decide_eq_true_eq]
  · exact (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
      (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · intro x hx
    simp only [InvCfg.sNF] at hx
    rw [O₄ x (by apart), M₃, O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv
