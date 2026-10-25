module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowCore
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words
public import VerifiedGarbage.Proof.Mont.AArch64.RowInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256DR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256ED
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFive
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowStore
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
public import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombPublic
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
public import VerifiedGarbage.Proof.Weierstrass.JacMul
public import VerifiedGarbage.Spec.Weierstrass.Mul
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombPublic
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Spec.Weierstrass.Mul

/-! A signed public lookup into the Jacobian window table. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| plain_simp_names simp only [jacLive,jacWinSlots,jacWinWrites,
                   winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

/-- Select and sign a nonzero public digit, retaining the accumulator. -/
theorem jacSignedEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k e j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n)))
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096) (hj : j<52)
    {P : Point C} {s : State} (h : JacCore K C base size P k e s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (h2 : s.gpr .x2=BitVec.ofNat 64 (magH 16 (Window5.nib k j)))
    (hnz : magH 16 (Window5.nib k j) ≠ 0) :
    WP isa (.block (Jacobian.publicEntry K ++ negYW K.M 5 K.neg K.zero K.E.y K.bits)) s fun t =>
      ProgKeep K.M base (winOther K) s t ∧ JacCore K C base size P k e t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) (Window5.winPt C P k j) := by
  let a := magH 16 (Window5.nib k j)
  have ha : 1≤a := by dsimp [a]; omega_arith
  have h16 : a≤16 := magH_le (by
    have hl : Window5.nib k j<32 := Nat.mod_lt _ (by decide)
    exact hl)
  have hn := h.field.scr.nowrap
  have hD : ∀ x ∈ [K.E.x,K.E.y,K.E.z], x ∈ jacWinSlots K := by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem
  have hT : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      x ∈ jacLive K := by
    intro x hx
    have he := jacTblPt_mem K ha h16 x hx
    apply List.mem_append_right
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact jacTbl_mem K ha h16 (c := 0) (by decide)
    · exact jacTbl_mem K ha h16 (c := 1) (by decide)
    · exact jacTbl_mem K ha h16 (c := 2) (by decide)
  have hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x := by
    have hx := hL.tbl K.E.x (by jmem)
    have hy := hL.tbl K.E.y (by jmem)
    have hz := hL.tbl K.E.z (by jmem)
    rw [hL.exy] at hy
    rw [hL.exz] at hz
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (jacPublicPoint_ok hL.lay hAl hL.n hL.exy hL.exz h.field h2 ha hTbl
    hD hT hap (h.stable.table a ha h16)) fun s₁ ⟨k₁,i₁,j₁⟩ => ?_
  have ks₁ : ProgKeep K.M base (winOther K) s s₁ := k₁.mono (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem)
  have hs₁ := h.stable.keep hL hJ hn ks₁.unch
  have hnd := hL.nodup
  simp only [winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hnd
  have hny : K.neg≠K.E.y := by grind
  have heLive : ∀ x ∈ [K.E.x,K.E.y,K.E.z], x ∈ jacLive K := by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jmem
  have i₁' := i₁.sub (fun x (hx : x ∈ jacLive K) => List.mem_append_right _ hx)
  have hzero : tmv C K.M.n base s₁ K.zero=0 := by
    unfold tmv; rw [hs₁.zero,toM_zero]
  have hbn := hL.bits_w K.neg (by jmem)
  have hbt := hL.bits_tmp
  have hbn' : K.bits+260 ≤ K.neg ∨ K.neg+8*K.M.n ≤ K.bits := by rw [hL.n]; exact hbn
  have hbt' : K.bits+260 ≤ K.M.tmp ∨ K.M.tmp+8*K.M.n ≤ K.bits := by rw [hL.n]; exact hbt
  have h19' : s₁.gpr .x19=BitVec.ofNat 64 j := by rw [k₁.gpr _ (x19_not_clob _),h19]
  refine WP.mono (negFieldWindow_ok hL.lay hAl hm i₁' (by jmem) (by jmem) (by jmem)
    hny hzero (by decide) (by decide) (by omega_arith) hL.bits (by omega_arith) h19' hs₁.bits hbn' hbt')
    fun t ⟨k₂,i₂⟩ => ?_
  have ks₂ : ProgKeep K.M base (winOther K) s₁ t := k₂.mono (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> jmem)
  have kp := ks₁.trans ks₂
  have i₂' := i₂.sub (fun x (hx : x ∈ jacLive K) => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have rr : InvJ C (tmv C K.M.n base t K.R.x) (tmv C K.M.n base t K.R.y)
      (tmv C K.M.n base t K.R.z) (mul e P) := by
    have pr := point_of_unch hL hn k₁ (p := K.R) (by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jmem) (by
      intro x hx y hy
      apply hL.lay.apart x y
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl <;> jmem
      · exact hD y hy
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
        grind) h.point
    apply point_of_unch hL hn k₂ (p := K.R) _ _ pr
    · intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jmem
    · intro x hx y hy
      apply hL.lay.apart x y
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl <;> jmem
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
        rcases hy with rfl | rfl <;> jmem
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
        grind
  refine ⟨kp,⟨i₂'.to_tmv,h.stable.keep hL hJ hn kp.unch,rr⟩,?_⟩
  apply i₂'.point_tmv heLive
  have hxyn : K.E.x≠K.E.y ∧ K.E.x≠K.neg ∧ K.E.z≠K.E.y ∧ K.E.z≠K.neg := by grind
  simp only [Function.update_self,Function.update_of_ne hxyn.1,Function.update_of_ne hxyn.2.1,
    Function.update_of_ne hxyn.2.2.1,Function.update_of_ne hxyn.2.2.2]
  rw [Window5.combWin_five,Window5.winPt_mag]
  split
  · exact j₁.negY
  · exact j₁

end VG.Proof.Weierstrass.AArch64
