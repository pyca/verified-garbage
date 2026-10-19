module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.MulFn
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words
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
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Mont.AArch64.RowInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.Pow

/-! # brainpoolP384r1 multiplication by the base point, by a call of `vg_brainpoolp384r1_mul` -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP384r1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP384r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem ladLayM : LadLay brainpoolp384r1.mulLadder size := by
  constructor
  · refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
    have h : ∀ x ∈ ladSlots brainpoolp384r1.mulLadder, ∀ y ∈ ladSlots brainpoolp384r1.mulLadder,
        x ≠ y → x + 48 ≤ y ∨ y + 48 ≤ x := by decide +kernel
    exact fun x y hx hy => h x hx y hy
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide
  · decide
  · decide +kernel

theorem ladAM : LadA brainpoolp384r1.mulLadder where
  sl := by decide +kernel
  mod := ⟨sl_mod8 brainpoolp384r1 MP, by decide⟩
  bits := by decide
  call := by intro f m h; cases h

theorem mulFn_v : brainpoolp384r1.mulFn.allInstrs (fun i => (vdstOf i).isNone) = true := by lit_decide

theorem mulFn_nf : brainpoolp384r1.mulFn.noFrames = true := by lit_decide

/-- What a multiplication by a call of `vg_brainpoolp384r1_mul` writes. -/
abbrev gW : List (Nat × Nat) := slW brainpoolp384r1 [BM] ++ mulWF brainpoolp384r1

theorem gMul_ok (hc : BaseCfgOk brainpoolp384r1) (hC : Law brainpoolp384r1.C)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed brainpoolp384r1 base g s.mem) :
    WP isa gMul s fun s' => KeepRegs (powClob 6) s s' ∧ Unch base gW s.mem s'.mem ∧
      Fixed brainpoolp384r1 base g s'.mem ∧ ModOkA brainpoolp384r1.MP' size brainpoolp384r1.C.p s'.mem base ∧
      (∀ x ∈ [brainpoolp384r1.sl RX, brainpoolp384r1.sl RY, brainpoolp384r1.sl RZ], wordsVal s'.mem base x brainpoolp384r1.n < brainpoolp384r1.C.p) ∧
      Rep brainpoolp384r1.C (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RX))
        (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RY))
        (tmv brainpoolp384r1.C brainpoolp384r1.n base s' (brainpoolp384r1.sl RZ)) (mul (sv brainpoolp384r1 base s K) (G brainpoolp384r1.C)) := by
  have hp3 := hc.p_ge
  have hmont : ∀ x, brainpoolp384r1.mont x < brainpoolp384r1.C.p := fun x => Nat.mod_lt _ (by omega)
  have eG : (Point.affine (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl GX)) (tmv brainpoolp384r1.C brainpoolp384r1.n base s (brainpoolp384r1.sl GY)) :
      Point brainpoolp384r1.C) = G brainpoolp384r1.C := by
    show Point.affine (toM _ _ (wordsVal s.mem base (brainpoolp384r1.sl GX) brainpoolp384r1.n))
      (toM _ _ (wordsVal s.mem base (brainpoolp384r1.sl GY) brainpoolp384r1.n)) = Point.affine _ _
    rw [F.gx, F.gy, toM_cmont hc, toM_cmont hc]
  have W := mulAt_ok hc (.inr (.inl rfl)) (.inr (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := Spec.Weierstrass.Mul.brainpoolp384r1.mulApi.name) (px := GX) (py := GY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs F (lt_of_eq_of_lt F.gx (hmont _))
    (lt_of_eq_of_lt F.gy (hmont _)) (by rw [eG]; exact hc.onG)
  rw [eG] at W
  exact W

end VG.Proof.Ecdsa.AArch64.BrainpoolP384r1
