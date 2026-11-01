module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.MulFn
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Weierstrass.CombLay

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
    (name := "vg_brainpoolp384r1_mul") (px := GX) (py := GY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs F (lt_of_eq_of_lt F.gx (hmont _))
    (lt_of_eq_of_lt F.gy (hmont _)) (by rw [eG]; exact hc.onG)
  rw [eG] at W
  exact W

end VG.Proof.Ecdsa.AArch64.BrainpoolP384r1
