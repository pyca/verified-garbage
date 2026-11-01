module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.MulFn
import VerifiedGarbage.Proof.Weierstrass.AArch64.P192Literals
public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Weierstrass.CombLay

/-! # p192 multiplication by the base point, by a call of `vg_p192_mul` -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P192

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.P192
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem ladLayM : LadLay p192.mulLadder size := by
  constructor
  · refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
    have h : ∀ x ∈ ladSlots p192.mulLadder, ∀ y ∈ ladSlots p192.mulLadder,
        x ≠ y → x + 32 ≤ y ∨ y + 32 ≤ x := by decide +kernel
    exact fun x y hx hy => h x hx y hy
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide
  · decide
  · decide +kernel

theorem ladAM : LadA p192.mulLadder where
  sl := by decide +kernel
  mod := ⟨sl_mod8 p192 MP, by decide⟩
  bits := by decide
  call := by intro f m h; cases h

theorem mulFn_v : p192.mulFn.allInstrs (fun i => (vdstOf i).isNone) = true := by lit_decide

theorem mulFn_nf : p192.mulFn.noFrames = true := by lit_decide

/-- What a multiplication by a call of `vg_p192_mul` writes. -/
abbrev gW : List (Nat × Nat) := slW p192 [BM] ++ mulWF p192

theorem gMul_ok (hc : BaseCfgOk p192) (hC : Law p192.C)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed p192 base g s.mem) :
    WP isa gMul s fun s' => KeepRegs (powClob 4) s s' ∧ Unch base gW s.mem s'.mem ∧
      Fixed p192 base g s'.mem ∧ ModOkA p192.MP' size p192.C.p s'.mem base ∧
      (∀ x ∈ [p192.sl RX, p192.sl RY, p192.sl RZ], wordsVal s'.mem base x 4 < p192.C.p) ∧
      Rep p192.C (tmv p192.C 4 base s' (p192.sl RX))
        (tmv p192.C 4 base s' (p192.sl RY))
        (tmv p192.C 4 base s' (p192.sl RZ)) (mul (sv p192 base s K) (G p192.C)) := by
  have hp3 := hc.p_ge
  have hmont : ∀ x, p192.mont x < p192.C.p := fun x => Nat.mod_lt _ (by omega)
  have eG : (Point.affine (tmv p192.C p192.n base s (p192.sl GX)) (tmv p192.C p192.n base s (p192.sl GY)) :
      Point p192.C) = G p192.C := by
    show Point.affine (toM _ _ (wordsVal s.mem base (p192.sl GX) p192.n))
      (toM _ _ (wordsVal s.mem base (p192.sl GY) p192.n)) = Point.affine _ _
    rw [F.gx, F.gy, toM_cmont hc, toM_cmont hc]
  have W := mulAt_ok hc (.inl rfl) (.inl (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := "vg_p192_mul") (px := GX) (py := GY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs F (lt_of_eq_of_lt F.gx (hmont _))
    (lt_of_eq_of_lt F.gy (hmont _)) (by rw [eG]; exact hc.onG)
  rw [eG] at W
  exact W

end VG.Proof.Ecdsa.AArch64.P192
