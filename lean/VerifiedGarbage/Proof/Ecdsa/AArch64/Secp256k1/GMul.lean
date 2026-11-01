module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.MulFn
import VerifiedGarbage.Proof.Weierstrass.AArch64.Secp256k1Literals
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Weierstrass.CombLay

/-! # secp256k1 multiplication by the base point, by a call of `vg_secp256k1_mul` -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.Secp256k1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem ladLayM : LadLay secp256k1.mulLadder size := by
  constructor
  · refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
    have h : ∀ x ∈ ladSlots secp256k1.mulLadder, ∀ y ∈ ladSlots secp256k1.mulLadder,
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

theorem ladAM : LadA secp256k1.mulLadder where
  sl := by decide +kernel
  mod := ⟨sl_mod8 secp256k1 MP, by decide⟩
  bits := by decide
  call := by intro f m h; cases h

theorem mulFn_v : secp256k1.mulFn.allInstrs (fun i => (vdstOf i).isNone) = true := by lit_decide

theorem mulFn_nf : secp256k1.mulFn.noFrames = true := by lit_decide

/-- What a multiplication by a call of `vg_secp256k1_mul` writes. -/
abbrev gW : List (Nat × Nat) := slW secp256k1 [BM] ++ mulWF secp256k1

theorem gMul_ok (hc : BaseCfgOk secp256k1) (hC : Law secp256k1.C)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed secp256k1 base g s.mem) :
    WP isa gMul s fun s' => KeepRegs (powClob 4) s s' ∧ Unch base gW s.mem s'.mem ∧
      Fixed secp256k1 base g s'.mem ∧ ModOkA secp256k1.MP' size secp256k1.C.p s'.mem base ∧
      (∀ x ∈ [secp256k1.sl RX, secp256k1.sl RY, secp256k1.sl RZ], wordsVal s'.mem base x 4 < secp256k1.C.p) ∧
      Rep secp256k1.C (tmv secp256k1.C 4 base s' (secp256k1.sl RX))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RY))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RZ)) (mul (sv secp256k1 base s K) (G secp256k1.C)) := by
  have hp3 := hc.p_ge
  have hmont : ∀ x, secp256k1.mont x < secp256k1.C.p := fun x => Nat.mod_lt _ (by omega)
  have eG : (Point.affine (tmv secp256k1.C secp256k1.n base s (secp256k1.sl GX)) (tmv secp256k1.C secp256k1.n base s (secp256k1.sl GY)) :
      Point secp256k1.C) = G secp256k1.C := by
    show Point.affine (toM _ _ (wordsVal s.mem base (secp256k1.sl GX) secp256k1.n))
      (toM _ _ (wordsVal s.mem base (secp256k1.sl GY) secp256k1.n)) = Point.affine _ _
    rw [F.gx, F.gy, toM_cmont hc, toM_cmont hc]
  have W := mulAt_ok hc (.inl rfl) (.inl (by decide)) ladLayM ladAM hC mulFn_v mulFn_nf
    (name := "vg_secp256k1_mul") (px := GX) (py := GY) (by decide) (by decide)
    (by decide) (by decide) (by decide) hs F (lt_of_eq_of_lt F.gx (hmont _))
    (lt_of_eq_of_lt F.gy (hmont _)) (by rw [eG]; exact hc.onG)
  rw [eG] at W
  exact W

end VG.Proof.Ecdsa.AArch64.Secp256k1
