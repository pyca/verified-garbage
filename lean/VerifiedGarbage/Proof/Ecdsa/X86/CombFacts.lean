import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Comb7Shape
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords

/-! # P-256 comb configuration and immutable table size -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256Comb_ok (hI : Weierstrass.X86.Inv.InvSounds) : CfgOk p256Comb := by
  rcases p256_ok hI with ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

theorem p256Comb_shape : CombOk p256Comb p256d := ⟨by decide, by decide, by decide⟩

theorem p256Comb_am3 : AM3 p256Comb.C := by unfold AM3; decide +kernel

theorem p256Comb_tables (hL : Law p256Comb.C) : CombTbls p256Comb := by
  intro d hd
  have he : p256d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.P256.combOk7 hL, Proof.P256.booth hL⟩

abbrev p256W : List (BitVec 64) := p256Comb.combWords p256d

theorem p256Comb_consts : p256Comb.combConsts = [("VG_P256_COMB", p256W)] := rfl

theorem p256W_length : p256W.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := p256Comb.n) (R := p256Comb.R) (p := p256Comb.C.p)
    (H := 64) (tbl := Impl.P256.p256Comb7) Proof.P256.p256Comb7_length Proof.P256.p256Comb7_rows).trans rfl

end VG.Proof.Ecdsa.X86
