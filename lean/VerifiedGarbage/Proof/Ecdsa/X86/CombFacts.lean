module
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays

import VerifiedGarbage.Proof.Ecdsa.X86.GMul
import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Comb7Shape
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.X86.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore

/-! # P-256 comb configuration and immutable table size -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256Comb_ok (hI : Weierstrass.X86.Inv.InvSounds) : CfgOk p256Comb := by
  rcases p256_ok hI with ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t⟩

/-- No instruction of the comb signature writes `esp`, and its calls use 24
bytes of stack. -/
theorem signComb_sp : X86.SpOk signP256Comb p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem signComb_spMul : X86.SpOk (p256Comb.signWithMul p256Comb.gMul) 24 :=
  X86.SpOk.right (a := p256Comb.tableAddr) signComb_sp

theorem signComb_spG : X86.SpOk p256Comb.gMul 24 :=
  X86.SpOk.left (X86.SpOk.right (a := p256Comb.signPrep) signComb_spMul)

theorem signComb_spTail : X86.SpOk p256Comb.signTail p256Comb.stk :=
  X86.SpOk.right (X86.SpOk.right (a := p256Comb.signPrep) signComb_spMul)

theorem p256Comb_shape : CombOk p256Comb p256d :=
  ⟨by decide, by decide, fun _ => by decide, fun h => absurd h (by decide)⟩

theorem p256Comb_am3 : AM3 p256Comb.C := by unfold AM3; decide +kernel

theorem p256Comb_tables (hL : Law p256Comb.C) : CombTbls p256Comb := by
  intro d hd
  have he : p256d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.P256.combOk7 hL, fun _ => ⟨Proof.P256.booth hL, p256Comb_am3⟩⟩

abbrev p256W : List (BitVec 64) := p256Comb.combWords p256d

theorem p256Comb_consts : p256Comb.combConsts = [("VG_P256_COMB", p256W)] := rfl

theorem p256W_length : p256W.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := p256Comb.n) (R := p256Comb.R) (p := p256Comb.C.p)
    (H := 64) (tbl := Impl.P256.p256Comb7) Proof.P256.p256Comb7_length Proof.P256.p256Comb7_rows).trans rfl

/-- The constant time of P-256's comb, as the stages take it. -/
theorem p256Comb_gMul (hL : Law p256Comb.C) (hI : Weierstrass.X86.Inv.InvSounds) {scratchSecond : Bool} :
    GMulRel p256Comb p256d scratchSecond := by
  refine GMulRel.of_body (d := p256d) (p256Comb_ok hI) rfl ?_
  intro base g₁ g₂ s₀ t₀ k₁ k₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
  exact gMul_rel (p256Comb_ok hI) hL (p256Comb_tables hL) p256Comb_shape h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 h18 h19 h20

/-- The taint checks of the stages of P-256's signature. -/
theorem p256SignCT : SignStagesCT p256Comb := ⟨signPrep_rel, signTail_rel⟩

end VG.Proof.Ecdsa.X86
