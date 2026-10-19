module
public import VerifiedGarbage.Proof.Ecdsa.X86.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT

import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Comb7Shape
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold

/-! # P-256 comb configuration and immutable table size -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256Comb_ok (hI : Weierstrass.X86.Inv.InvSounds) : CfgOk p256Comb := by
  rcases p256_ok hI with ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t⟩

/-- No instruction of the comb signature writes `esp`, and its calls use 20
bytes of stack. -/
theorem signComb_sp : X86.SpOk signP256Comb p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem signComb_spMul : X86.SpOk (p256Comb.signWithMul p256Comb.gMul) 20 :=
  X86.SpOk.right (a := p256Comb.tableAddr) signComb_sp

theorem signComb_spG : X86.SpOk p256Comb.gMul 20 :=
  X86.SpOk.left (X86.SpOk.right (a := p256Comb.signPrep) signComb_spMul)

theorem signComb_spTail : X86.SpOk p256Comb.signTail p256Comb.stk :=
  X86.SpOk.right (X86.SpOk.right (a := p256Comb.signPrep) signComb_spMul)

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
