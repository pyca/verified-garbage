module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.CombLay
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.TCB.AArch64.Isa

/-! A signed public lookup into the Jacobian window table. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| plain_simp_names simp only [jacLive,jacWinSlots,jacWinWrites,
                   winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

end VG.Proof.Weierstrass.AArch64
