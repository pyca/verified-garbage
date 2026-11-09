module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntryTiming
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
public import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedTiming
public import VerifiedGarbage.Proof.Weierstrass.CombLay
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

local macro "jslots" : tactic => `(tactic| plain_simp_names (simp only [jointSlots,jointLive,jointWork,
                   jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

end VG.Proof.Weierstrass.AArch64
