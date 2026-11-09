module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed
public import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words
import VerifiedGarbage.Proof.Mont.AArch64.RowInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256DR
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256ED
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowNeg
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

local macro "jslots" : tactic => `(tactic| plain_simp_names first
  | (simp (config := { contextual := true }) only [jointSlots, jointLive, jointWork, jacWinSlots, nafLive,
      winRo, winOther, rcbW, rcbR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
      or_true, and_true, implies_true, and_self, forall_eq_or_imp, forall_eq, eq_self_iff_true,
      List.forall_mem_append, List.forall_mem_cons]; done)
  | (intro x hx; simp only [jointSlots,jointLive,jointWork,
                   jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

end VG.Proof.Weierstrass.AArch64
