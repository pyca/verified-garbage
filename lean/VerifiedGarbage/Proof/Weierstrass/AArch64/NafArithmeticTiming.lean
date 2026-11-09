module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
local macro "jmem" : tactic => `(tactic| plain_simp_names simp only [jacCoords,nafLive,jacWinSlots,jacWinWrites,
                   winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

end VG.Proof.Weierstrass.AArch64
