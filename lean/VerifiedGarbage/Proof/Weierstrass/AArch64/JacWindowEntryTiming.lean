module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowEntry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| plain_simp_names simp only [jacLive,jacWinSlots,jacWinWrites,
                   winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

end VG.Proof.Weierstrass.AArch64
