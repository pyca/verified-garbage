module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntry
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafEntry
import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Mont.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

local macro "jmem" : tactic => `(tactic| plain_simp_names simp only [nafLive,jacWinSlots,jacWinWrites,
                   winRo,winOther,rcbR,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,true_or,or_true])

end VG.Proof.Weierstrass.AArch64
