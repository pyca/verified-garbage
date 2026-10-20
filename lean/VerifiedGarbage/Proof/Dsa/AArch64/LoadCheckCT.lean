module

import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInitCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInitCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Checks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Loading a checked operand and returning its secret mask -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def LoadedCheck (p : BPub) (s : State) : Prop := ∃ minv,
  SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧ p.x.wx < 2 ^ 31

theorem loadCheck_ct : RelCT isa (Two (LPre aX arg argLen)) (Arithmetic.load aX arg argLen)
    (Two LoadedCheck) := by
  refine two_post (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) ?_
  intro p s ⟨minv, bs, hc, hw2, hwx, hw30, ha, hp', hl', hp, hl, hlen, hs, h1, h31, hfit⟩
  exact WP.mono (load_ok hc hw2 hwx hw30 ha hp' hl' hp hl hs h1 h31 hfit)
    fun t ⟨ht, _⟩ => ⟨minv, ht, hw2, by omega⟩

theorem loadedRange_trace (aboveOne : Bool) : RelCT isa (Two LoadedCheck)
    (Checks.rangeMask aboveOne) (fun _ _ => True) := by
  exact two_map (fun p : BPub => ⟨off p.x.B p.x.o, slot p.x.wx 8, p.x.wx⟩)
    (fun p s ⟨minv, hc, hw, hw'⟩ => ⟨⟨minv, hc.good, Nat.le_refl _⟩, hw, hw'⟩) (rangeMask_ct aboveOne)

theorem loadedRange_ct (aboveOne : Bool) : RelCT isa (Two LoadedCheck) (Checks.rangeMask aboveOne)
    (Two fun (p : BPub) s => LinkedPre p.x s) := by
  refine two_post (loadedRange_trace aboveOne) ?_
  intro p s ⟨minv, hc, hw, hw'⟩
  exact WP.mono (rangeMask_ok hc.good (Nat.le_refl _) hw hw' aboveOne)
    fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩

theorem leaveAccumulate_ct : RelCT isa (Two LinkedPre)
    (.block (([Crt.leave] : List Instr) ++ Checks.accumulate)) (fun _ _ => True) := by
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x0 = p.B) [.x0]
    (pins_of (fun p _ => off p.B p.o) (by
      intro p s ⟨_, hc⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hc.x0)) (by taint_decide) ?_) ?_
  · intro p s ⟨minv, hc⟩
    drun [Crt.leave, hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.wx 8 by
        have := hdr_lt_slot p.wx 8 (show Crt.sLink < 32 by decide); omega)]
  exact two_taint [.x0] (pins_of (fun p _ => p.B) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h)) (by taint_decide)

end VG.Proof.Dsa.AArch64
