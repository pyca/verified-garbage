module

import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Checks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Loading a checked operand and returning its secret mask -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  unfold Checks.rangeMask seqs
  refine RelCT.seq (two_piece (Ψ := fun p s =>
    RangeAddresses ⟨off p.x.B p.x.o, slot p.x.wx 8, p.x.wx, 0⟩ s) [.rdi]
    (pins_of (fun p _ => off p.x.B p.x.o) (by
      intro p s ⟨_, hc, _⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hc.rdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨_, hc, _⟩
    exact WP.mono (rangeHead_ok hc.good (Nat.le_refl _)) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  have hp : Pins (fun (p : BPub) s => RangeAddresses ⟨off p.x.B p.x.o, slot p.x.wx 8, p.x.wx, 0⟩ s)
      [.r12, .rbx, .r10] := pins_of (fun p r =>
    if r = .r12 then BitVec.ofNat 64 p.x.wx else if r = .rbx then off (off p.x.B p.x.o) (slot p.x.wx aX)
      else off (off p.x.B p.x.o) (slot p.x.wx aN)) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)
  cases aboveOne <;> exact two_taint [.r12, .rbx, .r10] hp (by taint_decide)

theorem loadedRange_ct (aboveOne : Bool) : RelCT isa (Two LoadedCheck) (Checks.rangeMask aboveOne)
    (Two fun (p : BPub) s => LinkedPre p.x s) := by
  refine two_post (loadedRange_trace aboveOne) ?_
  intro p s ⟨minv, hc, hw, hw'⟩
  exact WP.mono (rangeMask_ok hc.good (Nat.le_refl _) hw hw' aboveOne)
    fun t ⟨_, hm, hk⟩ => ⟨minv, hc.of_keep hm hk (by decide)⟩

theorem leaveAccumulate_ct : RelCT isa (Two LinkedPre)
    (.block (([Crt.leave] : List Instr) ++ Checks.accumulate)) (fun _ _ => True) := by
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = p.B) [.rdi]
    (pins_of (fun p _ => off p.B p.o) (by
      intro p s ⟨_, hc⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hc.rdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨minv, hc⟩
    xrun [Crt.leave, State.ea, hdr, hc.rdi, hdrOff, hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.wx 8 by
        have := hdr_lt_slot p.wx 8 (show Crt.sLink < 32 by decide); omega)]
  exact two_taint [.rdi] (pins_of (fun p _ => p.B) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h)) (by taint_decide)

end VG.Proof.Dsa.X86_64
