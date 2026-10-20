module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time loading of reduction pointers and lengths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def LinkedPre (p : XPub) (s : State) : Prop := ∃ minv, SubCtx s p.B p.Z p.o p.w p.wx minv

/-- Reading a linked parent's argument slots does not dereference the
argument values. The parent and child addresses alone determine this trace. -/
theorem reduceInit_ct : RelCT isa (Two LinkedPre) (.block (Arithmetic.reduceInit arg argLen))
    (fun _ _ => True) := by
  change RelCT isa (Two LinkedPre) (.block (
    ([ldh .x5 Crt.sLink] : List Instr) ++
    [Crt.ldw .x1 .x5 arg, Crt.ldw .x3 .x5 argLen, sth .x1 Crt.sSrc, sth .x3 Crt.sRem])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x0 = off p.B p.o ∧ s.gpr .x5 = p.B) [.x0]
    (pins_of (fun p _ => off p.B p.o) (by
      intro p s ⟨_, hc⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hc.x0)) (by taint_decide) ?_) ?_
  · intro p s ⟨minv, hc⟩
    refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B) ?_ rfl rfl rfl)
      fun t ⟨ha, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hc.x0, ha⟩
    change WP isa (.block [ldh .x5 Crt.sLink]) s _
    drun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.wx 8 by
        have := hdr_lt_slot p.wx 8 (show Crt.sLink < 32 by decide); omega)]
  exact two_taint [.x0, .x5]
    (pins_of (fun p r => if r = .x0 then off p.B p.o else p.B) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
