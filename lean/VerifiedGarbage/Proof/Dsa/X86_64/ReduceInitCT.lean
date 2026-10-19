module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.Layout
meta import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time loading of reduction pointers and lengths -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def LinkedPre (p : XPub) (s : State) : Prop := ∃ minv, SubCtx s p.B p.Z p.o p.w p.wx minv

/-- Reading a linked parent's argument slots does not dereference the
argument values. The parent and child addresses alone determine this trace. -/
theorem reduceInit_ct : RelCT isa (Two LinkedPre) (.block (Arithmetic.reduceInit arg argLen))
    (fun _ _ => True) := by
  change RelCT isa (Two LinkedPre) (.block (
    ([.mov .rax (.mem (hdr Crt.sLink))] : List Instr) ++
    [.mov .rsi (.mem (Crt.ws .rax arg)), .mov .rcx (.mem (Crt.ws .rax argLen)),
      .store (hdr Crt.sSrc) .rsi, .store (hdr Crt.sRem) .rcx, .alu .test .rcx (.reg .rcx)])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rdi = off p.B p.o ∧ s.gpr .rax = p.B) [.rdi]
    (pins_of (fun p _ => off p.B p.o) (by
      intro p s ⟨_, hc⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      exact hc.rdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨minv, hc⟩
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B) ?_ rfl)
      fun t ⟨ha, hk⟩ => ⟨(hk.gpr (by decide)).trans hc.rdi, ha⟩
    xrun [State.ea, hdr, hc.rdi, hdrOff, hc.link,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot p.wx 8 by
        have := hdr_lt_slot p.wx 8 (show Crt.sLink < 32 by decide); omega)]
  exact two_taint [.rdi, .rax]
    (pins_of (fun p r => if r = .rdi then off p.B p.o else p.B) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64
