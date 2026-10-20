module

public import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
public import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit

/-!
# SM4 ECB on x86-64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them. `ecb_framed` runs it with its
working space on the stack, zeroed on return: 3144 bytes, the 392 words of
the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (specDir ecbX86_64)

/-- The initial taint: the registers of the arguments and the stack pointer are
public. It knows nothing of the writable regions: the code never reads a public
value back from them, and tracking them would cost the kernel at every store. -/
def ecbTaint : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecbTaint_agree (dir : Dir) (s t : State) (_ : (ecbX86_64 dir).pre s) (_ : (ecbX86_64 dir).pre t)
    (hp : (ecbX86_64 dir).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbX86_64 dir).pre (ecbX86_64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .decrypt) (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbX86_64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86_64 dir).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ecb_wp dir hs
  refine ⟨t, s', he, abiPreserved_of_exec (c := ecb dir) ?_ he hg, hpost⟩
  cases dir <;> lit_decide

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 1 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 392⟩]

theorem ecb_verified (dir : Dir) :
    Verified X86_64.target (ecb dir) (Proof.Sm4.ecbScratchContract X86_64.abi (specDir dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbX86_64, specDir,
      X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (ecb dir))
      (Spec.Sm4.ecbContract X86_64.abi (specDir dir) 3144) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 392) (post := Spec.Sm4.ecbPost (specDir dir) X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3144) (ecb_verified dir) (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by cases dir <;> lit_decide)) (by cases dir <;> lit_decide) (by decide)
    (Proof.Sm4.ecbPostOut_local _ _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
