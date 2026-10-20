module

public import VerifiedGarbage.Proof.Sm4.X86_64.KeyEk
meta import VerifiedGarbage.Proof.Sm4.X86_64.KeyEk
public import VerifiedGarbage.Proof.Sm4.X86_64.Lit
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.X86_64.Copy
import VerifiedGarbage.Proof.Sm4.X86_64.GroupStep
import VerifiedGarbage.Proof.Sm4.X86_64.KeyInit
import VerifiedGarbage.Proof.Sm4.X86_64.Verified
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.X86_64.Copy
meta import VerifiedGarbage.Proof.Sm4.X86_64.GroupStep
meta import VerifiedGarbage.Proof.Sm4.X86_64.KeyInit
meta import VerifiedGarbage.Proof.Sm4.X86_64.Verified
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# SM4 key expansion on x86-64 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (expandKeyX86_64)

theorem expandKey_ct : ConstantTime isa expandKeyX86_64.pre expandKeyX86_64.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨p1, p2, p3, p4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4]

theorem expandKey_correct (s : State) (hs : expandKeyX86_64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := expandKey_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := expandKey) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 392⟩]

theorem expandKey_verified :
    Verified X86_64.target expandKey (Proof.Sm4.expandKeyScratchContract X86_64.abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyX86_64, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 expandKey)
      (Spec.Sm4.expandKeyContract X86_64.abi 3144) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 392) (post := Proof.Sm4.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3144) expandKey_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
