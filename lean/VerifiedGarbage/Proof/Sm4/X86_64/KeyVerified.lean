import VerifiedGarbage.Proof.Sm4.X86_64.KeyEk
import VerifiedGarbage.Proof.Sm4.X86_64.Verified

/-!
# SM4 key expansion on x86-64 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does.
-/

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
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 390⟩]

theorem expandKey_verified :
    Verified X86_64.target expandKey (Proof.Sm4.expandKeyScratchContract X86_64.abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyX86_64, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3128 .rdx 390 expandKey)
      (Spec.Sm4.expandKeyContract X86_64.abi 3128) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 390) (post := Proof.Sm4.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3128) expandKey_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
