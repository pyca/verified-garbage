module

import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The stack pointer and MXCSR of a function with its calls inlined, by one check

The ABI's obligations of the x86-64 signatures and verifications need two
facts of every instruction of their code with its calls inlined: it does not
write `rsp` (`Exec.gpr`) and it does not load MXCSR (`abiPreserved_of_exec`).
The kernel evaluates both on the code's literal (`lit_decide`): checked
together, it goes through the code once rather than twice.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64

/-- Neither `rsp` written nor MXCSR loaded by any instruction of `c` with its
calls inlined, from one check of `c`. -/
theorem rsp_mxcsr {c : Prog isa}
    (h : c.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true) :
    (∀ i ∈ instrs c.inline, Taint.clobbers i .rsp = false) ∧
      c.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at h
  refine ⟨fun i hi => ?_, ?_⟩
  · have := h i hi
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this.1
  · rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    have := h i hi
    simp only [Bool.and_eq_true] at this
    exact this.2

end VG.Proof.Ecdsa.X86_64
