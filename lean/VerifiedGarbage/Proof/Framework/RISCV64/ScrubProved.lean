module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Registration

/-!
# Scrubbed code, verified (64-bit RISC-V)

The theorem a registration binds (`verified := …`) for the
cleanup of the whole frame: `verifiedScrubbedAll` states, of the code with
its cleanup, `scrubAll rb W c`, which `Impl/` defines as the function, that
it meets its contract in constant time and returns without secret residue.
The registration binds that definition and that theorem, and nothing else:
no builder, no wrapper and no side condition of its own. The selective
cleanup's, `verifiedScrubbedSel`, is in `ScrubSel.lean`.

What the cleanup needs of the code and of its stack is one Boolean
(`scrubSide`), a hypothesis the proof module gives: by the kernel's
evaluation of it (`lit_decide`) when that module is built. A fact that does
not hold is an error at the theorem.

The clearing itself needs nothing of the code on RISC-V: it wipes the
function's `W` bytes of stack (or the runs the call site states) and every
caller-saved register.
-/

@[expose] public section

namespace VG.RISCV64.Scrub

open VG.Impl.Scrub.RISCV64

/-- What `verifiedScrubbedAll` needs of code `c` scrubbed over `stack` bytes,
with the tables `ts` and a result of `rb` bits: its frames use at most
`stack` bytes, a multiple of 16 below `2 ^ 64`; it calls indirectly only
the functions of its tables; the result has at most 64 bits. -/
def scrubSide (c : Prog isa) (stack rb : Nat) (ts : List (String × List FnTable)) : Bool :=
  decide (c.riscv64Depth ≤ stack) && decide (stack < 2 ^ 64) && stack % 16 == 0 && tablesCall c ts &&
    decide (rb ≤ 64)

theorem of_scrubSide {c : Prog isa} {stack rb : Nat} {ts : List (String × List FnTable)}
    (h : scrubSide c stack rb ts = true) :
    c.riscv64Depth ≤ stack ∧ stack < 2 ^ 64 ∧ stack % 16 = 0 ∧ tablesCall c ts = true ∧ rb ≤ 64 := by
  simp only [scrubSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## The cleanup as part of the code

The theorems a registration binds (`verified := …`): of the code
as emitted, its body and then its cleanup (`scrubAll rb W c`; `scrubSel rb fs c`,
`ScrubSel.lean`), which `Impl/` defines as the function with the stack
`W` and the result's bits `rb` as literals. Each takes
what the cleanup needs of the code as a hypothesis, which the proof module
gives: by `lit_decide` of `scrubSide`, or, for code generic
over the implementations of a function it calls, from what the function
proves of its own instructions and each implementation of its own
(`scrubSide_of_fill`). `W` and `rb` are
arguments, so that the hypotheses are stated with them and not with
projections of `r`; `hW` and `hb` tie them to `r`'s stack and result. -/

/-- `r`'s code with its cleanup (`scrubAll`, over `W` bytes of stack, the
stack its frames use, with a result of `rb` bits) meets `r`'s contract in
constant time and returns without secret residue, given `scrubSide`: the
theorem about the code that a registration binds. -/
theorem verifiedScrubbedAll {api : Api} (r : Unscrubbed api target) {W rb : Nat}
    (hpost : PostOut r.contract rb) (hs : scrubSide r.code W rb r.tables = true)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll rb W r.code) r.contract rb := by
  subst hW hb
  obtain ⟨hd, hst, h16, htc, hrb⟩ := of_scrubSide hs
  have h := scrubCode_ok r hd hst h16 htc hrb hpost
  exact ⟨h.1, h.2⟩

end VG.RISCV64.Scrub
