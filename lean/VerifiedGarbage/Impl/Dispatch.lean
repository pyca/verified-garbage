module

public import VerifiedGarbage.TCB.Code

/-!
# Choosing code by a public selector

Code that takes a choice of algorithm as an argument (e.g. a hash function,
by its number) runs the code for the choice at each place that depends on
it: `chain test eq cases` runs, of the `cases` `(k, c)`, the `c` whose `k`
is the selector. For each case but the last, `test k` sets the condition
`eq` to whether the selector is `k` (e.g. `cmp rax, k` with the selector in
`rax`), and its code runs if so; the last case runs if none of the others
did, with no test (the precondition of the code says the selector is one of
the cases'). Each case is typically a direct call of the function for that
choice. The selector is public, so each test is a branch on public data.
-/

@[expose] public section

namespace VG.Impl.Dispatch

variable {M : ISA}

/-- The case of `cases` whose key is the selector: `test k` then `eq` for
each case `(k, c)` but the last, which runs if none of them did. -/
def chain (test : Nat → List M.Instr) (eq : M.Cond) : List (Nat × Prog M) → Prog M
  | [] => .block []
  | [(_, c)] => c
  | (k, c) :: cs => .seq (.block (test k)) (.ite eq c (chain test eq cs))

end VG.Impl.Dispatch
