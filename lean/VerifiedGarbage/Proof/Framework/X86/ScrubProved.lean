module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# What the cleanup needs of the code (x86, 32-bit)

`scrubSide` and `scrubFSide`: what `verifiedScrubbed` and
`verifiedScrubbedAll` (`ScrubFn.lean`) need of the code, as one Boolean each,
so that the kernel evaluates the code once and the proof module writes one
proof, by default `lit_decide`, rather than one theorem per fact. A fact
that does not hold is an error at the theorem.

Which form to use:

* `scrub rb c`, `verifiedScrubbed`: code that calls nothing and has no frame
  (`Code.noCalls`). The cleanup appends `tail`, which clears `eax`, `ecx`,
  `edx` (but the result's bits), the flags and `xmm0`–`xmm7`.
* `scrubAll rb W c`, `verifiedScrubbedAll`: code with frames or calls,
  direct or indirect through the registration's tables of functions
  (`tablesCall`), whose stack use (`stackUse`, callees included) fits in
  the `W` bytes its contract reserves, with `0 < W` and `W % 4 = 0`. The
  cleanup zeroes those `W` bytes below `esp`, then appends `tail`. `hpost`
  says that the postcondition reads the memory on return only within the
  buffers; build it from the contract's locality lemma with
  `postOut_of_local`.

Neither covers code with an MMX instruction or frame, nor `scrubAll` of code
that calls indirectly a function of none of its tables: the side condition
is then false, and the default proof fails.

The default proof is `lit_decide` of the side condition with the
registration's projections reduced: import the code's `Lit` module (and its
callees'), so that the kernel evaluates the literal. A function generic
over a list of variants (`Proof/Variants/<Iface>/X86.lean`), whose code is
not a closed term, gives the proof itself, as `hs`, proved of every
implementation of the list by one evaluation (`scrubFSide_of_fill`), with
its stack as `W`.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.Impl.Scrub.X86

/-- The result's bits of `r`'s function, which the tail keeps. -/
abbrev retBitsOf {api : Api} (r : Unscrubbed api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

/-- What `verifiedScrubbed` needs of code `c`: it calls nothing and has no frame,
and none of its instructions is an MMX instruction. -/
noncomputable def scrubSide (c : Prog isa) : Bool :=
  c.noCalls && c.allInstrs (fun i => !i.isMmx)

theorem of_scrubSide {c : Prog isa} (h : scrubSide c = true) :
    c.noCalls = true ∧ c.allInstrs (fun i => !i.isMmx) = true := by
  simp only [scrubSide, Bool.and_eq_true] at h
  exact h

/-- What `verifiedScrubbedAll` needs of code `c` with tables of functions `ts`,
scrubbed over `stack` bytes: its calls and frames use at most `stack` bytes
below `esp` (`stackUse`, which counts what the functions it calls
indirectly use), it calls indirectly only the functions of `ts`
(`tablesCall`, which code with no indirect call satisfies), it has no MMX
instruction, and `stack` is a frame the wipe can zero (`FrameOk`: positive,
a multiple of 4).
It is the one place these conditions are stated: covering more code changes
this definition and `of_scrubFSide`, and call sites keep their proof. -/
noncomputable def scrubFSide (c : Prog isa) (ts : List (String × List FnTable)) (stack : Nat) : Bool :=
  decide (stackUse c ≤ stack) && tablesCall c ts && c.allInstrs (fun i => !i.isMmx) &&
    decide (0 < stack) && stack % 4 == 0

theorem of_scrubFSide {c : Prog isa} {ts : List (String × List FnTable)} {stack : Nat}
    (h : scrubFSide c ts stack = true) :
    stackUse c ≤ stack ∧ tablesCall c ts = true ∧ c.allInstrs (fun i => !i.isMmx) = true ∧
      FrameOk stack := by
  simp only [scrubFSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

end VG.X86.Scrub
