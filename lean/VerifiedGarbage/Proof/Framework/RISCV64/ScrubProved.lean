module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Registration

/-!
# Scrubbed code, verified (64-bit RISC-V)

The theorems a registration binds (`verified := .scrubbed …`):
`verifiedScrubbedAll` and `verifiedScrubbedSel` state, of the code with its
cleanup, `scrubAll rb W c`
or `scrubSel rb fs c`, which `Impl/` defines as the function, that it meets
its contract in constant time and returns without secret residue. The
registration binds that definition and that theorem, and nothing else: no
builder, no wrapper and no side condition of its own.

What the cleanup needs of the code and of its stack is one Boolean
(`scrubSide`, `selSide`), a hypothesis the proof module gives: by the
kernel's evaluation of it (`lit_decide`) when that module is built. A fact
that does not hold is an error at the theorem.

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

/-- What `verifiedScrubbedSel` needs of the frames `fs` it clears runs of,
within a stack of `stack` bytes, with a result of `rb` bits: each frame a
nonzero multiple of 16 bytes, at most 2048, that holds its runs
(`FramesOk`); all of them within the stack; a result of at most 64 bits. -/
def selSide (fs : List (Nat × List (Nat × Nat))) (stack rb : Nat) : Bool :=
  framesOkB fs && decide (sizeOf fs ≤ stack) && decide (rb ≤ 64)

theorem of_selSide {fs : List (Nat × List (Nat × Nat))} {stack rb : Nat} (h : selSide fs stack rb = true) :
    FramesOk fs ∧ sizeOf fs ≤ stack ∧ rb ≤ 64 := by
  simp only [selSide, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨framesOk_of h.1.1, h.1.2, h.2⟩

/-! ## The cleanup as part of the code

The theorems a registration binds (`verified := .scrubbed …`): of the code
as emitted, its body and then its cleanup (`scrubAll rb W c`, or
`scrubSel rb fs c`), which `Impl/` defines as the function with the stack
`W` (or the runs `fs`) and the result's bits `rb` as literals. Each takes
what the cleanup needs of the code as a hypothesis, which the proof module
gives: by `lit_decide` of `scrubSide` or `selSide`, or, for code generic
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

/-- `r`'s code `code` with its cleanup of only the runs of `fs`
(`scrubSel`, with a result of `rb` bits) meets `r`'s contract in constant
time and returns without secret residue: the theorem about the code that a
registration binds. The residue analysis of the code with its cleanup
(`RISCV64.rtaint`, from a state where the `e.2` bytes from what each
register `e.1` of `bp0` holds are buffers of the contract's: `hbp`) ends
in `done`: `hres`, which the kernel evaluates where the theorem is used
(`taint_decide_ct`), stated of `code`, `W` and `rb`. -/
theorem verifiedScrubbedSel {api : Api} (r : Unscrubbed api target)
    (fs : List (Nat × List (Nat × Nat))) (bp0 : List (Reg × Nat)) {code : Prog isa} {W rb : Nat}
    (hpost : PostOut r.contract rb) (hs : selSide fs W rb = true)
    (hbp : ∀ s, r.contract.pre s → ∀ e ∈ bp0, ∀ i < e.2, ∃ g ∈ s.rd ++ s.wr,
      g.Contains (s.gpr e.1 + BitVec.ofNat 64 i) 1)
    (hres : ∃ hc, (rtaint.check (RTaint.init W bp0) (scrubSel rb fs code) hc).any
      (RTaint.done rb) = true)
    (hc : r.code = code := by rfl) (hW : r.stack = W := by rfl)
    (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubSel rb fs code) r.contract rb := by
  subst hc hW hb
  have h := of_selSide hs
  exact ⟨scrubSelCode_verified r fs h.1 h.2.1 h.2.2 hpost,
    scrubSel_noResidue r fs bp0 h.1 h.2.1 h.2.2 hpost hbp _ _ _ rfl rfl rfl hres⟩

end VG.RISCV64.Scrub
