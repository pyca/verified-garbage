module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Registration

/-!
# Scrubbed code registered with its facts proved (64-bit RISC-V)

`scrubOf` and `scrubSelOf`: what `Scrub.withScrub` and `Scrub.withScrubSel`
register, with nothing left for the emitter to decide. What the scrub needs
of the code and of the registration's stack is one Boolean (`scrubSide`,
`selSide`), whose proof is an argument: by default the kernel's evaluation
of it where the registration is defined, when that module is built. The
registration is `scrubReg`'s or `scrubSelReg`'s record: no `if`, and no
registration without a proof behind an `else`. A fact that does not hold is
an error at the definition.

The clearing itself needs nothing of the code on RISC-V: it wipes the
registration's `stack` bytes (or the runs the call site states) and every
caller-saved register.

`verifiedScrubbed` and `verifiedScrubbedSel` (below) state the same as
theorems about the code with its cleanup, `scrub rb W c` and
`scrubSel rb fs c`, which `Impl/` defines as the function: the proof a
registration binds (`verified := .scrubbed …`), the form every registration
takes once its family is converted. `scrubOf` and `scrubSelOf` remain for
the families not yet converted.
-/

@[expose] public section

namespace VG.RISCV64.Scrub

open VG.Impl.Scrub.RISCV64

/-- What `scrubOf` needs of code `c` scrubbed over `stack` bytes, with the
tables `ts` and a result of `rb` bits: `withScrub`'s conditions. Its frames
use at most `stack` bytes, a multiple of 16 below `2 ^ 64`; it calls
indirectly only the functions of its tables; the result has at most 64
bits. -/
def scrubSide (c : Prog isa) (stack rb : Nat) (ts : List (String × List FnTable)) : Bool :=
  decide (c.riscv64Depth ≤ stack) && decide (stack < 2 ^ 64) && stack % 16 == 0 && tablesCall c ts &&
    decide (rb ≤ 64)

theorem of_scrubSide {c : Prog isa} {stack rb : Nat} {ts : List (String × List FnTable)}
    (h : scrubSide c stack rb ts = true) :
    c.riscv64Depth ≤ stack ∧ stack < 2 ^ 64 ∧ stack % 16 = 0 ∧ tablesCall c ts = true ∧ rb ≤ 64 := by
  simp only [scrubSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `r`, its code followed by the clearing (`scrub`) of its `r.stack` bytes
of stack and its caller-saved registers, returning without secret residue:
`withScrub`, with what it needs of the code proved (`scrubSide`, which the
kernel evaluates where the registration is defined, by default) rather than
decided when the registration is evaluated.

A registration generic over the implementations of what its code calls
gives `W` and `rb`, its stack and its result's bits, and `hs`, proved of
every implementation of the list by one evaluation: `hs` is then stated
with them, and not with projections of `r`. -/
def scrubOf {api : Api} (r : Unscrubbed api target) (hpost : PostOut r.contract (retBitsOf r))
    (W : Nat := r.stack) (rb : Nat := retBitsOf r)
    (hs : scrubSide r.code W rb r.tables = true := by
      dsimp only [VG.RISCV64.Scrub.retBitsOf]; lit_decide)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl)
    (hw : r.written = [] := by rfl) : Registration api target :=
  have hs : scrubSide r.code r.stack (retBitsOf r) r.tables = true := by rw [hW, hb]; exact hs
  scrubReg r (of_scrubSide hs).1 (of_scrubSide hs).2.1 (of_scrubSide hs).2.2.1 (of_scrubSide hs).2.2.2.1
    (of_scrubSide hs).2.2.2.2 hpost hw

/-- What `scrubSelOf` needs of the frames `fs` it clears runs of, within a
stack of `stack` bytes, with a result of `rb` bits: `withScrubSel`'s
conditions. -/
def selSide (fs : List (Nat × List (Nat × Nat))) (stack rb : Nat) : Bool :=
  framesOkB fs && decide (sizeOf fs ≤ stack) && decide (rb ≤ 64)

theorem of_selSide {fs : List (Nat × List (Nat × Nat))} {stack rb : Nat} (h : selSide fs stack rb = true) :
    FramesOk fs ∧ sizeOf fs ≤ stack ∧ rb ≤ 64 := by
  simp only [selSide, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨framesOk_of h.1.1, h.1.2, h.2⟩

/-- `r`, its code followed by the clearing of only the runs of `fs`
(`scrubSel`), returning without secret residue: `withScrubSel`, with its
conditions on `fs` proved (`selSide`) rather than decided when the
registration is evaluated. `hnr` is `scrubSel_noResidue`'s, given them. -/
def scrubSelOf {api : Api} (r : Unscrubbed api target) (fs : List (Nat × List (Nat × Nat)))
    (hpost : PostOut r.contract (retBitsOf r))
    (hnr : FramesOk fs → sizeOf fs ≤ r.stack → retBitsOf r ≤ 64 →
      NoResidue (scrubSel (retBitsOf r) fs r.code) r.contract (retBitsOf r))
    (hs : selSide fs r.stack (retBitsOf r) = true := by
      dsimp only [VG.RISCV64.Scrub.retBitsOf]; lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  scrubSelReg r fs (of_selSide hs).1 (of_selSide hs).2.1 (of_selSide hs).2.2 hpost
    (hnr (of_selSide hs).1 (of_selSide hs).2.1 (of_selSide hs).2.2) hw

/-! ## The cleanup as part of the code

The theorems a registration binds (`verified := .scrubbed …`): of the code
as emitted, its body and then its cleanup (`scrub rb W c`, or
`scrubSel rb fs c`), which `Impl/` defines as the function with the stack
`W` (or the runs `fs`) and the result's bits `rb` as literals. Each takes
what the cleanup needs of the code as a hypothesis, which the proof module
gives: by `lit_decide` of `scrubSide` or `selSide`, or, for code generic
over the implementations of a function it calls, from what the function
proves of its own instructions and each implementation of its own
(`verifiedScrubbedOf` takes the facts one by one). `W` and `rb` are
arguments, so that the hypotheses are stated with them and not with
projections of `r`; `hW` and `hb` tie them to `r`'s stack and result. -/

/-- `r`'s code with its cleanup (`scrub`, over `W` bytes of stack, the
stack its frames use, with a result of `rb` bits) meets `r`'s contract in
constant time and returns without secret residue, from `withScrub`'s
conditions given one by one. -/
theorem verifiedScrubbedOf {api : Api} (r : Unscrubbed api target) {W rb : Nat}
    (hpost : PostOut r.contract rb) (hd : r.code.riscv64Depth ≤ W) (hst : W < 2 ^ 64)
    (h16 : W % 16 = 0) (htc : tablesCall r.code r.tables = true) (hrb : rb ≤ 64)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrub rb W r.code) r.contract rb := by
  subst hW hb
  have h := scrubCode_ok r hd hst h16 htc hrb hpost
  exact ⟨h.1, h.2⟩

/-- `verifiedScrubbedOf`, with its conditions one Boolean (`scrubSide`):
what `scrubOf` registers, as the theorem about the code that a registration
binds. -/
theorem verifiedScrubbed {api : Api} (r : Unscrubbed api target) {W rb : Nat}
    (hpost : PostOut r.contract rb) (hs : scrubSide r.code W rb r.tables = true)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrub rb W r.code) r.contract rb :=
  have h := of_scrubSide hs
  verifiedScrubbedOf r hpost h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hW hb

/-- `r`'s code `code` with its cleanup of only the runs of `fs`
(`scrubSel`, with a result of `rb` bits) meets `r`'s contract in constant
time and returns without secret residue: what `scrubSelOf` registers, as
the theorem about the code that a registration binds. `hnr` is the residue
analysis's (`scrubSel_noResidue`, or `verifiedScrubbedSelT`). -/
theorem verifiedScrubbedSel {api : Api} (r : Unscrubbed api target)
    (fs : List (Nat × List (Nat × Nat))) {code : Prog isa} {W rb : Nat}
    (hpost : PostOut r.contract rb) (hs : selSide fs W rb = true)
    (hnr : NoResidue (scrubSel rb fs code) r.contract rb)
    (hc : r.code = code := by rfl) (hW : r.stack = W := by rfl)
    (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubSel rb fs code) r.contract rb := by
  subst hc hW hb
  have h := of_selSide hs
  exact ⟨scrubSelCode_verified r fs h.1 h.2.1 h.2.2 hpost, hnr⟩

/-- `verifiedScrubbedSel`, with the residue analysis of the code with its
cleanup (`RISCV64.rtaint`, from a state where the `e.2` bytes from what each
register `e.1` of `bp0` holds are buffers of the contract's: `hbp`) ending
in `done`: `hres`, which the kernel evaluates where the theorem is used
(`taint_decide_ct`), stated of `code`, `W` and `rb`. -/
theorem verifiedScrubbedSelT {api : Api} (r : Unscrubbed api target)
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
  exact verifiedScrubbedSel r fs (hpost := hpost) hs
    (scrubSel_noResidue r fs bp0 h.1 h.2.1 h.2.2 hpost hbp _ _ _ rfl rfl rfl hres)

end VG.RISCV64.Scrub
