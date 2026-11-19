module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Lit

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
def scrubOf {api : Api} (r : Registration api target) (hpost : PostOut r.contract (retBitsOf r))
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
def scrubSelOf {api : Api} (r : Registration api target) (fs : List (Nat × List (Nat × Nat)))
    (hpost : PostOut r.contract (retBitsOf r))
    (hnr : FramesOk fs → sizeOf fs ≤ r.stack → retBitsOf r ≤ 64 →
      NoResidue (scrubSel (retBitsOf r) fs r.code) r.contract (retBitsOf r))
    (hs : selSide fs r.stack (retBitsOf r) = true := by
      dsimp only [VG.RISCV64.Scrub.retBitsOf]; lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  scrubSelReg r fs (of_selSide hs).1 (of_selSide hs).2.1 (of_selSide hs).2.2 hpost
    (hnr (of_selSide hs).1 (of_selSide hs).2.1 (of_selSide hs).2.2) hw

end VG.RISCV64.Scrub
