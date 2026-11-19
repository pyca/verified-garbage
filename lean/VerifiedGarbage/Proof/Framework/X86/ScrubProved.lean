module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# Scrubbed code registered with its facts proved (x86, 32-bit)

`scrubOf` and `scrubFOf`: what `Scrub.scrubReg` and `Scrub.scrubRegF`
register, with what they need of the code stated as one Boolean each
(`scrubSide`, `scrubFSide`), so that the kernel evaluates the code once, and
the call site writes one proof, by default `lit_decide`, rather than one
theorem per fact. A fact that does not hold is an error where the
registration is defined.

Which form to use:

* `scrubOf r`: code that calls nothing and has no frame (`Code.noCalls`).
  The scrub appends `tail`, which clears `eax`, `ecx`, `edx` (but the
  result's bits), the flags and `xmm0`–`xmm7`. Nothing else to give:

      scrubOf { code := Impl.Foo.X86.Stream.init, verified := Proof.Foo.X86.init }

* `scrubFOf r hpost`: code with frames or direct calls, whose stack use
  (`stackUse`, callees included) fits in the registration's `stack` bytes,
  with `0 < stack` and `stack % 4 = 0`. The scrub zeroes those
  `stack` bytes below `esp`, then appends `tail`. `hpost` says that the
  postcondition reads the memory on return only within the buffers; build it
  from the contract's locality lemma with `postOut_of_local`:

      scrubFOf { code := …, verified := … }
        (postOut_of_local ScrubAbi.plain (Proof.Foo.updatePost_out …))

Neither form covers code with an MMX instruction or frame, nor `scrubFOf`
code with an indirect call (`noIcall`), nor a registration whose `written`
is not empty: the side condition is then false, and the default proof fails.

The default proof is `lit_decide` of the side condition with the
registration's projections reduced: import the code's `Lit` module (and its
callees'), so that the kernel evaluates the literal. A registration generic
over a list of variants (`Proof/Variants/<Iface>/X86.lean`), whose code is
not a closed term, gives the proof itself, as `hs`, proved of every
implementation of the list by one evaluation, and, for `scrubFOf`, its stack
as `W` (by default `r.stack`): `hs` is then stated with `W` rather than a
projection of `r`, and `hW : r.stack = W` is `rfl`.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.Impl.Scrub.X86

/-- The result's bits of `r`'s function, which the tail keeps. -/
abbrev retBitsOf {api : Api} (r : Registration api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

/-- What `scrubOf` needs of code `c`: it calls nothing and has no frame,
and none of its instructions is an MMX instruction. -/
noncomputable def scrubSide (c : Prog isa) : Bool :=
  c.noCalls && c.allInstrs (fun i => !i.isMmx)

theorem of_scrubSide {c : Prog isa} (h : scrubSide c = true) :
    c.noCalls = true ∧ c.allInstrs (fun i => !i.isMmx) = true := by
  simp only [scrubSide, Bool.and_eq_true] at h
  exact h

/-- What `scrubFOf` needs of code `c` scrubbed over `stack` bytes: its calls
and frames use at most `stack` bytes below `esp` (`stackUse`), it makes no
indirect call (`noIcall`), it has no MMX instruction, and `stack` is a frame
the wipe can zero (`FrameOk`: positive, a multiple of 4).
It is the one place these conditions are stated: covering more code (calls
through tables rather than none, `noIcall`) changes this definition and
`of_scrubFSide`, and call sites keep their proof. -/
noncomputable def scrubFSide (c : Prog isa) (stack : Nat) : Bool :=
  decide (stackUse c ≤ stack) && noIcall c && c.allInstrs (fun i => !i.isMmx) &&
    decide (0 < stack) && stack % 4 == 0

theorem of_scrubFSide {c : Prog isa} {stack : Nat} (h : scrubFSide c stack = true) :
    stackUse c ≤ stack ∧ noIcall c = true ∧ c.allInstrs (fun i => !i.isMmx) = true ∧ FrameOk stack := by
  simp only [scrubFSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `r`, code that calls nothing and has no frame, followed by `tail`
(`scrub`), returning without secret residue: `scrubReg`, with what it needs
of the code proved as one Boolean (`scrubSide`), by default by the kernel's
evaluation where the registration is defined. -/
def scrubOf {api : Api} (r : Registration api target)
    (hs : scrubSide r.code = true := by (try dsimp only); lit_decide) : Registration api target :=
  scrubReg r (of_scrubSide hs).1 (of_scrubSide hs).2

/-- `r`, code with frames and direct calls, followed by the zeroing of its
`r.stack` bytes below `esp` and `tail` (`scrubF`), returning without secret
residue, given that its postcondition reads the memory on return only
within the buffers (`hpost`, from `postOut_of_local`): `scrubRegF`, with
what it needs of the code and the stack proved as one Boolean
(`scrubFSide`), by default by the kernel's evaluation where the
registration is defined.

A registration generic over the implementations of what its code calls
gives `W`, its stack, and `hs`, proved of every implementation of the list
by one evaluation: `hs` is then stated with `W`, not with `r.stack`. -/
def scrubFOf {api : Api} (r : Registration api target) (hpost : PostOut r.contract (retBitsOf r))
    (W : Nat := r.stack)
    (hs : scrubFSide r.code W = true := by (try dsimp only); lit_decide)
    (hW : r.stack = W := by rfl) (hw : r.written = [] := by rfl) : Registration api target :=
  have hs : scrubFSide r.code r.stack = true := by rw [hW]; exact hs
  scrubRegF r (of_scrubFSide hs).1 (of_scrubFSide hs).2.1 (of_scrubFSide hs).2.2.1 (of_scrubFSide hs).2.2.2
    hpost hw

end VG.X86.Scrub
