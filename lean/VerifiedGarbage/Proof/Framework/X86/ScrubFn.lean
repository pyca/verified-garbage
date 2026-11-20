module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved

/-!
# The cleanup as part of the code (x86, 32-bit)

A function's code as emitted, its body and then its cleanup, is a named
definition in `Impl/` (`Impl.<Alg>.X86.Fn.<f>`), written with the cleanup's
literals: the result's bits it keeps and, for code with frames or calls, the
bytes of stack it zeroes:

    def Fn.update : Prog isa := Impl.Scrub.X86.scrubF 0 704 (Instances.absorb rate)

`verifiedScrubbed` (code that calls nothing, `Impl.Scrub.X86.scrub`) and
`verifiedScrubbedF` (code with frames, direct calls and calls through its
tables, `Impl.Scrub.X86.scrubF`) state `VerifiedScrubbed` of that code: what
`X86.Scrub.scrubOf` and `scrubFOf` register, as the theorem about the code
that a registration binds (`verified := .scrubbed …`). They take what those
forms take, the side condition included (`scrubSide`, `scrubFSide`, by default
`lit_decide`), with the stack and the result's bits as the literals of the
code (`W`, `rb`), so that `hW` and `hb` are `rfl`. A function generic over a
variant gives `hs` from `X86.Scrub.scrubFSide_of_fill` or
`scrubFSide_of_fillB` (`Proof/Framework/X86/ScrubCall.lean`), proved of every
implementation where it is stated, never by evaluating the variant's code.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.Impl.Scrub.X86

/-- `r`'s code, which calls nothing and has no frame, followed by `tail rb`
(`scrub`), meets `r`'s contract in constant time and returns without secret
residue: what `scrubOf` registers, as the theorem about the code that a
registration binds. -/
theorem verifiedScrubbed {api : Api} (r : Unscrubbed api target) {rb : Nat}
    (hs : scrubSide r.code = true := by (try dsimp only); lit_decide)
    (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrub rb r.code) r.contract rb := by
  have e : api.sig.retBits target.abi.ptrBits = retBitsOf r :=
    (Abi.retBits_withConsts_withTables target.abi api.sig api.sig r.consts r.tables).symm
  subst hb
  have h := (scrubOf r hs).verified
  have hn := h.noResidue
  rw [e] at hn
  exact ⟨h.verified, hn⟩

/-- `r`'s code, with frames and direct calls or calls through its tables,
followed by the zeroing of its `W` bytes of stack below `esp` and `tail rb`
(`scrubF`), meets `r`'s contract in constant time and returns without secret
residue, given that its postcondition reads the memory on return only within
the buffers (`hpost`): what `scrubFOf` registers, as the theorem about the
code that a registration binds. -/
theorem verifiedScrubbedF {api : Api} (r : Unscrubbed api target) (hpost : PostOut r.contract (retBitsOf r))
    {W rb : Nat} (hs : scrubFSide r.code r.tables W = true := by (try dsimp only); lit_decide)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) (hw : r.written = [] := by rfl) :
    VerifiedScrubbed target (scrubF rb W r.code) r.contract rb := by
  have e : api.sig.retBits target.abi.ptrBits = retBitsOf r :=
    (Abi.retBits_withConsts_withTables target.abi api.sig api.sig r.consts r.tables).symm
  subst hb
  have h := (scrubFOf r hpost W hs hW hw).verified
  have hn := h.noResidue
  rw [e] at hn
  have hv := h.verified
  rw [show (scrubFOf r hpost W hs hW hw).code = scrubF (retBitsOf r) W r.code by
    simp only [scrubFOf, scrubRegFT, hW]] at hv hn
  exact ⟨hv, hn⟩

end VG.X86.Scrub
