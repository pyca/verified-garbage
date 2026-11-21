module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved

/-!
# The cleanup as part of the code (x86, 32-bit)

A function's code as emitted, its body and then its cleanup, is a named
definition in `Impl/` (`Impl.<Alg>.X86.Fn.<f>`), written with the cleanup's
literals: the result's bits it keeps and, for code with frames or calls, the
bytes of stack it zeroes:

    def Fn.update : Prog isa := Impl.Scrub.X86.scrubAll 0 704 (Instances.absorb rate)

`verifiedScrubbed` (code that calls nothing, `Impl.Scrub.X86.scrub`) and
`verifiedScrubbedAll` (code with frames, direct calls and calls through its
tables, `Impl.Scrub.X86.scrubAll`) state `VerifiedScrubbed` of that code: what
`X86.Scrub.scrubOf` and `scrubAllOf` register, as the theorem about the code
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
(`scrubAll`), meets `r`'s contract in constant time and returns without secret
residue, given that its postcondition reads the memory on return only within
the buffers (`hpost`): what `scrubAllOf` registers, as the theorem about the
code that a registration binds. -/
theorem verifiedScrubbedAll {api : Api} (r : Unscrubbed api target) (hpost : PostOut r.contract (retBitsOf r))
    {W rb : Nat} (hs : scrubFSide r.code r.tables W = true := by (try dsimp only); lit_decide)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) (hw : r.written = [] := by rfl) :
    VerifiedScrubbed target (scrubAll rb W r.code) r.contract rb := by
  have e : api.sig.retBits target.abi.ptrBits = retBitsOf r :=
    (Abi.retBits_withConsts_withTables target.abi api.sig api.sig r.consts r.tables).symm
  subst hb
  have h := (scrubAllOf r hpost W hs hW hw).verified
  have hn := h.noResidue
  rw [e] at hn
  have hv := h.verified
  rw [show (scrubAllOf r hpost W hs hW hw).code = scrubAll (retBitsOf r) W r.code by
    simp only [scrubAllOf, scrubRegFT, hW]] at hv hn
  exact ⟨hv, hn⟩

/-- The code as emitted, `c` and then its cleanup (`scrub`), writes `esp`
only in its frames and calls, as `c` does: `Registration.spSafe` of a
function's `Fn` from its body's, for code generic over a variant, which
`sp_safe` does not evaluate. -/
theorem scrub_spSafe {rb : Nat} {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrub rb c).all (fun i => !isa.writesSp i) = true := by
  simp only [scrub, Code.all, h, tail_all, Bool.true_and]

/-- The code as emitted, `c` and then its cleanup (`scrubAll`), writes `esp`
only in its frames and calls, as `c` does. -/
theorem scrubAll_spSafe {rb W : Nat} {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubAll rb W c).all (fun i => !isa.writesSp i) = true := by
  simp only [scrubAll, wipeBelow, Code.all, h, zeroRegs_all, tail_all, Bool.true_and, Bool.and_true]
  exact wipe_all _

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers where the precondition holds (one that reads an
output buffer by a length the precondition equates with the buffer's). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

end VG.X86.Scrub
