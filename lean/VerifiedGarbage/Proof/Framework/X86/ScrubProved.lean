module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# The cleanup as part of the code, and what it needs of the code (x86, 32-bit)

A function's code as emitted, its body and then its cleanup, is a named
definition in `Impl/` (`Impl.<Alg>.X86.Fn.<f>`), written with the cleanup's
literals: the result's bits it keeps and, for code with frames or calls, the
bytes of stack it zeroes:

    def Fn.update : Prog isa := Impl.Scrub.X86.scrubAll 0 704 (Instances.absorb rate)

`verifiedScrubbed` (code that calls nothing, `Impl.Scrub.X86.scrub`) and
`verifiedScrubbedAll` (code with frames, direct calls and calls through its
tables, `Impl.Scrub.X86.scrubAll`) state `VerifiedScrubbed` of that code: the
theorem about the code that a registration binds (`verified := …`).
Each takes what the cleanup needs of the code as one Boolean (`scrubSide`,
`scrubFSide`), so that the kernel evaluates the code once and the proof
module writes one proof, by default `lit_decide`, rather than one theorem
per fact; a fact that does not hold is an error at the theorem. The stack
and the result's bits are the literals of the code (`W`, `rb`), so that `hW`
and `hb` are `rfl`. A function generic over a variant gives `hs` from
`X86.Scrub.scrubFSide_of_fill` or `scrubFSide_of_fillB`
(`Proof/Framework/X86/ScrubCall.lean`), proved of every implementation where
it is stated, never by evaluating the variant's code.

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

/-- `r`'s code, which calls nothing and has no frame, followed by `tail rb`
(`scrub`), meets `r`'s contract in constant time and returns without secret
residue: the theorem about the code that a registration binds. -/
theorem verifiedScrubbed {api : Api} (r : Unscrubbed api target) {rb : Nat}
    (hs : scrubSide r.code = true := by (try dsimp only); lit_decide)
    (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrub rb r.code) r.contract rb := by
  subst hb
  obtain ⟨hn, hm⟩ := of_scrubSide hs
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  unfold retBitsOf
  rw [e] at hv ⊢
  have h := Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv hn hm rfl
  exact ⟨h.1, h.2⟩

/-- `r`'s code, with frames and direct calls or calls through its tables,
followed by the zeroing of its `W` bytes of stack below `esp` and `tail rb`
(`scrubAll`), meets `r`'s contract in constant time and returns without secret
residue, given that its postcondition reads the memory on return only within
the buffers (`hpost`): the theorem about the code that a registration
binds. -/
theorem verifiedScrubbedAll {api : Api} (r : Unscrubbed api target) (hpost : PostOut r.contract (retBitsOf r))
    {W rb : Nat} (hs : scrubFSide r.code r.tables W = true := by (try dsimp only); lit_decide)
    (hW : r.stack = W := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll rb W r.code) r.contract rb := by
  subst hb hW
  obtain ⟨hd, htc, hm, hn⟩ := of_scrubFSide hs
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hp ⊢
  rw [e] at hv hp ⊢
  have h := Verified.scrubAllT (ScrubAbi.of r.consts api.sig r.tables) hv (noSp_of_all r.spSafe) hd
    (tablesCall_fnAddr htc) hm hn rfl hp
  exact ⟨h.1, h.2⟩

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
