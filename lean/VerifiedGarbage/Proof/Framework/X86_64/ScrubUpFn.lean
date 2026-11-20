module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp

/-!
# The cleanup of the baseline ISA's callers of AVX code, as part of the code (x86-64)

Code of the baseline ISA that may run, through a table of functions,
functions with AVX instructions that end with `vzeroupper` cannot be cleared
at the level of every instruction it may run (`avx`), whose clearing needs a
CPU feature the code does not. `verifiedScrubbedAllUp` states
`VerifiedScrubbed` of it followed by `scrubAll .sse rb n`: two runs that may
differ only in secrets take the same path, so the upper halves of the vector
registers agree at the end (`UpperLock.up`, `upperOk_lock`), and the clearing
at the level `sse` leaves no residue (`Verified.scrubU`). It needs of the
code that its instructions, its tables' functions' included, are below the
level `evex`, `UpperLock.up`, that it loads no MXCSR and calls indirectly
only its tables' functions.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- `r`'s code followed by `scrubAll .sse rb n`, which clears the SSE
registers, the caller-saved registers but the result's `rb` bits and every
granule of the `n` bytes of stack, meets `r`'s contract in constant time and
returns without secret residue: for code below the level `evex` whose upper
halves agree after it if they did before (`hup`), which calls indirectly only
its tables' functions (`hic`). -/
theorem verifiedScrubbedAllUp {api : Api} (r : Unscrubbed api target) {n rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r))
    (hd : r.code.x86_64Depth ≤ r.stack)
    (hl1 : r.code.allInstrs (fun i => decide (i.vecLevel ≤ 1)) = true)
    (hup : UpperLock.up r.code true = true) (hic : tablesCall r.code r.tables = true)
    (hl : litSide r.stack (retBitsOf r) = true := by decide)
    (hn : r.stack = n := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll .sse rb n r.code) r.contract rb := by
  subst hn hb
  simp only [litSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
  obtain ⟨⟨⟨hst, hcs⟩, hcv⟩, hrb⟩ := hl
  have hcv' : ∀ b ∈ chunksA r.stack, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
    fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)
  have hl1' : ∀ i ∈ instrs r.code, i.vecLevel ≤ 1 := fun i hi => by
    simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ r.code).symm.trans hl1) i hi
  have hnames : ∀ f ∈ UpperLock.inames r.code, f ∈ tableFns r.tables := fun f hf => by
    simpa using List.all_eq_true.mp hic f hf
  have ht : TailOk (retBitsOf r) xregs (psOf (wipeKs (chunksA r.stack))) (gsAll (wipeKs (chunksA r.stack)))
      (wipeKs (chunksA r.stack)) :=
    { x0 := fun _ => mem_xregs _
      r11 := fun hk => by simp [psOf, hk]
      psOk := fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
      gsOk := fun q hq => by
        unfold gsAll at hq; split at hq
        · exact hq
        · exact List.mem_of_mem_erase hq
      gne := by unfold gsAll; split <;> simp [scratchRegs] }
  have hgk : ∀ q ∈ scratchRegs, q ∉ gsAll (wipeKs (chunksA r.stack)) → q ∉ psOf (wipeKs (chunksA r.stack)) →
      ∀ i ∈ instrs r.code, Taint.clobbers i q = false := fun q hq hg hp =>
    ((gsAll_cover _ q hq).elim (fun h => absurd h hg) (fun h => absurd h hp))
  have hres : ResOk r.code r.contract r.stack (wipeKs (chunksA r.stack)) (chunksA r.stack) := by
    rw [wipeKs_eq]; exact RScrub.resOk_allC _ _ (fun b hb => (hcv' b hb).2.2) hcs
  have hrb' : retBitsOf r ≤ 32 ∨ retBitsOf r = 64 := hrb
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  unfold retBitsOf at hrb' hp ht ⊢
  rw [e] at hv hp hr ⊢
  have key := Verified.scrubU (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv' (fun _ => hl1')
    (upperOk_lock hv.2.1 (fun s₁ s₂ h f hf => tables_pub_syms h f (hnames f hf)) hup)
    hrb' hp hr ht (.inl mem_xregs) (fun e => absurd e (by decide)) (fun _ _ e => absurd e (by decide)) hgk
    (fun s₁ s₂ h f hf => tables_pub_syms (contract_pub h) f (hnames f hf))
  exact ⟨key.1, key.2⟩

end VG.X86_64.Scrub
