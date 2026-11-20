module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub

/-!
# The cleanup as part of the code (x86-64)

A function's code as emitted, its body and then its cleanup, is a named
definition in `Impl/` (`Impl.<Alg>.X86_64.Fn.<f>`), written with the
cleanup's literals (`Impl.Scrub.X86_64.scrubAll v rb n` or
`scrubSel v rb n rs`, `Impl/Scrub/X86_64/Fn.lean`). `verifiedScrubbedAll`
and `verifiedScrubbedSel` state `VerifiedScrubbed` of that code, the theorem
a registration binds (`verified := .scrubbed …`).

What the cleanup needs of the code is one Boolean, `scrubSideG` (its depth,
the level of its vector instructions, that it leaves MXCSR as two runs found
it, that it calls indirectly only its tables' functions), which the kernel
evaluates once when the theorem's module is built (by default `lit_decide`).
`scrubAll` needs nothing else of the code but that its postcondition reads
the memory on return only within its buffers (`PostOut`). `scrubSel` also
needs the residue analysis of the code (`RTaint.rtaint`) to end with every
byte of the stack it may leave different in two runs inside the runs `rs`
(`hres`, by `taint_decide`). The stack, the result's bits and the level are
the literals of the code (`hn`, `hb`: `rfl`).
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

theorem wipeKs_eq : ∀ cs : List Nat, wipeKs cs = allKs cs
  | [] => rfl
  | b :: bs => by simp only [wipeKs, allKs, wipeKs_eq bs]

/-- `r`'s code followed by `scrubKs v rb n ks`: the clearing of every vector
register at the level `v`, of every caller-saved register but the result's
`rb` bits and of the granules `ks` of its stack (in `chunksA n`), meets
`r`'s contract in constant time and returns without secret residue, given
`scrubSideG` and that two runs leave the same bytes in its stack but those
granules (`hres`). -/
theorem verifiedScrubbedKs {api : Api} (r : Unscrubbed api target) (v : VecLevel) (ks : List Nat)
    {n rb : Nat} (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks (chunksA r.stack))
    (hs : scrubSideG r.code r.stack (retBitsOf r) v true ks (chunksA r.stack) (gsAll ks) r.tables = true)
    (hn : r.stack = n) (hb : retBitsOf r = rb) :
    VerifiedScrubbed target (scrubKs v rb n ks r.code) r.contract rb := by
  subst hn hb
  have h := scrubSideG_ok r v .avx true ks (chunksA r.stack) (gsAll ks) hs hpost hres (by decide)
  exact ⟨h.1, h.2⟩

/-- `r`'s code followed by `scrubAll v rb n`, which wipes every granule of
its `n` bytes of stack, meets `r`'s contract in constant time and returns
without secret residue: for any code whose postcondition reads the memory
on return only within its buffers (`hpost`), given `scrubSideG`. -/
theorem verifiedScrubbedAll {api : Api} (r : Unscrubbed api target) (v : VecLevel) {n rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r))
    (hs : scrubSideG r.code r.stack (retBitsOf r) v true (wipeKs (chunksA r.stack)) (chunksA r.stack)
      (gsAll (wipeKs (chunksA r.stack))) r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hn : r.stack = n := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll v rb n r.code) r.contract rb := by
  subst hn
  obtain ⟨hcs, hcv⟩ := scrubSideG_cs hs
  have hres : ResOk r.code r.contract r.stack (wipeKs (chunksA r.stack)) (chunksA r.stack) := by
    rw [wipeKs_eq]; exact RScrub.resOk_allC _ _ (fun b hb => (hcv b hb).2.2) hcs
  exact verifiedScrubbedKs r v _ hpost hres hs rfl hb

/-- `r`'s code followed by `scrubSel v rb n rs`, which wipes only the runs
`rs` of granules of its `n` bytes of stack, meets `r`'s contract in
constant time and returns without secret residue, given `scrubSideG` and
the residue analysis of the code (`hc`, by `taint_decide`), from its buffers'
bytes `pubs` known public (`hpub`). -/
theorem verifiedScrubbedSel {api : Api} (r : Unscrubbed api target) (v : VecLevel) (rs : List (Nat × Nat))
    {code : Prog isa} {n rb : Nat} (hpost : PostOut r.contract (retBitsOf r)) {pubs : List (Nat × Nat × Nat)}
    (hpub : RScrub.PubOk r.contract pubs) {h : VG.Taint.Hint RTaint.FT}
    (hc : (VG.Taint.check RTaint.rtaint (RScrub.init api.sig n pubs) code h).any
      (RScrub.resOkF · n (runKs rs) (chunksA n)) = true)
    (hs : scrubSideG r.code r.stack (retBitsOf r) v true (runKs rs) (chunksA r.stack)
      (gsAll (runKs rs)) r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hfit : RScrub.pubsFit api.sig pubs = true := by decide)
    (hcode : r.code = code := by rfl) (hn : r.stack = n := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubSel v rb n rs code) r.contract rb := by
  subst hcode hn
  obtain ⟨hcs, -⟩ := scrubSideG_cs hs
  have hres : ResOk r.code r.contract r.stack (runKs rs) (chunksA r.stack) := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpub
    rw [e] at hv hp ⊢
    exact RScrub.resOk_of_check (ScrubAbi.of r.consts api.sig r.tables) hv hcs hfit hp (RScrub.any_resOkB hc)
  exact verifiedScrubbedKs r v _ hpost hres hs rfl hb

/-- No instruction of `scrubKs v rb n ks c` writes the stack pointer if none
of `c`'s does: the clearing's own instructions do not (its frames are
`alloc` and `free`), so the registration's `spSafe` follows from its code's,
without evaluating the clearing with the code. -/
theorem scrubKs_spSafe {v : VecLevel} {rb n : Nat} {ks : List Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubKs v rb n ks c).all (fun i => !isa.writesSp i) = true :=
  scrub_spSafe v rb _ _ _ _ _
    (fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs])
    (fun q hq => by
      unfold gsAll at hq; split at hq
      · exact hq
      · exact List.mem_of_mem_erase hq) h

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.Impl.Scrub.X86_64 VG.X86_64.RTaint

/-- `keepFor`, for the chunks `chunksA stack` of `scrubSel`, as the runs of
granules it wipes. -/
def keepRuns (sig : Sig) (stack : Nat) (code : Prog isa) (pubs : List (Nat × Nat × Nat) := []) :
    List (Nat × Nat) :=
  let ks := match VG.Taint.hint rtaint 256 (init sig stack pubs) code with
    | some (τ, _) => keepOf τ.sec (chunksA stack)
    | none => []
  (ks.mergeSort (· ≤ ·)).foldr (fun k acc => match acc with
    | (o, m) :: rest => if k + 16 = o then (k, m + 1) :: rest else (k, 1) :: acc
    | [] => [(k, 1)]) []

end VG.X86_64.RScrub
