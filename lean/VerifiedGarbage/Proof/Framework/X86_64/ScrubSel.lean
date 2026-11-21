module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved

/-!
# The selective cleanup (x86-64)

`verifiedScrubbedSel` states `VerifiedScrubbed` of code followed by
`Impl.Scrub.X86_64.scrubSel v rb n rs`, which wipes only the runs `rs` of
granules of its `n` bytes of stack: the theorem a registration binds
(`verified := .scrubbed …`), as `verifiedScrubbedAll` (`ScrubProved.lean`)
is of `scrubAll`. Beside `scrubSideG`, it needs the residue analysis of the
code (`RTaint.rtaint`) to end with every byte of the stack it may leave
different in two runs inside the runs `rs` (`hc`, by `taint_decide`).
`SelScrub` packages both for code generic over a variant, whose analysis is
evaluated once where the implementation is defined, and `RScrub.keepRuns`
finds the runs from the analysis.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

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

/-- What the cleanup `scrubSel level rb stack runs` of `code` needs of it,
for code generic over an implementation it calls (a variant), whose analysis
is evaluated where the implementation is defined, once: the level of its
vector registers, the runs of granules that may hold secrets, the residue
analysis ending with secrets only there (`ok`, from `SelScrub.ok_of` by
`taint_decide`), and the cleanup's other conditions (`side`, by
`lit_decide`). -/
structure SelScrub (sig : Sig) (stack rb : Nat) (code : Prog isa) where
  level : VecLevel
  runs : List (Nat × Nat)
  ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init sig stack []) code h).any
      (RScrub.resOkB · stack (runKs runs) (chunksA stack)) = true
  side : scrubSideG code stack rb level true (runKs runs) (chunksA stack) (gsAll (runKs runs)) [] = true

/-- `SelScrub.ok`, from the analysis with a hint `taint_decide` finds,
ending as `resOkF` checks (which the kernel evaluates faster). -/
theorem SelScrub.ok_of {sig : Sig} {stack : Nat} {code : Prog isa} (runs : List (Nat × Nat))
    {h : VG.Taint.Hint RTaint.FT}
    (hc : (VG.Taint.check RTaint.rtaint (RScrub.init sig stack []) code h).any
      (RScrub.resOkF · stack (runKs runs) (chunksA stack)) = true) :
    ∃ h : VG.Taint.Hint RTaint.FT,
      (VG.Taint.check RTaint.rtaint (RScrub.init sig stack []) code h).any
        (RScrub.resOkB · stack (runKs runs) (chunksA stack)) = true :=
  ⟨h, RScrub.any_resOkB hc⟩

/-- `r`'s code followed by `scrubSel a.level rb n a.runs`, from what the
implementation it calls proves of it (`a`). -/
theorem SelScrub.scrubbed {api : Api} (r : Unscrubbed api target) {n rb : Nat}
    (a : SelScrub api.sig n rb r.code) (hpost : PostOut r.contract (retBitsOf r))
    (hn : r.stack = n := by rfl) (hb : retBitsOf r = rb := by rfl) (ht : r.tables = [] := by rfl) :
    VerifiedScrubbed target (scrubSel a.level rb n a.runs r.code) r.contract rb := by
  subst hn hb
  have hs := a.side
  rw [← ht] at hs
  obtain ⟨hcs, -⟩ := scrubSideG_cs hs
  have hres : ResOk r.code r.contract r.stack (runKs a.runs) (chunksA r.stack) := by
    obtain ⟨h, hc⟩ := a.ok
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp : RScrub.PubOk r.contract [] := RScrub.pubOk_nil _
    rw [e] at hv hp ⊢
    exact RScrub.resOk_of_check (ScrubAbi.of r.consts api.sig r.tables) hv hcs rfl hp hc
  exact verifiedScrubbedKs r a.level _ hpost hres hs rfl rfl

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
