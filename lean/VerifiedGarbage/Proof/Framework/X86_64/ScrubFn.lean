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

/-- What the cleanup `scrubKs v rb n ks` needs of its literals alone, the
stack `n` of the code and the result's bits `rb`: the chunks `chunksA n`
are ones the wipe takes, and the result fits the clearing of `rax`'s upper
bits. -/
def litSide (n rb : Nat) : Bool :=
  decide (n + 8 < 2 ^ 64) && (chunksA n).sum == n &&
  (chunksA n).all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) && (decide (rb ≤ 32) || rb == 64)

theorem gsAll_cover (ks : List Nat) : ∀ q ∈ scratchRegs, q ∈ gsAll ks ∨ q ∈ psOf ks := by
  intro q hq
  unfold gsAll psOf
  by_cases hk : ks = []
  · simp only [hk, ↓reduceIte]; exact .inl hq
  · simp only [hk, ↓reduceIte]
    by_cases hr : q = .r11
    · exact .inr (by simp [hr])
    · exact .inl ((List.mem_erase_of_ne hr).mpr hq)

/-- No instruction of `c` loads MXCSR, so two runs of it leave the MXCSR
they started with. -/
theorem mxSame_of_noLoad {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) : MxSame c :=
  MxSame.of_fun ⟨id, fun _ _ _ e => Exec.mxcsr (fun i hi => by
    simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ c).symm.trans h) i hi) e⟩

/-- `verifiedScrubbedKs`, from what the cleanup needs of the code one fact
at a time rather than as `scrubSideG`: its depth (`hd`), the level of its
vector instructions (`hlv`), that it leaves MXCSR as two runs found it
(`hmx`) and that it calls indirectly only its tables' functions (`hic`).
For code generic over an implementation it calls, whose facts follow from
the implementation's own (`ScrubCall.lean`), without evaluating it with
the code. -/
theorem verifiedScrubbedKsF {api : Api} (r : Unscrubbed api target) (v : VecLevel) (ks : List Nat)
    {n rb : Nat} (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks (chunksA r.stack))
    (hd : r.code.x86_64Depth ≤ r.stack)
    (hlv : r.code.allInstrs (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : MxSame r.code) (hic : tablesCall r.code r.tables = true)
    (hl : litSide r.stack (retBitsOf r) = true)
    (hn : r.stack = n) (hb : retBitsOf r = rb) :
    VerifiedScrubbed target (scrubKs v rb n ks r.code) r.contract rb := by
  subst hn hb
  simp only [litSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
  obtain ⟨⟨⟨hst, hcs⟩, hcv⟩, hrb⟩ := hl
  have hcv' : ∀ b ∈ chunksA r.stack, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
    fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb)
  have hlv' : ∀ i ∈ instrs r.code, i.vecLevelR ≤ v.level := fun i hi => by
    simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ r.code).symm.trans hlv) i hi
  have ht : TailOk (retBitsOf r) xregs (psOf ks) (gsAll ks) ks :=
    { x0 := fun _ => mem_xregs _
      r11 := fun hk => by simp [psOf, hk]
      psOk := fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
      gsOk := fun q hq => by
        unfold gsAll at hq; split at hq
        · exact hq
        · exact List.mem_of_mem_erase hq
      gne := by unfold gsAll; split <;> simp [scratchRegs] }
  have hgk : ∀ q ∈ scratchRegs, q ∉ gsAll ks → q ∉ psOf ks → ∀ i ∈ instrs r.code,
      Taint.clobbers i q = false := fun q hq hg hp =>
    ((gsAll_cover ks q hq).elim (fun h => absurd h hg) (fun h => absurd h hp))
  have hrb' : retBitsOf r ≤ 32 ∨ retBitsOf r = 64 := hrb
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  unfold retBitsOf at hrb' hp ht ⊢
  rw [e] at hv hp hr ⊢
  have key := Verified.scrubM (f := .avx) (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv' hlv' (fun _ => hmx) hrb' hp hr ht (.inl mem_xregs) (fun _ => mem_xregs)
    (fun _ _ e => absurd e (by decide)) hgk
  exact ⟨key.1, key.2 (tablesCall_syms hic rfl)⟩

/-- `verifiedScrubbedKsF` for `scrubAll v rb n`, which wipes every granule
of the stack: for code generic over an implementation it calls. -/
theorem verifiedScrubbedAllF {api : Api} (r : Unscrubbed api target) (v : VecLevel) {n rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r))
    (hd : r.code.x86_64Depth ≤ r.stack)
    (hlv : r.code.allInstrs (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : MxSame r.code) (hic : tablesCall r.code r.tables = true)
    (hl : litSide r.stack (retBitsOf r) = true := by decide)
    (hn : r.stack = n := by rfl) (hb : retBitsOf r = rb := by rfl) :
    VerifiedScrubbed target (scrubAll v rb n r.code) r.contract rb := by
  have hl' := hl
  simp only [litSide, Bool.and_eq_true, beq_iff_eq] at hl'
  have hres : ResOk r.code r.contract r.stack (wipeKs (chunksA r.stack)) (chunksA r.stack) := by
    rw [wipeKs_eq]
    exact RScrub.resOk_allC _ _ (fun b hb => (of_decide_eq_true (List.all_eq_true.mp hl'.1.2 b hb)).2.2)
      hl'.1.1.2
  subst hn
  exact verifiedScrubbedKsF r v _ hpost hres hd hlv hmx hic hl rfl hb

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
