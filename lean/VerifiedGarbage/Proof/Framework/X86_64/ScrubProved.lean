module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# The cleanup of the whole frame, and what the cleanup needs of the code (x86-64)

A function's code as emitted, its body and then its cleanup, is a named
definition in `Impl/` (`Impl.<Alg>.X86_64.Fn.<f>`), written with the
cleanup's literals (`Impl.Scrub.X86_64.scrubAll v rb n`,
`Impl/Scrub/X86_64/Fn.lean`). `verifiedScrubbedAll` states `VerifiedScrubbed`
of that code, the theorem a registration binds (`verified := .scrubbed …`);
`verifiedScrubbedSel`, of the selective cleanup `scrubSel v rb n rs`, is in
`ScrubSel.lean`.

What the cleanup needs of the code is one Boolean, `scrubSideG c stack rb v
vec ks cs` (its depth, the level of its vector instructions, that it leaves
MXCSR as two runs found it, that it calls indirectly only its tables'
functions), for code `c` with `stack` bytes of stack and a result of `rb`
bits, at the level `v`, with the granules `ks` of the chunks `cs` wiped: one
pass over the instructions (`sideI`) and that two runs along a path leave
the same MXCSR (`mxSameB`). The kernel evaluates it once when the theorem's
module is built (by default `lit_decide`), and `scrubSideG_ok` turns it into
what `Verified.scrubWith` takes. `scrubAll` needs nothing else of the code
but that its postcondition reads the memory on return only within its
buffers (`PostOut`). The stack, the result's bits and the level are the
literals of the code (`hn`, `hb`: `rfl`).
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

/-- The result's bits of `r`'s function. -/
abbrev retBitsOf {api : Api} (r : Unscrubbed api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

/-- The SSE registers the tail clears: all of them for code that may write
one (`vec`); otherwise `xmm0` if the wipe stores it (`ks` not empty). -/
def xsFor (vec : Bool) (ks : List Nat) : List XReg :=
  if vec then xregs else if ks = [] then [] else [.xmm0]

/-- The caller-saved registers the tail leaves as the code left them: those
it clears neither as `gs` nor for the wipe. -/
def keptG (ks : List Nat) (gs : List Reg) : List Reg :=
  scratchRegs.filter fun r => !gs.contains r && !(psOf ks).contains r

/-- What the scrub needs of an instruction: its vector registers are at a
level of at most `k`, it writes none unless the tail clears them all
(`vec`), and it writes none of the registers `kept`. -/
def sideI (k : Nat) (vec : Bool) (kept : List Reg) (i : Instr) : Bool :=
  decide (i.vecLevelR ≤ k) && (vec || !writesVec i) && kept.all fun r => !Taint.clobbers i r

end VG.X86_64.Scrub

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

/-! ## Any chunks, and code that leaves the same MXCSR along a path -/

/-- Whether two runs of `c` along the same path leave the same MXCSR if
they started with the same: it leaves a function of MXCSR on entry
(`mxClass`), or every `ldmxcsr` in it loads what `Mx.mx` follows. The
kernel evaluates the second only where the first fails. -/
noncomputable def mxSameB (c : Prog isa) : Bool := (mxClass c).isSome || (RScrub.Mx.mx c []).isSome

theorem mxSame_ofB {c : Prog isa} (h : mxSameB c = true) : MxSame c := by
  simp only [mxSameB, Bool.or_eq_true] at h
  rcases h with h | h
  · exact MxSame.of_fun (mxFun_of h)
  · exact RScrub.Mx.mxSame_of h

/-- What the tail needs of the registers it clears, from `sideI` of every
instruction: `TailOk`, that it clears every SSE register unless the code
writes none, that the code writes none of the registers it leaves, and the
level of the code's instructions. -/
theorem sideI_facts {c : Prog isa} {k : Nat} {vec : Bool} {ks : List Nat} {gs : List Reg} (rb : Nat)
    (hall : c.allInstrs (sideI k vec (keptG ks gs)) = true)
    (hgs : gs.all (scratchRegs.contains ·) = true) (hgne : (!gs.isEmpty) = true) :
    TailOk rb (xsFor vec ks) (psOf ks) gs ks ∧
      ((∀ x, x ∈ xsFor vec ks) ∨ ∀ i ∈ instrs c, writesVec i = false) ∧
      (∀ q ∈ scratchRegs, q ∉ gs → q ∉ psOf ks → ∀ i ∈ instrs c, Taint.clobbers i q = false) ∧
      ∀ i ∈ instrs c, i.vecLevelR ≤ k := by
  have hI : ∀ i ∈ instrs c, sideI k vec (keptG ks gs) i = true :=
    fun i hi => List.all_eq_true.mp ((Code.allInstrs_eq _ c).symm.trans hall) i hi
  have hgs' : ∀ q ∈ gs, q ∈ scratchRegs := fun q hq => by
    simpa using List.all_eq_true.mp hgs q hq
  have hps : ∀ q ∈ psOf ks, q ∈ scratchRegs := fun q hq => by
    unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { x0 := fun hk => by
          unfold xsFor; split
          · exact mem_xregs _
          · simp
        r11 := fun hk => by simp [psOf, hk]
        psOk := hps
        gsOk := hgs'
        gne := by
          intro e; rw [e] at hgne; simp at hgne }
  · cases hvec : vec
    · refine .inr fun i hi => ?_
      have h1 := hI i hi
      simp only [sideI, hvec, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h1
      exact h1.1.2
    · exact .inl fun x => by unfold xsFor; simp only [↓reduceIte]; exact mem_xregs x
  · intro q hq hng hnp i hi
    have h1 := hI i hi
    simp only [sideI, Bool.and_eq_true] at h1
    have hk : q ∈ keptG ks gs := List.mem_filter.mpr ⟨hq, by simp [hng, hnp]⟩
    simpa using List.all_eq_true.mp h1.2 q hk
  · intro i hi
    have h1 := hI i hi
    simp only [sideI, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1

/-- `scrubSide` for a stack wiped in the chunks `cs` (from the top), at any
level, of code that leaves the same MXCSR along a path (`mxSameB`): what
the cleanup needs of code `c` with `stack` bytes of stack and a result of
`rb` bits, scrubbed at the level `v` with the granules `ks` wiped and the
registers `gs` cleared, with the tables `ts`. One pass over the
instructions, and `mxSameB`; only the kernel evaluates it. -/
noncomputable def scrubSideG (c : Prog isa) (stack rb : Nat) (v : VecLevel) (vec : Bool) (ks cs : List Nat)
    (gs : List Reg) (ts : List (String × List FnTable)) : Bool :=
  decide (c.x86_64Depth ≤ stack) && decide (stack + 8 < 2 ^ 64) && cs.sum == stack &&
  cs.all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) &&
  (decide (rb ≤ 32) || rb == 64) && gs.all (scratchRegs.contains ·) && !gs.isEmpty &&
  mxSameB c && (decide (v ≠ .evex) || vec) &&
  c.allInstrs (sideI v.level vec (keptG ks gs)) && tablesCall c ts

/-- The chunks of `scrubSideG` sum to the stack, and each is one the wipe
takes. -/
theorem scrubSideG_cs {c : Prog isa} {stack rb : Nat} {v : VecLevel} {vec : Bool} {ks cs : List Nat}
    {gs : List Reg} {ts : List (String × List FnTable)} (hs : scrubSideG c stack rb v vec ks cs gs ts = true) :
    cs.sum = stack ∧ ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0 := by
  simp only [scrubSideG, Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨hs.1.1.1.1.1.1.1.1.2, fun b hb => of_decide_eq_true (List.all_eq_true.mp hs.1.1.1.1.1.1.1.2 b hb)⟩

/-- `r`'s code, scrubbed at the level `v` with the granules `ks` of the
chunks `cs` wiped and the registers `xsFor vec ks` and `gs` cleared, without
`mxFix` (`f` below `evex`), is verified and returns without secret residue,
given `scrubSideG`. -/
theorem scrubSideG_ok {api : Api} (r : Unscrubbed api target) (v f : VecLevel) (vec : Bool) (ks cs : List Nat)
    (gs : List Reg) (hs : scrubSideG r.code r.stack (retBitsOf r) v vec ks cs gs r.tables = true)
    (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks cs) (hne : f ≠ .evex) :
    Verified target (scrubWith v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks cs r.code f) r.contract ∧
      NoResidue (scrubWith v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks cs r.code f) r.contract
        (retBitsOf r) := by
  obtain ⟨hcs, hcv⟩ := scrubSideG_cs hs
  simp only [scrubSideG, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hst⟩, -⟩, -⟩, hrb⟩, hgs⟩, hgne⟩, hmx⟩, hxv⟩, hall⟩, hic⟩ := hs
  obtain ⟨ht, hxs, hgk, hlv⟩ := sideI_facts (retBitsOf r) hall hgs hgne
  have hxe : v = .evex → ∀ x, x ∈ xsFor vec ks := fun e x => by
    have hv : vec = true := hxv.resolve_left (fun h => h e)
    unfold xsFor; simp only [hv, ↓reduceIte]; exact mem_xregs x
  have hrb' : retBitsOf r ≤ 32 ∨ retBitsOf r = 64 := hrb
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  unfold retBitsOf at hrb' hp ht ⊢
  rw [e] at hv hp hr ⊢
  have key := Verified.scrubM (f := f) (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    hcs hst hcv hlv (fun _ => mxSame_ofB hmx) hrb' hp hr ht hxs hxe (fun _ _ e => absurd e hne) hgk
  exact ⟨key.1, key.2 (tablesCall_syms hic rfl)⟩

/-! ## The cleanup as part of the code -/

open VG.X86_64

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

/-- No instruction of `scrubKs v rb n ks c` writes the stack pointer if none
of `c`'s does: the clearing's own instructions do not (its frames are
`alloc` and `free`), so the registration's `spSafe` follows from its code's,
without evaluating the clearing with the code. -/
theorem scrubKs_spSafe {v : VecLevel} {rb n : Nat} {ks : List Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrubKs v rb n ks c).all (fun i => !isa.writesSp i) = true :=
  scrubWith_spSafe v rb _ _ _ _ _
    (fun q hq => by unfold psOf at hq; split at hq <;> simp_all [scratchRegs])
    (fun q hq => by
      unfold gsAll at hq; split at hq
      · exact hq
      · exact List.mem_of_mem_erase hq) h

end VG.X86_64.Scrub
