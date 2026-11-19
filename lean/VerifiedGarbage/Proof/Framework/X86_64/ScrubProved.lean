module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPart
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Scrubbed code registered with its facts proved (x86-64)

`scrubResOf`, `scrubOf` and `scrubAllOf`: what `Scrub.scrubReg`,
`RScrub.withScrub` and `Scrub.withScrubAll` register, with nothing left for
the emitter to work out; and likewise `scrubAllFOf` and `scrubResFOf`
(`RScrub.withScrubAllF`, and the second routes of `withScrubAllM`,
`withScrubM` and `withScrubResM`), `scrubAllCOf` and `scrubResCOf`
(`withScrubAllC`, `withScrubResC`), `scrubResCROf` and `scrubResCRHOf`
(`withScrubResCR`, `withScrubResCRH`) and `scrubUpOf` (`Scrub.withUp`, the
second route of `withScrubAllUp`). Where a wrapper chose between two of
these by evaluating the code, the registration names the one it means. The level the tail clears the vector registers at,
whether it clears them all (`vec`) and the general-purpose registers it
clears are arguments (literals at the call site), and what the scrub needs
of the code is one Boolean (`scrubSide`) whose proof the call site gives,
checked by the kernel when its module is built: the registration is a record
whose code is `scrub` of literals and the code, and evaluating it inspects
no code.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

/-- The result's bits of `r`'s function. -/
abbrev retBitsOf {api : Api} (r : Unscrubbed api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

/-- The SSE registers the tail clears: all of them for code that may write
one (`vec`); otherwise `xmm0` if the wipe stores it (`ks` not empty), as
`xsOf` finds them from the code. -/
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

/-- What `scrubResOf` needs of code `c` with `stack` bytes of stack and a
result of `rb` bits, scrubbed at the level `v` with the granules `ks` wiped
and the registers `gs` cleared, with the tables `ts`: the conditions that
`RScrub.withScrub` and `Scrub.withScrubAll` decided when the registration
was evaluated, and that the registers the tail clears are those the code
(callees included) may write. One pass over the instructions; only the
kernel evaluates it (`Code.allInstrs`). -/
noncomputable def scrubSide (c : Prog isa) (stack rb : Nat) (v : VecLevel) (vec : Bool) (ks : List Nat)
    (gs : List Reg) (ts : List (String × List FnTable)) : Bool :=
  decide (c.x86_64Depth ≤ stack) && decide (stack + 8 < 2 ^ 64) && stack % 8 == 0 &&
  (decide (rb ≤ 32) || rb == 64) && gs.all (scratchRegs.contains ·) && !gs.isEmpty &&
  (decide (v = .evex) || (mxClass c).isSome) &&
  c.allInstrs (sideI v.level vec (keptG ks gs)) && tablesCall c ts

/-- `r`'s code, scrubbed at the level `v` with the granules `ks` wiped and
the registers `xsFor vec ks` and `gs` cleared, is verified and returns
without secret residue, given `scrubSide` and the two facts of the level
`evex`. -/
theorem scrubSide_ok {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (ks : List Nat)
    (gs : List Reg) (hs : scrubSide r.code r.stack (retBitsOf r) v vec ks gs r.tables = true)
    (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hxe : v = .evex → vec = true)
    (hev : ∀ p : Addr, (chunks r.stack).sum ≤ p.toNat → EvexOk v ks (chunks r.stack) p) :
    Verified target (scrub v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks (chunks r.stack) r.code) r.contract ∧
      NoResidue (scrub v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks (chunks r.stack) r.code) r.contract
        (retBitsOf r) := by
  simp only [scrubSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hd, hst⟩, h8⟩, hrb⟩, hgs⟩, hgne⟩, hmx⟩, hall⟩, hic⟩ := hs
  have hI : ∀ i ∈ instrs r.code, sideI v.level vec (keptG ks gs) i = true :=
    fun i hi => List.all_eq_true.mp ((Code.allInstrs_eq _ r.code).symm.trans hall) i hi
  have hgs' : ∀ q ∈ gs, q ∈ scratchRegs := fun q hq => by
    simpa using List.all_eq_true.mp hgs q hq
  have hps : ∀ q ∈ psOf ks, q ∈ scratchRegs := fun q hq => by
    unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
  have ht : TailOk (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks :=
    { x0 := fun hk => by
        unfold xsFor; split
        · exact mem_xregs _
        · simp
      r11 := fun hk => by simp [psOf, hk]
      psOk := hps
      gsOk := hgs'
      gne := by
        intro e; rw [e] at hgne; simp at hgne }
  have hxs : (∀ x, x ∈ xsFor vec ks) ∨ ∀ i ∈ instrs r.code, writesVec i = false := by
    cases hvec : vec
    · refine .inr fun i hi => ?_
      have h1 := hI i hi
      simp only [sideI, hvec, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h1
      exact h1.1.2
    · exact .inl fun x => by unfold xsFor; simp only [↓reduceIte]; exact mem_xregs x
  have hxe' : v = .evex → ∀ x, x ∈ xsFor vec ks := fun e x => by
    unfold xsFor; simp only [hxe e, ↓reduceIte]; exact mem_xregs x
  have hgk : ∀ q ∈ scratchRegs, q ∉ gs → q ∉ psOf ks → ∀ i ∈ instrs r.code, Taint.clobbers i q = false := by
    intro q hq hng hnp i hi
    have h1 := hI i hi
    simp only [sideI, Bool.and_eq_true] at h1
    have hk : q ∈ keptG ks gs := List.mem_filter.mpr ⟨hq, by simp [hng, hnp]⟩
    simpa using List.all_eq_true.mp h1.2 q hk
  have hlv : ∀ i ∈ instrs r.code, i.vecLevelR ≤ v.level := fun i hi => by
    have h1 := hI i hi
    simp only [sideI, Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1
  have hmx' : v ≠ .evex → MxSame r.code := fun hne =>
    MxSame.of_fun (mxFun_of (hmx.resolve_left hne))
  have h8' : r.stack % 8 = 0 := h8
  have hrb' : retBitsOf r ≤ 32 ∨ retBitsOf r = 64 := hrb
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  unfold retBitsOf at hrb' hp ht ⊢
  rw [e] at hv hp hr ⊢
  have key := Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8') hlv hmx' hrb' hp hr ht hxs hxe' hev hgk
  exact ⟨key.1, key.2 (tablesCall_syms hic rfl)⟩

/-- `r`, scrubbed at the level `v` with the granules `ks` wiped and the
registers `xsFor vec ks` and `gs` cleared, returning without secret residue,
given `scrubSide`, proved where the registration is defined, and that two
runs leave the same bytes in its stack but those granules (`hres`):
`Scrub.scrubReg`, and `RScrub.withScrubRes`, with the level and the
registers stated rather than found when the registration is evaluated. -/
def scrubResOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (ks : List Nat)
    (gs : List Reg) (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hs : scrubSide r.code r.stack (retBitsOf r) v vec ks gs r.tables = true)
    (hne : v ≠ .evex := by decide) (hw : r.written = [] := by rfl) : Registration api target :=
  have hok := scrubSide_ok r v vec ks gs hs hpost hres (fun e => absurd e hne) (fun _ _ e => absurd e hne)
  have hgs : ∀ q ∈ gs, q ∈ scratchRegs := fun q hq => by
    simp only [scrubSide, Bool.and_eq_true] at hs
    simpa using List.all_eq_true.mp hs.1.1.1.1.2 q hq
  have hps : ∀ q ∈ psOf ks, q ∈ scratchRegs := fun q hq => by
    unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks (chunks r.stack) r.code
    contract := r.contract
    verified := .scrubbed <| .abi ⟨hok.1, hok.2⟩
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ hps hgs r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.Impl.Scrub.X86_64 VG.X86_64.Scrub

/-- `r`, returning without secret residue, given the residue analysis of its
code (`Analysed`): `withScrub`, with the level and the registers its tail
clears stated and what it needs of the code proved (`Scrub.scrubSide`)
rather than found when the registration is evaluated. -/
def scrubOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (gs : List Reg)
    (hpost : PostOut r.contract (retBitsOf r))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Analysed api.sig r.stack pubs r.code)
    (hs : scrubSide r.code r.stack (retBitsOf r) v vec a.ks gs r.tables = true)
    (hfit : pubsFit api.sig pubs = true := by decide)
    (hne : v ≠ .evex := by decide) (hw : r.written = [] := by rfl) : Registration api target :=
  scrubResOf r v vec a.ks gs hpost (by obtain ⟨_, hc⟩ := a.ok; exact resOk_reg r a.ks hfit hpub hc) hs hne hw

end VG.X86_64.RScrub

namespace VG.X86_64.Scrub

open VG.Impl.Scrub.X86_64

/-- `scrubSide`, for code scrubbed with every granule of its stack wiped,
and what the level `evex` needs: every SSE register cleared and 16 bytes of
stack. -/
noncomputable def scrubAllSide (c : Prog isa) (stack rb : Nat) (v : VecLevel) (vec : Bool) (gs : List Reg)
    (ts : List (String × List FnTable)) : Bool :=
  scrubSide c stack rb v vec (allKs (chunks stack)) gs ts &&
  (decide (v ≠ .evex) || (vec && decide (16 ≤ stack)))

/-- `r`, scrubbed with every granule of its stack wiped, returning without
secret residue: `withScrubAll`, with the level and the registers its tail
clears stated and what it needs of the code proved (`scrubAllSide`) rather
than found when the registration is evaluated. For code the residue
analysis does not follow. -/
def scrubAllOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (gs : List Reg)
    (hpost : PostOut r.contract (retBitsOf r))
    (hs : scrubAllSide r.code r.stack (retBitsOf r) v vec gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  have hs1 : scrubSide r.code r.stack (retBitsOf r) v vec (allKs (chunks r.stack)) gs r.tables = true := by
    simp only [scrubAllSide, Bool.and_eq_true] at hs; exact hs.1
  have h8 : r.stack % 8 = 0 := by
    simp only [scrubSide, Bool.and_eq_true, beq_iff_eq] at hs1; exact hs1.1.1.1.1.1.1.2
  have hst : r.stack + 8 < 2 ^ 64 := by
    simp only [scrubSide, Bool.and_eq_true, decide_eq_true_eq] at hs1; exact hs1.1.1.1.1.1.1.1.2
  have hE : v = .evex → vec = true ∧ 16 ≤ r.stack := fun e => by
    simp only [scrubAllSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hs
    rcases hs.2 with h | h
    · exact absurd e h
    · exact h
  have hok := scrubSide_ok r v vec (allKs (chunks r.stack)) gs hs1 hpost (resOk_all _ _ h8)
    (fun e => (hE e).1)
    (fun p hp e => evexOk_all v (fun b hb => (chunks_valid h8 b hb).2.2)
      (by rw [chunks_sum]; exact (hE e).2) (by rw [chunks_sum]; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ 8) hst) hp e)
  have hgs : ∀ q ∈ gs, q ∈ scratchRegs := fun q hq => by
    simp only [scrubSide, Bool.and_eq_true] at hs1
    simpa using List.all_eq_true.mp hs1.1.1.1.1.2 q hq
  have hps : ∀ q ∈ psOf (allKs (chunks r.stack)), q ∈ scratchRegs := fun q hq => by
    unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (retBitsOf r) (xsFor vec (allKs (chunks r.stack))) (psOf (allKs (chunks r.stack))) gs
      (allKs (chunks r.stack)) (chunks r.stack) r.code
    contract := r.contract
    verified := .scrubbed <| .abi ⟨hok.1, hok.2⟩
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ hps hgs r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

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
`scrubGOf` needs of code `c` with `stack` bytes of stack and a result of
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
    Verified target (scrub v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks cs r.code f) r.contract ∧
      NoResidue (scrub v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks cs r.code f) r.contract
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

/-- `r`, scrubbed at the level `v` with the granules `ks` of the chunks `cs`
of its stack wiped and the registers `xsFor vec ks` and `gs` cleared,
without `mxFix` (`f` below `evex`), returning without secret residue, given
`scrubSideG`, proved where the registration is defined, and that two runs
leave the same bytes in its stack but those granules (`hres`). -/
def scrubGOf {api : Api} (r : Unscrubbed api target) (v f : VecLevel) (vec : Bool) (ks cs : List Nat)
    (gs : List Reg) (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks cs)
    (hs : scrubSideG r.code r.stack (retBitsOf r) v vec ks cs gs r.tables = true)
    (hne : f ≠ .evex := by decide) (hw : r.written = [] := by rfl) : Registration api target :=
  have hok := scrubSideG_ok r v f vec ks cs gs hs hpost hres hne
  have hgs : ∀ q ∈ gs, q ∈ scratchRegs := fun q hq => by
    simp only [scrubSideG, Bool.and_eq_true] at hs
    simpa using List.all_eq_true.mp hs.1.1.1.1.1.2 q hq
  have hps : ∀ q ∈ psOf ks, q ∈ scratchRegs := fun q hq => by
    unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (retBitsOf r) (xsFor vec ks) (psOf ks) gs ks cs r.code f
    contract := r.contract
    verified := .scrubbed <| .abi ⟨hok.1, hok.2⟩
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ hps hgs r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

/-- `r`, scrubbed with the granules `ks` of its stack wiped in the chunks
`cs` (from the top), returning without secret residue: `RScrub.withScrubResC`,
with the level and the registers its tail clears stated and what it needs of
the code proved (`scrubSideG`) rather than found when the registration is
evaluated. -/
def scrubResCOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (ks cs : List Nat)
    (gs : List Reg) (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks cs)
    (hs : scrubSideG r.code r.stack (retBitsOf r) v vec ks cs gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hne : v ≠ .evex := by decide) (hw : r.written = [] := by rfl) : Registration api target :=
  scrubGOf r v v vec ks cs gs hpost hres hs hne hw

/-- `r`, scrubbed with every granule of its stack wiped in the chunks `cs`
(from the top), returning without secret residue: `RScrub.withScrubAllC`,
with the level and the registers its tail clears stated and what it needs of
the code proved (`scrubSideG`). -/
def scrubAllCOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (gs : List Reg)
    (hpost : PostOut r.contract (retBitsOf r)) (cs : List Nat)
    (hs : scrubSideG r.code r.stack (retBitsOf r) v vec (allKs cs) cs gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hne : v ≠ .evex := by decide) (hw : r.written = [] := by rfl) : Registration api target :=
  scrubGOf r v v vec (allKs cs) cs gs hpost
    (RScrub.resOk_allC _ _ (fun b hb => ((scrubSideG_cs hs).2 b hb).2.2) (scrubSideG_cs hs).1) hs hne hw

/-- `r`, scrubbed with the granules `ks` of its stack wiped and no `mxFix`,
at any level, returning without secret residue: the second route of
`RScrub.withScrubResM` (and of `withScrubM`), for code that leaves the same
MXCSR along a path, with the level and the registers its tail clears stated
and what it needs of the code proved (`scrubSideG`). The first route is
`scrubResOf`'s: the registration names the one it means. -/
def scrubResFOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (ks : List Nat)
    (gs : List Reg) (hpost : PostOut r.contract (retBitsOf r))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hs : scrubSideG r.code r.stack (retBitsOf r) v vec ks (chunks r.stack) gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  scrubGOf r v .avx vec ks (chunks r.stack) gs hpost hres hs (by decide) hw

/-- `r`, scrubbed with every granule of its stack wiped and no `mxFix`, at
any level, returning without secret residue: `RScrub.withScrubAllF`, which
is `withScrubAllR`'s and the first route of `withScrubAllM`, for code that
leaves the same MXCSR along a path, with the level and the registers its
tail clears stated and what it needs of the code proved (`scrubSideG`).
`withScrubAllM`'s other route is `scrubAllOf`'s: the registration names the
one it means. -/
def scrubAllFOf {api : Api} (r : Unscrubbed api target) (v : VecLevel) (vec : Bool) (gs : List Reg)
    (hpost : PostOut r.contract (retBitsOf r))
    (hs : scrubSideG r.code r.stack (retBitsOf r) v vec (allKs (chunks r.stack)) (chunks r.stack) gs
      r.tables = true := by (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  scrubGOf r v .avx vec (allKs (chunks r.stack)) (chunks r.stack) gs hpost
    (RScrub.resOk_allC _ _ (fun b hb => ((scrubSideG_cs hs).2 b hb).2.2) (scrubSideG_cs hs).1) hs (by decide) hw

/-! ## Only the registers two runs may not agree on -/

/-- What `scrubResCROf` needs of code `c`, scrubbed at the level `v` with
the granules `ks` of the chunks `cs` wiped and the registers `xs` and `gs`
cleared: the conditions that `RScrub.withScrubResCR` decided when the
registration was evaluated. Only the kernel evaluates it. -/
noncomputable def scrubSideR (c : Prog isa) (stack rb : Nat) (v : VecLevel) (ks cs : List Nat) (xs : List XReg)
    (gs : List Reg) (ts : List (String × List FnTable)) : Bool :=
  cs.sum == stack && cs.all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) &&
  decide (c.x86_64Depth ≤ stack) && decide (stack + 8 < 2 ^ 64) &&
  c.allInstrs (fun i => decide (i.vecLevelR ≤ v.level)) && (mxClass c).isSome &&
  (decide (rb ≤ 32) || rb == 64) && tailOkB xs gs ks && tablesCall c ts

/-- `r`, scrubbed with the granules `ks` of the chunks `cs` wiped and only
the SSE registers `xs` and the caller-saved registers `gs` cleared, those
two runs may not agree on at the end (`hregs`), returning without secret
residue: `RScrub.withScrubResCR`, with the level stated and what it needs of
the code proved (`scrubSideR`) rather than found when the registration is
evaluated. -/
def scrubResCROf {api : Api} (r : Unscrubbed api target) (v : VecLevel)
    (hpost : PostOut r.contract (retBitsOf r))
    (ks cs : List Nat) (hres : ResOk r.code r.contract r.stack ks cs)
    (xs : List XReg) (gs : List Reg) (hregs : RegsOk r.code r.contract xs (psOf ks) gs)
    (hs : scrubSideR r.code r.stack (retBitsOf r) v ks cs xs gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hne : v ≠ .evex := by decide) (hw : r.written = [] := by rfl) : Registration api target :=
  have h : (cs.sum = r.stack ∧ (∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) ∧ r.code.x86_64Depth ≤ r.stack ∧
      r.stack + 8 < 2 ^ 64) ∧ r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true ∧
      (mxClass r.code).isSome = true ∧ (retBitsOf r ≤ 32 ∨ retBitsOf r = 64) ∧
      tailOkB xs gs ks = true ∧ tablesCall r.code r.tables = true := by
    simp only [scrubSideR, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hcs, hcv⟩, hd⟩, hst⟩, hlv⟩, hmx⟩, hrb⟩, ht⟩, hic⟩ := hs
    exact ⟨⟨hcs, fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb), hd, hst⟩,
      Code.all_of_allInstrs hlv, hmx, hrb, ht, hic⟩
  have ht := tailOk_ofB (retBitsOf r) h.2.2.2.2.1
  have hok := scrubCodeMCR_ok r v ks cs xs gs h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 h.2.1 h.2.2.1 h.2.2.2.1 hpost hres hw hne
    ht hregs
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub v (retBitsOf r) xs (psOf ks) gs ks (wipeCs ks cs) r.code
    contract := r.contract
    verified := .scrubbed <| .abi ⟨hok.1, hok.2 h.2.2.2.2.2⟩
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ ht.psOk ht.gsOk r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

/-- `Code.all p` fails where `Code.allInstrs p` does. -/
theorem all_false_of_allInstrs {p : Instr → Bool} {c : Prog isa} (h : c.allInstrs p = false) :
    c.all p = false := by
  cases hc : c.all p
  · rfl
  · have h' : (instrs c).all p = true := List.all_eq_true.mpr fun i hi => Code.all_instrs hc i hi
    rw [← Code.allInstrs_eq, h] at h'
    exact absurd h' (by decide)

/-- `scrubSideR` for `scrubResCRHOf`: at the level `avx`, of code that
writes a vector register. -/
noncomputable def scrubSideRH (c : Prog isa) (stack rb : Nat) (ks cs : List Nat) (xs : List XReg)
    (gs : List Reg) (ts : List (String × List FnTable)) : Bool :=
  cs.sum == stack && cs.all (fun b => decide (0 < b ∧ b < 4096 ∧ b % 8 = 0)) &&
  decide (c.x86_64Depth ≤ stack) && decide (stack + 8 < 2 ^ 64) && (mxClass c).isSome &&
  (decide (rb ≤ 32) || rb == 64) && tailOkB xs gs ks && !c.allInstrs (fun i => !writesVec i) &&
  tablesCall c ts

/-- `scrubResCROf` for code that writes `zmm16`–`zmm31` but leaves them
agreeing in two runs (`hH`): `RScrub.withScrubResCRH`, the clearing at the
level `avx`, which keeps them, with what it needs of the code proved
(`scrubSideRH`) rather than found when the registration is evaluated. -/
def scrubResCRHOf {api : Api} (r : Unscrubbed api target)
    (hpost : PostOut r.contract (retBitsOf r))
    (ks cs : List Nat) (hres : ResOk r.code r.contract r.stack ks cs)
    (xs : List XReg) (gs : List Reg) (hregs : RegsOk r.code r.contract xs (psOf ks) gs)
    (hH : HRegsOk r.code r.contract)
    (hs : scrubSideRH r.code r.stack (retBitsOf r) ks cs xs gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  have h : (cs.sum = r.stack ∧ (∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) ∧ r.code.x86_64Depth ≤ r.stack ∧
      r.stack + 8 < 2 ^ 64) ∧ (mxClass r.code).isSome = true ∧ (retBitsOf r ≤ 32 ∨ retBitsOf r = 64) ∧
      tailOkB xs gs ks = true ∧ r.code.all (fun i => !writesVec i) = false ∧
      tablesCall r.code r.tables = true := by
    simp only [scrubSideRH, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hcs, hcv⟩, hd⟩, hst⟩, hmx⟩, hrb⟩, ht⟩, hx⟩, hic⟩ := hs
    exact ⟨⟨hcs, fun b hb => of_decide_eq_true (List.all_eq_true.mp hcv b hb), hd, hst⟩, hmx, hrb, ht,
      all_false_of_allInstrs hx, hic⟩
  have ht := tailOk_ofB (retBitsOf r) h.2.2.2.1
  have hok := scrubCodeMCRH_ok r ks cs xs gs h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2 (MxSame.of_fun (mxFun_of h.2.1))
    h.2.2.1 hpost hres (fun x => by unfold xsOf; rw [h.2.2.2.2.1]; exact mem_xregs x) ht hregs hH
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub .avx (retBitsOf r) xs (psOf ks) gs ks (wipeCs ks cs) r.code .avx
    contract := r.contract
    verified := .scrubbed <| .abi ⟨hok.1, hok.2 h.2.2.2.2.2⟩
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe .avx _ _ _ _ _ _ ht.psOk ht.gsOk r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

/-! ## Functions with AVX instructions that end with `vzeroupper` -/

/-- What `scrubUpOf` needs of code `c`: the conditions that `Scrub.withUp`
decided when the registration was evaluated (`UpOk`: its instructions are
below the level `evex`, the vectors' upper halves agree at the end if they
did at the start, and it calls indirectly only its tables' functions), and
`scrubSide`'s of the registers the tail clears. Only the kernel evaluates
it. -/
noncomputable def scrubUpSide (c : Prog isa) (stack rb : Nat) (vec : Bool) (gs : List Reg)
    (ts : List (String × List FnTable)) : Bool :=
  decide (c.x86_64Depth ≤ stack) && decide (stack + 8 < 2 ^ 64) && stack % 8 == 0 &&
  (decide (rb ≤ 32) || rb == 64) && gs.all (scratchRegs.contains ·) && !gs.isEmpty &&
  c.allInstrs (fun i => decide (i.vecLevel ≤ 1) && sideI 1 vec (keptG (allKs (chunks stack)) gs) i) &&
  UpperLock.up c true && tablesCall c ts

/-- `r`, scrubbed at the level `sse` with every granule of its stack wiped,
for code below the level `evex` whose functions with AVX instructions, run
through its tables, end with `vzeroupper`: `Scrub.withUp`, the second route
of `withScrubAllUp`, with the registers its tail clears stated and what it
needs of the code proved (`scrubUpSide`) rather than found when the
registration is evaluated. `withScrubAllUp`'s first route is `scrubAllOf`'s:
the registration names the one it means. -/
def scrubUpOf {api : Api} (r : Unscrubbed api target) (vec : Bool) (gs : List Reg)
    (hpost : PostOut r.contract (retBitsOf r))
    (hs : scrubUpSide r.code r.stack (retBitsOf r) vec gs r.tables = true := by
      (try dsimp only [VG.X86_64.Scrub.retBitsOf]); lit_decide)
    (hw : r.written = [] := by rfl) : Registration api target :=
  have hgs : gs.all (scratchRegs.contains ·) = true := by
    simp only [scrubUpSide, Bool.and_eq_true] at hs; exact hs.1.1.1.1.2
  have hgs' : ∀ q ∈ gs, q ∈ scratchRegs := fun q hq => by
    simpa using List.all_eq_true.mp hgs q hq
  have hps : ∀ q ∈ psOf (allKs (chunks r.stack)), q ∈ scratchRegs := fun q hq => by
    unfold psOf at hq; split at hq <;> simp_all [scratchRegs]
  have hok : Verified target (scrub .sse (retBitsOf r) (xsFor vec (allKs (chunks r.stack)))
        (psOf (allKs (chunks r.stack))) gs (allKs (chunks r.stack)) (chunks r.stack) r.code) r.contract ∧
      NoResidue (scrub .sse (retBitsOf r) (xsFor vec (allKs (chunks r.stack)))
        (psOf (allKs (chunks r.stack))) gs (allKs (chunks r.stack)) (chunks r.stack) r.code) r.contract
        (retBitsOf r) := by
    simp only [scrubUpSide, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hd, hst⟩, h8⟩, hrb⟩, -⟩, hgne⟩, hall⟩, hup⟩, hic⟩ := hs
    have hI : ∀ i ∈ instrs r.code, (decide (i.vecLevel ≤ 1) &&
        sideI 1 vec (keptG (allKs (chunks r.stack)) gs) i) = true :=
      fun i hi => List.all_eq_true.mp ((Code.allInstrs_eq _ r.code).symm.trans hall) i hi
    have hl1 : ∀ i ∈ instrs r.code, i.vecLevel ≤ 1 := fun i hi => by
      have h1 := hI i hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.1
    have hall' : r.code.allInstrs (sideI 1 vec (keptG (allKs (chunks r.stack)) gs)) = true := by
      rw [Code.allInstrs_eq]
      exact List.all_eq_true.mpr fun i hi => by
        have h1 := hI i hi
        simp only [Bool.and_eq_true] at h1
        exact h1.2
    obtain ⟨ht, hxs, hgk, -⟩ := sideI_facts (retBitsOf r) hall' hgs hgne
    have hnames : ∀ f ∈ UpperLock.inames r.code, f ∈ tableFns r.tables := fun f hf => by
      simpa using List.all_eq_true.mp hic f hf
    have h8' : r.stack % 8 = 0 := h8
    have hrb' : retBitsOf r ≤ 32 ∨ retBitsOf r = 64 := hrb
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    unfold retBitsOf at hrb' hp ht ⊢
    rw [e] at hv hp ⊢
    have hr := resOk_all r.code (api.sig.contract ((abi.withConsts r.consts).withTables api.sig r.tables)
      pre post api.writeArgs r.stack leak) h8'
    exact Verified.scrubU (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
      (chunks_sum r.stack) hst (chunks_valid h8') (fun _ => hl1)
      (upperOk_lock hv.2.1 (fun s₁ s₂ h f hf => tables_pub_syms h f (hnames f hf)) hup)
      hrb' hp hr ht hxs (fun e => absurd e (by decide)) (fun _ _ e => absurd e (by decide))
      hgk (fun s₁ s₂ h f hf => tables_pub_syms (contract_pub h) f (hnames f hf))
  { suffix := r.suffix
    consts := r.consts
    tables := r.tables
    stack := r.stack
    code := scrub .sse (retBitsOf r) (xsFor vec (allKs (chunks r.stack))) (psOf (allKs (chunks r.stack))) gs
      (allKs (chunks r.stack)) (chunks r.stack) r.code
    contract := r.contract
    verified := .scrubbed <| .abi ⟨hok.1, hok.2⟩
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe .sse _ _ _ _ _ _ hps hgs' r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith }

end VG.X86_64.Scrub
