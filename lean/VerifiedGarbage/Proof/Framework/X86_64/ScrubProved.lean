module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Scrubbed code registered with its facts proved (x86-64)

`scrubResOf`, `scrubOf` and `scrubAllOf`: what `Scrub.scrubReg`,
`RScrub.withScrub` and `Scrub.withScrubAll` register, with nothing left for
the emitter to work out. The level the tail clears the vector registers at,
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
abbrev retBitsOf {api : Api} (r : Registration api target) : Nat :=
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
theorem scrubSide_ok {api : Api} (r : Registration api target) (v : VecLevel) (vec : Bool) (ks : List Nat)
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
def scrubResOf {api : Api} (r : Registration api target) (v : VecLevel) (vec : Bool) (ks : List Nat)
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
    verified := hok.1
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ hps hgs r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith
    residue := some ⟨hok.2⟩ }

end VG.X86_64.Scrub

namespace VG.X86_64.RScrub

open VG.Impl.Scrub.X86_64 VG.X86_64.Scrub

/-- `r`, returning without secret residue, given the residue analysis of its
code (`Analysed`): `withScrub`, with the level and the registers its tail
clears stated and what it needs of the code proved (`Scrub.scrubSide`)
rather than found when the registration is evaluated. -/
def scrubOf {api : Api} (r : Registration api target) (v : VecLevel) (vec : Bool) (gs : List Reg)
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
def scrubAllOf {api : Api} (r : Registration api target) (v : VecLevel) (vec : Bool) (gs : List Reg)
    (hpost : PostOut r.contract (retBitsOf r))
    (hs : scrubAllSide r.code r.stack (retBitsOf r) v vec gs r.tables = true)
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
    verified := hok.1
    ofApi := r.ofApi
    ofSig := r.ofSig
    spSafe := scrub_spSafe v _ _ _ _ _ _ hps hgs r.spSafe
    written := r.written
    writtenOk := by rw [hw]; exact fun _ _ _ _ _ => True.intro
    extra := r.extra
    vendor := r.vendor
    notWith := r.notWith
    residue := some ⟨hok.2⟩ }

end VG.X86_64.Scrub
