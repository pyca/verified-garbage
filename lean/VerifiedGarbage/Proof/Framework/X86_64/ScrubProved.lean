module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubUp
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# What the cleanup needs of the code, as one Boolean (x86-64)

`scrubSideG c stack rb v vec ks cs` is what the cleanup of code `c` with
`stack` bytes of stack and a result of `rb` bits needs of it, at the level
`v`, with the granules `ks` of the chunks `cs` wiped: one pass over the
instructions (`sideI`) and that two runs along a path leave the same MXCSR
(`mxSameB`). The kernel evaluates it where the function is proven
(`lit_decide`), and `scrubSideG_ok` turns it into what `Verified.scrub`
takes (`ScrubFn.lean` states the cleanups `scrubAll` and `scrubSel` with
it).
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

end VG.X86_64.Scrub
