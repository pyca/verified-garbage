module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock

/-!
# Code that loads MXCSR only in the functions it calls (x86-64)

`mxCalls c` checks that two runs of `c` along the same trace from the same
MXCSR leave the same MXCSR (`MxSame`, `mxSame_of_mxCalls`), as
`RScrub.Mx.mx` does, but follows `c` itself only by its structure: its
blocks and frames load no MXCSR, and each function it calls either meets
`mxCalls` too or meets `RScrub.Mx.mx` on its own (`vg_mcdt_enter`, which
saves MXCSR and loads it from what it saved). The kernel evaluates
`RScrub.Mx.mx` only on those functions, and the rest of the code one
instruction at a time (`Code.allInstrs`): `mx` of a whole function whose
blocks run to thousands of instructions is too deep for it.

For code generic over the implementations it calls (`Fill`, as in
`ScrubCall.lean`), `mxCallsS` checks the same of its code with a stub
(`Fill.mxCalls`), and `verifiedScrubbedAllFillM` is
`verifiedScrubbedAllFill` from it (`stubSideM`), for code that calls
`vg_mcdt_enter` (ChaCha20-Poly1305, through Poly1305's vector code).
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- Whether `c` loads MXCSR only in functions it calls that meet
`RScrub.Mx.mx` on their own, and calls nothing indirectly. Only the kernel
evaluates it. -/
noncomputable def mxCalls : Prog isa → Bool
  | .block is => Code.allInstrs (fun i => !loadsMxcsr i) (.block is : Prog isa)
  | .seq a b => mxCalls a && mxCalls b
  | .ite _ t e => mxCalls t && mxCalls e
  | .loop b _ => mxCalls b
  | .call _ b => mxCalls b || (RScrub.Mx.mx b []).isSome
  | .frame i b j => !loadsMxcsr i && mxCalls b && !loadsMxcsr j
  | .icall .. => false

/-- Two runs of code that meets `mxCalls`, whose traces agree extended by
`r₁` and `r₂`, from the same MXCSR: their traces are the same, and so is
MXCSR after them. -/
theorem mxCalls_ok {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      mxCalls c = true → s₁.mxcsr = s₂.mxcsr → t₁ = t₂ ∧ s₁'.mxcsr = s₂'.mxcsr := by
  induction e₁ with
  | block h₁ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    cases e₂ with
    | block h₂ =>
      have hl := (execBlock_length h₁).trans (execBlock_length h₂).symm
      have hn : ∀ i ∈ instrs (.block _ : Prog isa), loadsMxcsr i = false := fun i hi => by
        simpa using List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans hc) i hi
      rw [Exec.mxcsr hn (.block h₁), Exec.mxcsr hn (.block h₂)]
      exact ⟨(UpperLock.append_cancel hl ht).1, hm⟩
  | seq x₁ y₁ ihx ihy =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls, Bool.and_eq_true] at hc
    cases e₂ with
    | seq x₂ y₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨hx, mx⟩ := ihx x₂ ht hc.1 hm
      subst hx
      obtain ⟨hy, my⟩ := ihy y₂ (List.append_cancel_left ht) hc.2 mx
      subst hy
      exact ⟨rfl, my⟩
  | iteT _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨h, m⟩ := ih x₂ ht hc.1 hm
      exact ⟨by rw [h], m⟩
    | iteF _ _ => exact (UpperLock.branch_ne ht).elim
  | iteF _ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls, Bool.and_eq_true] at hc
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨h, m⟩ := ih x₂ ht hc.2 hm
      exact ⟨by rw [h], m⟩
    | iteT _ _ => exact (UpperLock.branch_ne ht.symm).elim
  | loopExit x₁ _ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    have hb : mxCalls _ = true := hc
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, m⟩ := ih x₂ ht hb hm
      subst h
      exact ⟨rfl, m⟩
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := ih x₂ ht hb hm
      subst h
      simp at ht
  | loopNext x₁ _ _ ihx ihl =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    have hb : mxCalls _ = true := hc
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := ihx x₂ ht hb hm
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, m⟩ := ihx x₂ ht hb hm
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨h', m'⟩ := ihl l₂ ht' hc m
      subst h'
      exact ⟨rfl, m'⟩
  | call hc₁ x₁ hr₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls, Bool.or_eq_true] at hc
    cases e₂ with
    | call hc₂ x₂ hr₂ =>
      have ht0 := ht
      simp only [List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.cons.injEq] at ht
      have hm' := (RScrub.Mx.call_mx hc₁).trans (hm.trans (RScrub.Mx.call_mx hc₂).symm)
      obtain ⟨h, m⟩ : _ ∧ _ := by
        rcases hc with hc | hc
        · exact ih x₂ ht.2 hc hm'
        · obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hc
          have := RScrub.Mx.mx_ok x₁ x₂ ht.2 [] g (.inl hg) ⟨hm', fun _ h => by cases h⟩
          exact ⟨this.1, this.2.1⟩
      subst h
      exact ⟨(UpperLock.append_cancel (by simp) ht0).1,
        (RScrub.Mx.ret_mx hr₁).trans (m.trans (RScrub.Mx.ret_mx hr₂).symm)⟩
  | @frame i j _ _ _ _ _ _ hp₁ x₁ hq₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls, Bool.and_eq_true] at hc
    cases e₂ with
    | frame hp₂ x₂ hq₂ =>
      have ht0 := ht
      simp only [List.append_assoc] at ht
      obtain ⟨-, ht⟩ := UpperLock.append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      have hm' := (push_mxcsr hp₁).trans (hm.trans (push_mxcsr hp₂).symm)
      obtain ⟨h, m⟩ := ih x₂ ht hc.1.2 hm'
      subst h
      refine ⟨(UpperLock.append_cancel ?_ ht0).1,
        (pop_mxcsr hq₁).trans (m.trans (pop_mxcsr hq₂).symm)⟩
      simp only [List.length_append, List.length_map, addrs_length _ _ State.zero]
  | icall _ _ _ _ _ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls] at hc
    exact absurd hc (by decide)
  | icallNext _ _ _ _ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hc hm
    simp only [mxCalls] at hc
    exact absurd hc (by decide)

/-- Code that meets `mxCalls` leaves the same MXCSR in two runs along the
same trace from the same MXCSR. -/
theorem mxSame_of_mxCalls {c : Prog isa} (h : mxCalls c = true) : MxSame c :=
  fun _ _ _ _ _ e₁ e₂ hm => (mxCalls_ok e₁ e₂ (r₁ := []) (r₂ := []) rfl h hm).2

/-! ## Over a stub for the implementations it calls -/

/-- Whether `c` has no call `.call f (.block [])` of an implementation it is
generic over (`Fill.hole`). -/
def noHole : Prog isa → Bool
  | .block _ => true
  | .seq a b => noHole a && noHole b
  | .ite _ t e => noHole t && noHole e
  | .loop b _ => noHole b
  | .call _ (.block []) => false
  | .call _ b => noHole b
  | .frame _ b _ => noHole b
  | .icall _ _ b x => noHole b && noHole x

theorem noHole_call {f : String} {b : Prog isa} (h : noHole (.call f b) = true) : noHole b = true := by
  cases b with
  | block is => cases is <;> simp_all [noHole]
  | _ => simpa [noHole] using h

/-- `mxCalls` of code with a stub (`a`) for the implementations it calls,
which load no MXCSR: as `mxCalls`, but the functions it calls that meet
`RScrub.Mx.mx` on their own are none of those implementations
(`noHole`). Only the kernel evaluates it. -/
noncomputable def mxCallsS : Prog isa → Bool
  | .block is => Code.allInstrs (fun i => !loadsMxcsr i) (.block is : Prog isa)
  | .seq a b => mxCallsS a && mxCallsS b
  | .ite _ t e => mxCallsS t && mxCallsS e
  | .loop b _ => mxCallsS b
  | .call _ b => mxCallsS b || ((RScrub.Mx.mx b []).isSome && noHole b)
  | .frame i b j => !loadsMxcsr i && mxCallsS b && !loadsMxcsr j
  | .icall .. => false

/-- Code that loads no MXCSR and calls nothing indirectly meets `mxCalls`. -/
theorem mxCalls_of_side : ∀ {c : Prog isa}, c.allInstrs (fun i => !loadsMxcsr i) = true →
    UpperLock.inames c = [] → mxCalls c = true
  | .block _, h, _ => h
  | .seq a b, h, hi => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [UpperLock.inames, List.append_eq_nil_iff] at hi
    simp only [mxCalls, mxCalls_of_side h.1 hi.1, mxCalls_of_side h.2 hi.2, Bool.and_self]
  | .ite _ t e, h, hi => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [UpperLock.inames, List.append_eq_nil_iff] at hi
    simp only [mxCalls, mxCalls_of_side h.1 hi.1, mxCalls_of_side h.2 hi.2, Bool.and_self]
  | .loop b _, h, hi => mxCalls_of_side (c := b) h hi
  | .call _ b, h, hi => by
    simp only [mxCalls, mxCalls_of_side (c := b) h hi, Bool.true_or]
  | .frame i b j, h, hi => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [mxCalls, h.1.1, h.2, mxCalls_of_side h.1.2 hi, Bool.and_self]
  | .icall .., _, hi => by simp [UpperLock.inames] at hi

namespace Fill

variable {k : Nat} {n : String → Nat}

/-- Code with a stub and no hole, and the same code with its calls named
otherwise: `RScrub.Mx.mx` and its `kept` read no name. -/
theorem mx_eq_of_noHole {a b : Prog isa} (hf : Fill k n a b) (h : noHole a = true) :
    (∀ fs, RScrub.Mx.mx b fs = RScrub.Mx.mx a fs) ∧ ∀ f, RScrub.Mx.kept f b = RScrub.Mx.kept f a := by
  induction hf with
  | block => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | hole => simp [noHole] at h
  | seq _ _ iha ihb =>
    simp only [noHole, Bool.and_eq_true] at h
    obtain ⟨ma, ka⟩ := iha h.1; obtain ⟨mb, kb⟩ := ihb h.2
    have mb' := funext mb
    exact ⟨fun fs => by simp only [RScrub.Mx.mx, ma, mb'], fun f => by simp only [RScrub.Mx.kept, ka, kb]⟩
  | ite _ _ _ iha ihb =>
    simp only [noHole, Bool.and_eq_true] at h
    obtain ⟨ma, ka⟩ := iha h.1; obtain ⟨mb, kb⟩ := ihb h.2
    exact ⟨fun fs => by simp only [RScrub.Mx.mx, ma, mb], fun f => by simp only [RScrub.Mx.kept, ka, kb]⟩
  | loop _ _ ih =>
    obtain ⟨m, kk⟩ := ih h
    have hk : ∀ fs : List RScrub.Mx.F, fs.filter (RScrub.Mx.kept · _) = fs.filter (RScrub.Mx.kept · _) :=
      fun fs => List.filter_congr fun f _ => kk f
    exact ⟨fun fs => by simp only [RScrub.Mx.mx, hk, m], fun f => by simp only [RScrub.Mx.kept, kk]⟩
  | call _ _ _ ih =>
    obtain ⟨m, kk⟩ := ih (noHole_call h)
    exact ⟨fun fs => by simp only [RScrub.Mx.mx, m], fun f => by simp only [RScrub.Mx.kept, kk]⟩
  | frame _ _ _ ih =>
    obtain ⟨m, kk⟩ := ih h
    exact ⟨fun fs => by simp only [RScrub.Mx.mx, m], fun f => by simp only [RScrub.Mx.kept, kk]⟩
  | icall => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- `mxCallsS` of a stub gives `mxCalls` of the code with the
implementations it calls, which load no MXCSR (`calleeSide`). -/
theorem mxCalls {a b : Prog isa} (hf : Fill k n a b) (h : mxCallsS a = true) : mxCalls b = true := by
  induction hf with
  | block => exact h
  | hole _ _ hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    have hn : _ := (Code.allInstrs_eq _ _).trans (List.all_eq_true.mpr fun i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans hd.1.2) i hi
      simp only [Bool.and_eq_true] at this; exact this.2)
    simp only [List.isEmpty_iff] at hd
    simp only [VG.X86_64.Scrub.mxCalls, mxCalls_of_side hn hd.2, Bool.true_or]
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [mxCallsS, Bool.and_eq_true] at h
    simp only [VG.X86_64.Scrub.mxCalls, iha h.1, ihb h.2, Bool.and_self]
  | loop _ _ ih => exact ih h
  | call _ _ hb ih =>
    simp only [mxCallsS, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hm, hh⟩
    · simp only [VG.X86_64.Scrub.mxCalls, ih h, Bool.true_or]
    · simp only [VG.X86_64.Scrub.mxCalls, (mx_eq_of_noHole hb hh).1, hm, Bool.or_true]
  | frame _ _ _ ih =>
    simp only [mxCallsS, Bool.and_eq_true] at h
    simp only [VG.X86_64.Scrub.mxCalls, h.1.1, h.2, ih h.1.2, Bool.and_self]
  | icall => simp [mxCallsS] at h

/-- The level of `a`'s vector instructions, which are `b`'s but those its
implementations run, is `b`'s, if theirs is at most it. -/
theorem level {a b : Prog isa} (hf : Fill k n a b)
    (ha : a.allInstrs (fun i => decide (i.vecLevelR ≤ k)) = true) :
    b.allInstrs (fun i => decide (i.vecLevelR ≤ k)) = true := by
  induction hf with
  | block => exact ha
  | hole _ _ hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    simp only [Code.allInstrs]
    exact (Code.allInstrs_eq _ _).trans (List.all_eq_true.mpr fun i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans hd.1.2) i hi
      simp only [Bool.and_eq_true] at this; exact this.1)
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩
  | icall _ _ _ _ ihb ihx =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ihb ha.1.2⟩, ihx ha.2⟩

end Fill

theorem allInstrs_level_mono {a : Prog isa} {ks k : Nat} (hk : ks ≤ k)
    (h : a.allInstrs (fun i => decide (i.vecLevelR ≤ ks)) = true) :
    a.allInstrs (fun i => decide (i.vecLevelR ≤ k)) = true :=
  (Code.allInstrs_eq _ a).trans (List.all_eq_true.mpr fun i hi => by
    have := List.all_eq_true.mp ((Code.allInstrs_eq _ a).symm.trans h) i hi
    simp only [decide_eq_true_eq] at this ⊢; omega)

/-- What the cleanup of a function needs of its code `a` with a stub for
the implementations it calls, which need at most `n` bytes of stack, where
the functions it calls load MXCSR (`mxCallsS`): its stack with theirs at
most `stack` (`depthH`), vector instructions of at most the level `k`, and
indirect calls only of its tables' functions. Only the kernel evaluates it. -/
noncomputable def stubSideM (a : Prog isa) (k : Nat) (n : String → Nat) (stack : Nat)
    (ts : List (String × List FnTable)) : Bool :=
  decide (depthH n a ≤ stack) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k)) && mxCallsS a &&
    tablesCall a ts

/-- `verifiedScrubbedAllFill`, for code whose functions load MXCSR
(`vg_mcdt_enter`): from `stubSideM` of its code with a stub. -/
theorem verifiedScrubbedAllFillM {api : Api} (r : Unscrubbed api target) (v : VecLevel) {a : Prog isa}
    {ks k : Nat} {n : String → Nat} {stack rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r)) (hf : Fill k n a r.code)
    (hks : ks ≤ k) (hk : k ≤ v.level) (ts : List (String × List FnTable) := [])
    (hn : r.stack = stack := by rfl) (hb : retBitsOf r = rb := by rfl) (htb : r.tables = ts := by rfl)
    (ha : stubSideM a ks n stack ts = true := by lit_decide)
    (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAll v rb stack r.code) r.contract rb := by
  subst hn hb htb
  simp only [stubSideM, Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨⟨⟨hd, hs⟩, hm⟩, ht⟩ := ha
  have hlv := allInstrs_level_mono hk (hf.level (allInstrs_level_mono hks hs))
  have hic : tablesCall r.code r.tables = true := by rw [tablesCall, hf.inames_eq]; exact ht
  exact verifiedScrubbedAllF r v hpost (Nat.le_trans hf.depth_leH hd) hlv
    (mxSame_of_mxCalls (hf.mxCalls hm)) hic hl rfl rfl

end VG.X86_64.Scrub
