module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn

/-!
# The cleanup of a function generic over what it calls (x86-64)

`X86_64.Scrub.verifiedScrubbedKsF` needs four facts of a function's code,
callees included: its depth, the level of its vector instructions, that it
leaves MXCSR as two runs found it, and that it calls indirectly only its
tables' functions. A function generic over an implementation it calls (a
variant, `Proof/Variants/<Iface>/X86_64.lean`) has code that is not a closed
term: it is the function's own code with the implementation's code where it
calls it, and each implementation is evaluated where it is defined, never in
its callers.

`Fill k n a b` says that `b` is the code `a` with some of its empty blocks
replaced by code that needs at most `n` bytes of stack, whose vector
instructions are at most of level `k`, which loads no MXCSR and calls nothing
indirectly (`calleeSide`), and its calls' names changed: `a` is the
function's code with a stub, an implementation whose code is `.block []`, and
`b` its code with an implementation. A function proves it once of every
implementation, by `fill_calls` (which walks the function's code, not the
implementation's), from `calleeSide` of the implementation's code, a fact
the variant proves where it is defined. `verifiedScrubbedAllFill` then gives
`VerifiedScrubbed` of `scrubAll` of `b` from `stubSide` of `a`, which the
kernel evaluates once, of the stub's code (as x86's `ScrubCall.lean`).
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- What the cleanup of a function that calls `c` needs of it: at most `n`
bytes of stack, vector instructions of at most the level `k`, no load of
MXCSR, and no indirect call. Only the kernel evaluates it. -/
noncomputable def calleeSide (c : Prog isa) (k n : Nat) : Bool :=
  decide (c.x86_64Depth ≤ n) && c.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    (UpperLock.inames c).isEmpty

/-- What the cleanup of a function needs of its code `a` with a stub for
the implementations it calls, which need at most `n` bytes of stack: its
stack with theirs at most `stack`, vector instructions of at most the level
`k`, no load of MXCSR, and indirect calls only of its tables' functions. -/
noncomputable def stubSide (a : Prog isa) (k n stack : Nat) (ts : List (String × List FnTable)) : Bool :=
  decide (a.x86_64Depth + n ≤ stack) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    tablesCall a ts

/-- `b` is `a` with some of its empty blocks replaced by code that meets
`calleeSide _ k n` (`hole`), and the names of its calls changed: `a` is a
function's code with a stub for the implementations it calls, and `b` its
code with them. Its blocks, conditions, frames and indirect calls are
`a`'s. -/
inductive Fill (k n : Nat) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : Fill k n (.block is) (.block is)
  | hole {d : Prog isa} : calleeSide d k n = true → Fill k n (.block []) d
  | seq {a b a' b' : Prog isa} : Fill k n a a' → Fill k n b b' → Fill k n (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : Fill k n t t' → Fill k n e e' → Fill k n (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : Fill k n b b' → Fill k n (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : Fill k n b b' → Fill k n (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : Fill k n b b' → Fill k n (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      Fill k n b b' → Fill k n x x' → Fill k n (.icall i f b x) (.icall i f b' x')

namespace Fill

variable {k n : Nat} {a b : Prog isa}

theorem depth_le (h : Fill k n a b) : b.x86_64Depth ≤ a.x86_64Depth + n := by
  induction h with
  | block => exact Nat.le_add_right _ _
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at hd
    simp only [Code.x86_64Depth, Nat.zero_add]; exact hd.1.1
  | seq _ _ iha ihb => simp only [Code.x86_64Depth]; omega
  | ite _ _ _ iht ihe => simp only [Code.x86_64Depth]; omega
  | loop _ _ ih => simp only [Code.x86_64Depth]; exact ih
  | call _ _ _ ih => simp only [Code.x86_64Depth]; omega
  | frame _ _ _ ih => simp only [Code.x86_64Depth]; omega
  | icall _ _ _ _ ihb ihx => simp only [Code.x86_64Depth]; omega

/-- What `a`'s instructions meet, `b`'s do, if what fills its holes meets it
too: a level of the vector instructions, and no load of MXCSR. -/
theorem side (h : Fill k n a b)
    (ha : a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true) :
    b.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true := by
  induction h with
  | block => exact ha
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    exact hd.1.2
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩
  | icall _ _ _ _ ihb ihx =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ihb ha.1.2⟩, ihx ha.2⟩

/-- The functions `b` may call indirectly are `a`'s: an implementation
calls none (`calleeSide`). -/
theorem inames_eq (h : Fill k n a b) : UpperLock.inames b = UpperLock.inames a := by
  induction h with
  | block => rfl
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    simpa [UpperLock.inames] using hd.2
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [UpperLock.inames, iha, ihb]
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simp only [UpperLock.inames, ih]
  | icall _ _ _ _ ihb ihx => simp only [UpperLock.inames, ihb, ihx]

/-- `Fill` into code that the implementation chooses (`if p then x else y`),
where it chooses `x`. -/
theorem if_pos {p : Prop} [Decidable p] {x y : Prog isa} (h : Fill k n a x) (hp : p) :
    Fill k n a (if p then x else y) := by
  rw [ite_eq_left hp]; exact h

/-- `Fill` into code that the implementation chooses, where it chooses `y`. -/
theorem if_neg {p : Prop} [Decidable p] {x y : Prog isa} (h : Fill k n a y) (hp : ¬p) :
    Fill k n a (if p then x else y) := by
  rw [ite_eq_right hp]; exact h

end Fill

/-- The level of the vector instructions of `b` is at most `v`'s, `k`, and
`b` loads no MXCSR, from what `a`'s stub and its implementations meet. -/
theorem allInstrs_level {b : Prog isa} {k : Nat} {v : VecLevel} (hk : k ≤ v.level)
    (h : b.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true) :
    b.allInstrs (fun i => decide (i.vecLevelR ≤ v.level)) = true ∧
      b.allInstrs (fun i => !loadsMxcsr i) = true := by
  have hI := (Code.allInstrs_eq _ b).symm.trans h
  refine ⟨(Code.allInstrs_eq _ b).trans (List.all_eq_true.mpr fun i hi => ?_),
    (Code.allInstrs_eq _ b).trans (List.all_eq_true.mpr fun i hi => ?_)⟩
  · have := List.all_eq_true.mp hI i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact decide_eq_true (Nat.le_trans this.1 hk)
  · have := List.all_eq_true.mp hI i hi
    simp only [Bool.and_eq_true] at this
    exact this.2

/-- What `a`'s instructions meet at the level `ks`, they meet at any level
`k` above it. -/
theorem side_mono {a : Prog isa} {ks k : Nat} (hk : ks ≤ k)
    (h : a.allInstrs (fun i => decide (i.vecLevelR ≤ ks) && !loadsMxcsr i) = true) :
    a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true := by
  have hI := (Code.allInstrs_eq _ a).symm.trans h
  refine (Code.allInstrs_eq _ a).trans (List.all_eq_true.mpr fun i hi => ?_)
  have := List.all_eq_true.mp hI i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this ⊢
  exact ⟨Nat.le_trans this.1 hk, this.2⟩

/-- `r`'s code `b`, generic over the implementations it calls (`Fill k n a
b`), followed by `scrubAll v rb stack`, meets `r`'s contract in constant
time and returns without secret residue: from `stubSide` of its code with a
stub (`a`) at the level `ks` of its own instructions, which the kernel
evaluates once, and what each implementation proves of its own code where it
is defined, at its level `k` (in `hf`), both at most `v`'s. -/
theorem verifiedScrubbedAllFill {api : Api} (r : Unscrubbed api target) (v : VecLevel) {a : Prog isa}
    {ks k n stack rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r)) (hf : Fill k n a r.code)
    (hks : ks ≤ k) (hk : k ≤ v.level) (ts : List (String × List FnTable) := [])
    (hn : r.stack = stack := by rfl) (hb : retBitsOf r = rb := by rfl) (htb : r.tables = ts := by rfl)
    (ha : stubSide a ks n stack ts = true := by lit_decide)
    (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAll v rb stack r.code) r.contract rb := by
  subst hn hb htb
  simp only [stubSide, Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨⟨hd, hs⟩, ht⟩ := ha
  obtain ⟨hlv, hmx⟩ := allInstrs_level hk (hf.side (side_mono hks hs))
  have hic : tablesCall r.code r.tables = true := by rw [tablesCall, hf.inames_eq]; exact ht
  exact verifiedScrubbedAllF r v hpost (Nat.le_trans hf.depth_le hd) hlv (mxSame_of_noLoad hmx) hic hl rfl rfl

/-- Proves `Fill k n a b` of a function's code with a stub (`a`) and with
implementations (`b`), from hypotheses `calleeSide c k n = true` of each
implementation's code `c`: it walks the function's code, unfolding its
definitions, and closes each place it calls an implementation by its
hypothesis (`Fill.hole`). -/
macro "fill_calls" : tactic => `(tactic| repeat' (first
  | exact Fill.block _
  | exact Fill.hole (by assumption)
  | refine Fill.seq ?_ ?_
  | refine Fill.ite _ ?_ ?_
  | refine Fill.loop _ ?_
  | refine Fill.call _ _ ?_
  | refine Fill.frame _ _ ?_
  | refine Fill.icall _ _ ?_ ?_
  | refine Fill.if_pos ?_ (by assumption)
  | refine Fill.if_neg ?_ (by assumption)))

end VG.X86_64.Scrub
