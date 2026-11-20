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

`Fill k n a b` says that `b` is the code `a` with the bodies of some of its
calls `.call f (.block [])` replaced by code that needs at most `n f` bytes
of stack, whose vector instructions are at most of level `k`, which loads no
MXCSR and calls nothing indirectly (`calleeSide`), and its calls' names
changed: `a` is the function's code with a stub, an implementation whose
code is `.block []`, called by a name that tells apart the kinds of
implementation it calls and the stack each needs, and `b` its code with
implementations. A function proves it once of every
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

/-- `Code.x86_64Depth` of code with a stub for the implementations it calls,
each call `.call f (.block [])` of one (`Fill.hole`) taking `n f` bytes: the
stack of the code with implementations that need at most that much
(`Fill.depth_leH`). -/
def depthH (n : String → Nat) : Prog isa → Nat
  | .block _ => 0
  | .call f (.block []) => n f + 8
  | .seq a b => max (depthH n a) (depthH n b)
  | .ite _ t e => max (depthH n t) (depthH n e)
  | .loop b _ => depthH n b
  | .call _ b => depthH n b + 8
  | .frame i b _ => depthH n b + i.frameBytes
  | .icall _ _ b x => max (depthH n b + 8) (depthH n x)

/-- What the cleanup of a function needs of its code `a` with a stub for
the implementations it calls, which need at most `n` bytes of stack: its
stack with theirs at most `stack` (`depthH`), vector instructions of at most
the level `k`, no load of MXCSR, and indirect calls only of its tables'
functions. -/
noncomputable def stubSide (a : Prog isa) (k : Nat) (n : String → Nat) (stack : Nat) (ts : List (String × List FnTable)) : Bool :=
  decide (depthH n a ≤ stack) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    tablesCall a ts

/-- `b` is `a` with the bodies of some of its calls `.call f (.block [])`
replaced by code that meets `calleeSide _ k (n f)` (`hole`), and the names
of its calls changed: `a` is a function's code with a stub for the
implementations it calls, and `b` its code with them. Its blocks,
conditions, frames and indirect calls are `a`'s. -/
inductive Fill (k : Nat) (n : String → Nat) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : Fill k n (.block is) (.block is)
  | hole {d : Prog isa} (f g : String) : calleeSide d k (n f) = true →
      Fill k n (.call f (.block [])) (.call g d)
  | seq {a b a' b' : Prog isa} : Fill k n a a' → Fill k n b b' → Fill k n (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : Fill k n t t' → Fill k n e e' → Fill k n (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : Fill k n b b' → Fill k n (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : Fill k n b b' → Fill k n (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : Fill k n b b' → Fill k n (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      Fill k n b b' → Fill k n x x' → Fill k n (.icall i f b x) (.icall i f b' x')

namespace Fill

variable {k : Nat} {n : String → Nat} {a b : Prog isa}

theorem depthH_call (f : String) (c : Prog isa) : depthH n c + 8 ≤ depthH n (.call f c) := by
  cases c with
  | block is => cases is <;> simp [depthH]
  | _ => simp [depthH]

/-- The stack `b` uses is at most `depthH n a`. -/
theorem depth_leH (h : Fill k n a b) : b.x86_64Depth ≤ depthH n a := by
  induction h with
  | block is => simp [Code.x86_64Depth, depthH]
  | hole f g hd =>
    simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at hd
    simp only [Code.x86_64Depth, depthH]; omega
  | seq _ _ iha ihb => simp only [Code.x86_64Depth, depthH]; omega
  | ite _ _ _ iht ihe => simp only [Code.x86_64Depth, depthH]; omega
  | loop _ _ ih => simp only [Code.x86_64Depth, depthH]; exact ih
  | @call b _ f _ _ ih =>
    have := depthH_call (n := n) f b
    simp only [Code.x86_64Depth]; omega
  | frame _ _ _ ih => simp only [Code.x86_64Depth, depthH]; omega
  | icall _ _ _ _ ihb ihx => simp only [Code.x86_64Depth, depthH]; omega

/-- What `a`'s instructions meet, `b`'s do, if what fills its holes meets it
too: a level of the vector instructions, and no load of MXCSR. -/
theorem side (h : Fill k n a b)
    (ha : a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true) :
    b.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true := by
  induction h with
  | block => exact ha
  | hole _ _ hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    simp only [Code.allInstrs]; exact hd.1.2
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
  | hole _ _ hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    simpa [UpperLock.inames] using hd.2
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [UpperLock.inames, iha, ihb]
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simp only [UpperLock.inames, ih]
  | icall _ _ _ _ ihb ihx => simp only [UpperLock.inames, ihb, ihx]

/-- `Fill` into code that both the stub and the implementation choose by the
same condition. -/
theorem ifp {p : Prop} [Decidable p] {a a' x y : Prog isa} (h : Fill k n a x) (h' : Fill k n a' y) :
    Fill k n (if p then a else a') (if p then x else y) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]; exact h
  · rw [ite_eq_right hp, ite_eq_right hp]; exact h'

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

/-- What `calleeSide` needs of code `a` with a stub for the implementations
it calls, which need at most `n f` bytes of stack: its stack with theirs at
most `m`, vector instructions of at most the level `k`, no load of MXCSR,
and no indirect call. -/
noncomputable def stubCallee (a : Prog isa) (k : Nat) (n : String → Nat) (m : Nat) : Bool :=
  decide (depthH n a ≤ m) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    (UpperLock.inames a).isEmpty

/-- Code generic over the implementations it calls meets `calleeSide`, as
an implementation of a function that others call, from `stubCallee` of its
code with a stub, which the kernel evaluates once. -/
theorem calleeSide_of_fill {ks k : Nat} {n : String → Nat} {m : Nat} {a b : Prog isa} (hf : Fill k n a b)
    (hks : ks ≤ k) (ha : stubCallee a ks n m = true) : calleeSide b k m = true := by
  simp only [stubCallee, Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨⟨hd, hs⟩, hi⟩ := ha
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Nat.le_trans hf.depth_leH hd, hf.side (side_mono hks hs)⟩, by rw [hf.inames_eq]; exact hi⟩

theorem level_join_left (a b : VecLevel) : a.level ≤ (a.join b).level := by
  cases a <;> cases b <;> decide

theorem level_join_right (a b : VecLevel) : b.level ≤ (a.join b).level := by
  cases a <;> cases b <;> decide

/-- What the cleanup needs of an implementation at the level `k` and stack
`n`, it meets at any level and stack above them. -/
theorem calleeSide_mono {c : Prog isa} {k k' n n' : Nat} (hk : k ≤ k') (hn : n ≤ n')
    (h : calleeSide c k n = true) : calleeSide c k' n' = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨Nat.le_trans h.1.1 hn, side_mono hk h.1.2⟩, h.2⟩

/-- `r`'s code `b`, generic over the implementations it calls (`Fill k n a
b`), followed by `scrubAll v rb stack`, meets `r`'s contract in constant
time and returns without secret residue: from `stubSide` of its code with a
stub (`a`) at the level `ks` of its own instructions, which the kernel
evaluates once, and what each implementation proves of its own code where it
is defined, at its level `k` (in `hf`), both at most `v`'s. -/
theorem verifiedScrubbedAllFill {api : Api} (r : Unscrubbed api target) (v : VecLevel) {a : Prog isa}
    {ks k : Nat} {n : String → Nat} {stack rb : Nat}
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
  exact verifiedScrubbedAllF r v hpost (Nat.le_trans hf.depth_leH hd) hlv (mxSame_of_noLoad hmx) hic hl rfl rfl

/-- Proves `Fill k n a b` of a function's code with a stub (`a`) and with
implementations (`b`), from hypotheses `calleeSide c k n = true` of each
implementation's code `c`: it walks the function's code, unfolding its
definitions, and closes each place it calls an implementation by its
hypothesis (`Fill.hole`). -/
macro "fill_calls" : tactic => `(tactic| repeat' (first
  | exact Fill.block _
  | exact Fill.hole _ _ (by assumption)
  | refine Fill.seq ?_ ?_
  | refine Fill.ite _ ?_ ?_
  | refine Fill.loop _ ?_
  | refine Fill.call _ _ ?_
  | refine Fill.frame _ _ ?_
  | refine Fill.icall _ _ ?_ ?_
  | refine Fill.ifp ?_ ?_
  | refine Fill.if_pos ?_ (by assumption)
  | refine Fill.if_neg ?_ (by assumption)))

end VG.X86_64.Scrub
