module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86_64.CalleeSide
public import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# The cleanup of code generic over code it inlines (x86-64)

`Proof/Framework/X86_64/ScrubCall.lean`'s `Fill` replaces the bodies of
calls: its holes are calls `.call f (.block [])`, filled by calls of an
implementation's code. Code generic over an implementation may instead
inline what the implementation gives at many places: Montgomery
multiplication `mm o a b` (a call of a function, or its code inline), or a
list of code spliced into the function's own (`seqs (… ++ ex sp sl ++ …)`).
`FillG k n a b` says that `b` is the code `a` with each hole
`.call f (.block [])` replaced by any code that meets `calleeSide _ k (n f)`
(`hole`), or by a list of such code at the head of a sequence (`holes`): `a`
is the function's code over a stub (`mm := fun _ _ _ => .call "mm" (.block
[])`), closed, which the kernel evaluates once (`stubSideG`), and `b` its
code over an implementation, whose facts the implementation proves where it
is defined. A hole's code takes the place of the call, so it needs at most
`n f` bytes of stack, not `n f + 8` (`depthG`).

`fill_gen` proves `FillG` by walking the function's code, closing each hole
by a hypothesis (`∀ o a b, calleeSide (mm o a b) k 8 = true` too, a `FillG` of
a part of it proven apart, and
`calleeSide c k m` for a hole of a call of `c`, of `m + 8` bytes).
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- `Code.x86_64Depth` of code with a stub, each hole `.call f (.block [])`
taking `n f` bytes (and at least a call's 8). -/
def depthG (n : String → Nat) : Prog isa → Nat
  | .block _ => 0
  | .call f (.block []) => max (n f) 8
  | .seq a b => max (depthG n a) (depthG n b)
  | .ite _ t e => max (depthG n t) (depthG n e)
  | .loop b _ => depthG n b
  | .call _ b => depthG n b + 8
  | .frame i b _ => depthG n b + i.frameBytes
  | .icall _ _ b x => max (depthG n b + 8) (depthG n x)

/-- What the cleanup of a function needs of its code `a` with a stub
(`depthG`): as `stubSide`. -/
noncomputable def stubSideG (a : Prog isa) (k : Nat) (n : String → Nat) (stack : Nat)
    (ts : List (String × List FnTable)) : Bool :=
  decide (depthG n a ≤ stack) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    tablesCall a ts

/-- What `calleeSide` needs of code `a` with a stub (`depthG`): as
`stubCallee`. -/
noncomputable def stubCalleeG (a : Prog isa) (k : Nat) (n : String → Nat) (m : Nat) : Bool :=
  decide (depthG n a ≤ m) && a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) &&
    (UpperLock.inames a).isEmpty

/-- `b` is `a` with each of some holes `.call f (.block [])` replaced by code
that meets `calleeSide _ k (n f)` (`hole`), or by a list of it at the head of
a sequence (`holes`), and the names of its calls changed. -/
inductive FillG (k : Nat) (n : String → Nat) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : FillG k n (.block is) (.block is)
  | hole {d : Prog isa} (f : String) : calleeSide d k (n f) = true → FillG k n (.call f (.block [])) d
  | holes {a b : Prog isa} (f : String) (ds : List (Prog isa)) : (∀ d ∈ ds, calleeSide d k (n f) = true) →
      FillG k n a b → FillG k n (.seq (.call f (.block [])) a) (ds.foldr .seq b)
  | seq {a b a' b' : Prog isa} : FillG k n a a' → FillG k n b b' → FillG k n (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : FillG k n t t' → FillG k n e e' →
      FillG k n (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : FillG k n b b' → FillG k n (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : FillG k n b b' → FillG k n (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : FillG k n b b' → FillG k n (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      FillG k n b b' → FillG k n x x' → FillG k n (.icall i f b x) (.icall i f b' x')

namespace FillG

variable {k : Nat} {n : String → Nat} {a b : Prog isa}

theorem depthG_call (f : String) (c : Prog isa) : depthG n c + 8 ≤ depthG n (.call f c) ∨
    (c = .block [] ∧ depthG n (.call f c) = max (n f) 8) := by
  cases c with
  | block is => cases is <;> simp [depthG]
  | _ => left; simp [depthG]

theorem depth_foldr (ds : List (Prog isa)) (b : Prog isa) (m : Nat) (hd : ∀ d ∈ ds, d.x86_64Depth ≤ m) :
    (ds.foldr .seq b).x86_64Depth ≤ max m b.x86_64Depth := by
  induction ds with
  | nil => exact Nat.le_max_right _ _
  | cons d ds ih =>
    simp only [List.foldr_cons, Code.x86_64Depth]
    have h1 := hd d (List.mem_cons_self ..)
    have h2 := ih fun x hx => hd x (List.mem_cons_of_mem _ hx)
    omega

/-- The stack `b` uses is at most `depthG n a`. -/
theorem depth_le (h : FillG k n a b) : b.x86_64Depth ≤ depthG n a := by
  induction h with
  | block is => simp [Code.x86_64Depth, depthG]
  | hole f hd =>
    simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at hd
    simp only [depthG]; omega
  | @holes _ b' f ds hd _ ih =>
    have := depth_foldr ds b' (n f) fun d hm => by
      have := hd d hm
      simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1
    simp only [depthG]; omega
  | seq _ _ iha ihb => simp only [Code.x86_64Depth, depthG]; omega
  | ite _ _ _ iht ihe => simp only [Code.x86_64Depth, depthG]; omega
  | loop _ _ ih => simp only [Code.x86_64Depth, depthG]; exact ih
  | @call b _ f _ hf ih =>
    rcases depthG_call (n := n) f b with h | ⟨rfl, _⟩
    · simp only [Code.x86_64Depth]; omega
    · cases hf; simp only [Code.x86_64Depth, depthG]; omega
  | frame _ _ _ ih => simp only [Code.x86_64Depth, depthG]; omega
  | icall _ _ _ _ ihb ihx => simp only [Code.x86_64Depth, depthG]; omega

theorem side_foldr (p : Instr → Bool) (ds : List (Prog isa)) (b : Prog isa)
    (hd : ∀ d ∈ ds, d.allInstrs p = true) (hb : b.allInstrs p = true) : (ds.foldr .seq b).allInstrs p = true := by
  induction ds with
  | nil => exact hb
  | cons d ds ih =>
    simp only [List.foldr_cons, Code.allInstrs, Bool.and_eq_true]
    exact ⟨hd d (List.mem_cons_self ..), ih fun x hx => hd x (List.mem_cons_of_mem _ hx)⟩

/-- What `a`'s instructions meet, `b`'s do, if what fills its holes meets it
too: a level of the vector instructions, and no load of MXCSR. -/
theorem side (h : FillG k n a b)
    (ha : a.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true) :
    b.allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true := by
  induction h with
  | block => exact ha
  | hole _ hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    exact hd.1.2
  | holes _ ds hd _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha
    exact side_foldr _ ds _ (fun d hm => by
      have := hd d hm
      simp only [calleeSide, Bool.and_eq_true] at this
      exact this.1.2) (ih ha.2)
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩
  | icall _ _ _ _ ihb ihx =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ihb ha.1.2⟩, ihx ha.2⟩

theorem inames_foldr (ds : List (Prog isa)) (b : Prog isa) (hd : ∀ d ∈ ds, UpperLock.inames d = []) :
    UpperLock.inames (ds.foldr .seq b) = UpperLock.inames b := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons, UpperLock.inames, hd d (List.mem_cons_self ..),
      ih fun x hx => hd x (List.mem_cons_of_mem _ hx), List.nil_append]

/-- The functions `b` may call indirectly are `a`'s: what fills its holes
calls none (`calleeSide`). -/
theorem inames_eq (h : FillG k n a b) : UpperLock.inames b = UpperLock.inames a := by
  induction h with
  | block => rfl
  | hole _ hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    simpa [UpperLock.inames] using hd.2
  | holes _ ds hd _ ih =>
    rw [inames_foldr ds _ fun d hm => by
      have := hd d hm
      simp only [calleeSide, Bool.and_eq_true] at this
      simpa using this.2]
    simp only [UpperLock.inames, ih, List.nil_append]
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [UpperLock.inames, iha, ihb]
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simp only [UpperLock.inames, ih]
  | icall _ _ _ _ ihb ihx => simp only [UpperLock.inames, ihb, ihx]

/-- `FillG` into code that both the stub and the implementation choose by
the same condition. -/
theorem ifp {p : Prop} [Decidable p] {a a' x y : Prog isa} (h : FillG k n a x) (h' : FillG k n a' y) :
    FillG k n (if p then a else a') (if p then x else y) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]; exact h
  · rw [ite_eq_right hp, ite_eq_right hp]; exact h'

/-- Code is itself with no hole filled. -/
theorem refl : ∀ c : Prog isa, FillG k n c c
  | .block is => .block is
  | .seq a b => .seq (refl a) (refl b)
  | .ite c t e => .ite c (refl t) (refl e)
  | .loop b c => .loop c (refl b)
  | .call f b => .call f f (refl b)
  | .frame i b j => .frame i j (refl b)
  | .icall i f b x => .icall i f (refl b) (refl x)

/-- A call of code that meets `calleeSide` at `m`, as a hole of `m + 8` bytes. -/
theorem calleeSide_call {d : Prog isa} {m : Nat} (g : String) (h : calleeSide d k m = true) :
    calleeSide (.call g d) k (m + 8) = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨by simp only [Code.x86_64Depth]; omega, by simpa only [Code.allInstrs] using h.1.2⟩,
    by simpa only [UpperLock.inames] using h.2⟩

/-- A list spliced into a sequence of the implementation's code, in the
place of a hole of the stub's (`holes`). -/
theorem seqs_append {f : String} {ds bs : List (Prog isa)} {a : Prog isa} (hne : bs ≠ [])
    (hd : ∀ d ∈ ds, calleeSide d k (n f) = true) (h : FillG k n a (Impl.Bignum.X86_64.seqs bs)) :
    FillG k n (.seq (.call f (.block [])) a) (Impl.Bignum.X86_64.seqs (ds ++ bs)) := by
  have e : ∀ ds : List (Prog isa), Impl.Bignum.X86_64.seqs (ds ++ bs) = ds.foldr .seq (Impl.Bignum.X86_64.seqs bs) := by
    intro ds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      rw [List.cons_append, List.foldr_cons, ← ih]
      cases h' : ds ++ bs with
      | nil => exact absurd (List.append_eq_nil_iff.mp h').2 hne
      | cons _ _ => rfl
  rw [e]; exact holes f ds hd h

/-- A list spliced into a sequence of the implementation's code after its
element `x`, in the place of a hole of the stub's. -/
theorem seqs_cons {x : Prog isa} {ds bs : List (Prog isa)} {a c : Prog isa} (hx : FillG k n a x)
    (h : FillG k n c (Impl.Bignum.X86_64.seqs (ds ++ bs))) (hne : bs ≠ []) :
    FillG k n (.seq a c) (Impl.Bignum.X86_64.seqs (x :: (ds ++ bs))) := by
  cases h' : ds ++ bs with
  | nil => exact absurd (List.append_eq_nil_iff.mp h').2 hne
  | cons y ys => rw [h'] at h; exact .seq hx h

end FillG

/-- `r`'s code `b`, generic over code it inlines or calls (`FillG k n a b`),
followed by `scrubAll v rb stack`, meets `r`'s contract in constant time and
returns without secret residue: from `stubSideG` of its code with a stub
(`a`) at the level `ks` of its own instructions, which the kernel evaluates
once, and what each implementation proves of its code where it is defined,
at the level `k` (in `hf`), both at most `v`'s. -/
theorem verifiedScrubbedAllFillG {api : Api} (r : Unscrubbed api target) (v : VecLevel) {a : Prog isa}
    {ks k : Nat} {n : String → Nat} {stack rb : Nat}
    (hpost : PostOut r.contract (retBitsOf r)) (hf : FillG k n a r.code)
    (hks : ks ≤ k) (hk : k ≤ v.level) (ts : List (String × List FnTable) := [])
    (hn : r.stack = stack := by rfl) (hb : retBitsOf r = rb := by rfl) (htb : r.tables = ts := by rfl)
    (ha : stubSideG a ks n stack ts = true := by lit_decide)
    (hl : litSide stack rb = true := by decide) :
    VerifiedScrubbed target (scrubAll v rb stack r.code) r.contract rb := by
  subst hn hb htb
  simp only [stubSideG, Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨⟨hd, hs⟩, ht⟩ := ha
  obtain ⟨hlv, hmx⟩ := allInstrs_level hk (hf.side (side_mono hks hs))
  have hic : tablesCall r.code r.tables = true := by rw [tablesCall, hf.inames_eq]; exact ht
  exact verifiedScrubbedAllF r v hpost (Nat.le_trans hf.depth_le hd) hlv (mxSame_of_noLoad hmx) hic hl rfl rfl

/-- Code generic over code it inlines or calls meets `calleeSide`, as an
implementation that others call, from `stubCalleeG` of its code with a
stub, which the kernel evaluates once. -/
theorem calleeSide_of_fillG {ks k : Nat} {n : String → Nat} {m : Nat} {a b : Prog isa} (hf : FillG k n a b)
    (hks : ks ≤ k) (ha : stubCalleeG a ks n m = true) : calleeSide b k m = true := by
  simp only [stubCalleeG, Bool.and_eq_true, decide_eq_true_eq] at ha
  obtain ⟨⟨hd, hs⟩, hi⟩ := ha
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Nat.le_trans hf.depth_le hd, hf.side (side_mono hks hs)⟩, by rw [hf.inames_eq]; exact hi⟩

/-- `c` with each hole `.call f (.block [])` whose name `σ` maps to a name
and code replaced by the call of that code by that name: code over a stub
with the implementation's functions where it calls them, for code too large
to walk (`fill_gen`), whose equation with the implementation's the kernel
checks instead (`kernel_rfl`). -/
def fillCallsG (σ : String → Option (String × Prog isa)) : Prog isa → Prog isa
  | .call f (.block []) => match σ f with
    | some (g, d) => .call g d
    | none => .call f (.block [])
  | .block is => .block is
  | .seq a b => .seq (fillCallsG σ a) (fillCallsG σ b)
  | .ite c t e => .ite c (fillCallsG σ t) (fillCallsG σ e)
  | .loop b c => .loop (fillCallsG σ b) c
  | .call f b => .call f (fillCallsG σ b)
  | .frame i b j => .frame i (fillCallsG σ b) j
  | .icall i f b x => .icall i f (fillCallsG σ b) (fillCallsG σ x)

/-- `fillCallsG σ c` is `c` with its holes filled, if the call of each code
`σ` gives meets `calleeSide` for the hole's stack. -/
theorem fillG_of {k : Nat} {n : String → Nat} {σ : String → Option (String × Prog isa)}
    (hσ : ∀ f g d, σ f = some (g, d) → calleeSide (.call g d) k (n f) = true) :
    ∀ c : Prog isa, FillG k n c (fillCallsG σ c)
  | .block is => .block is
  | .seq a b => .seq (fillG_of hσ a) (fillG_of hσ b)
  | .ite c t e => .ite c (fillG_of hσ t) (fillG_of hσ e)
  | .loop b c => .loop c (fillG_of hσ b)
  | .frame i b j => .frame i j (fillG_of hσ b)
  | .icall i f b x => .icall i f (fillG_of hσ b) (fillG_of hσ x)
  | .call f b => by
    cases b with
    | block is =>
      cases is with
      | nil =>
        simp only [fillCallsG]
        cases h : σ f with
        | none => exact .call f f (.block [])
        | some p => obtain ⟨g, d⟩ := p; exact .hole f (hσ f g d h)
      | cons i is => exact .call f f (.block _)
    | _ => exact .call f f (fillG_of hσ _)

/-- Each of a list of code generic over code it inlines meets `calleeSide`,
from `stubCalleeG` of each of the list over a stub. -/
theorem calleeSide_of_forall₂ {ks k : Nat} {n : String → Nat} {m : Nat} {as bs : List (Prog isa)}
    (hf : List.Forall₂ (FillG k n) as bs) (hks : ks ≤ k)
    (ha : as.all (fun a => stubCalleeG a ks n m) = true) : ∀ b ∈ bs, calleeSide b k m = true := by
  induction hf with
  | nil => intro b hb; cases hb
  | cons h _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ha
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact calleeSide_of_fillG h hks ha.1
    · exact ih ha.2 b hb

/-- Proves `FillG k n a b` of a function's code over a stub (`a`) and over
implementations (`b`), from hypotheses `calleeSide c k m = true` of what
fills each hole (or `∀ o a b, …` of a family of such code): it walks the
function's code, unfolding its definitions, and closes each hole by a
hypothesis. -/
macro "fill_gen" : tactic => `(tactic| repeat' (first
  | with_reducible assumption
  | with_reducible exact FillG.refl _
  | exact FillG.block _
  | exact FillG.hole _ (by with_reducible assumption)
  | exact FillG.hole _ (by solve_by_elim (maxDepth := 3))
  | exact FillG.hole _ (FillG.calleeSide_call _ (by with_reducible assumption))
  | refine FillG.seq ?_ ?_
  | refine FillG.ite _ ?_ ?_
  | refine FillG.loop _ ?_
  | refine FillG.call _ _ ?_
  | refine FillG.frame _ _ ?_
  | refine FillG.icall _ _ ?_ ?_
  | refine FillG.ifp ?_ ?_
  | exact List.Forall₂.nil
  | refine List.Forall₂.cons ?_ ?_
  | simp only [List.nil_append, List.append_eq]
  | (refine FillG.seqs_append (by simp) ?_ ?_; · intro d hd; solve_by_elim (maxDepth := 3))
  | refine FillG.seqs_cons ?_ ?_ (by simp)))

end VG.X86_64.Scrub
