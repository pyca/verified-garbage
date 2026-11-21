module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubSide

/-!
# The cleanup of a function generic over what it calls (x86, 32-bit)

What the cleanup needs of a function's code, callees included
(`X86.Scrub.verifiedScrubbedAll`), is one Boolean, `scrubFSide`, which the
kernel evaluates. A function generic over
an implementation it calls (a variant, `Proof/Variants/<Iface>/X86.lean`)
has code that is not a closed term: it is the function's own code with the
implementation's code where it calls it, and each implementation is
evaluated where it is defined, never in its callers.

`Fill n a b` says that `b` is the code `a` with some of its empty blocks
replaced by code that needs at most `n` bytes of stack and meets `calleeOk`
(`calleeSide`), and its calls' names changed: `a` is the function's code
with a stub, an implementation whose code is `.block []`, and `b` its code
with an implementation. A function proves it once of every implementation,
by `fill_calls` (which walks the function's code, not the
implementation's), from what the implementation states of its own code:
`calleeOk`, a field of the variant proved where it is defined, and its stack.
`scrubFSide_of_fill` then gives `scrubFSide b ts W` from `scrubFSide a ts m`, which
the kernel evaluates once, of the stub's code, and `m + n ≤ W`:

    theorem init_fill (e : Impl.Aes.X86.ExpandKey) (c : Impl.Aes.X86.Ctr32) (sfx : String)
        (he : calleeSide e.code 0 = true) (hc : calleeSide c.code 0 = true) :
        Fill 0 (init stubExpand stubCtr "") (init e c sfx) := by fill_calls

    theorem init_side : scrubFSide (init stubExpand stubCtr "") [] 2336 = true := by lit_decide

    theorem init_scrub (v : Ctr32Impl) : scrubFSide (init v.expand v.callee v.suffix) [] 2336 = true :=
      scrubFSide_of_fill (init_fill _ _ _ (calleeSide_of_eq v.expandStack v.expandScrub)
        (calleeSide_of_eq v.stack v.scrub)) init_side

and the theorem about each variant's function gives `init_scrub v` as
`verifiedScrubbedAll`'s `hs`, with its stack as `W`: nothing in it evaluates
code.
-/

@[expose] public section

namespace VG.X86.Scrub

open VG.X86

/-- What the cleanup of a function that calls `c` needs of it: `calleeOk`,
and at most `n` bytes of stack. -/
noncomputable def calleeSide (c : Prog isa) (n : Nat) : Bool :=
  decide (stackUse c ≤ n) && calleeOk c

theorem calleeOk_iff (c : Prog isa) :
    calleeOk c = true ↔ noIcall c = true ∧ c.allInstrs (fun i => !i.isMmx) = true := by
  induction c with
  | block is =>
    induction is with
    | nil => simp only [calleeOk, noIcall, Code.allInstrs, true_and]
    | cons i is ih =>
      simp only [calleeOk, noIcall, Code.allInstrs, true_and, Bool.and_eq_true] at ih ⊢
  | seq a b iha ihb =>
    simp only [calleeOk, noIcall, Code.allInstrs, Bool.and_eq_true, iha, ihb]
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩
  | ite _ t e iht ihe =>
    simp only [calleeOk, noIcall, Code.allInstrs, Bool.and_eq_true, iht, ihe]
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩
  | loop b _ ih => simp only [calleeOk, noIcall, Code.allInstrs, ih]
  | call _ b ih => simp only [calleeOk, noIcall, Code.allInstrs, ih]
  | frame i b j ih =>
    simp only [calleeOk, noIcall, Code.allInstrs, Bool.and_eq_true, ih]
    exact ⟨fun h => ⟨h.1.2.1, ⟨h.1.1, h.1.2.2⟩, h.2⟩, fun h => ⟨⟨h.2.1.1, h.1, h.2.1.2⟩, h.2.2⟩⟩
  | icall => simp only [calleeOk, noIcall, Bool.false_eq_true, false_and]

/-- `calleeSide` of an implementation from what it states: its stack `k`,
at most `n`, and `calleeOk`. -/
theorem calleeSide_of_eq {c : Prog isa} {k n : Nat} (hs : stackUse c = k) (h : calleeOk c = true)
    (hk : k ≤ n := by decide) : calleeSide c n = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hs ▸ hk, h⟩

/-- `calleeSide` of an implementation that states a bound `k ≤ n` on its stack. -/
theorem calleeSide_of_le {c : Prog isa} {k n : Nat} (hs : stackUse c ≤ k) (h : calleeOk c = true)
    (hk : k ≤ n := by decide) : calleeSide c n = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Nat.le_trans hs hk, h⟩

/-- `b` is `a` with some of its empty blocks replaced by code that meets
`calleeSide _ n` (`hole`), and the names of its calls changed: `a` is a
function's code with a stub for the implementations it calls, and `b` its
code with them. Its blocks, conditions, frames and indirect calls are
`a`'s. -/
inductive Fill (n : Nat) : Prog isa → Prog isa → Prop
  | block (is : List Instr) : Fill n (.block is) (.block is)
  | hole {d : Prog isa} : calleeSide d n = true → Fill n (.block []) d
  | seq {a b a' b' : Prog isa} : Fill n a a' → Fill n b b' → Fill n (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : Fill n t t' → Fill n e e' → Fill n (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : Fill n b b' → Fill n (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : Fill n b b' → Fill n (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : Fill n b b' → Fill n (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      Fill n b b' → Fill n x x' → Fill n (.icall i f b x) (.icall i f b' x')

namespace Fill

variable {n : Nat} {a b : Prog isa}

theorem stackUse_le (h : Fill n a b) : stackUse b ≤ stackUse a + n := by
  induction h with
  | block => exact Nat.le_add_right _ _
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at hd
    simp only [stackUse, Nat.zero_add]; exact hd.1
  | seq _ _ iha ihb => simp only [stackUse]; omega
  | ite _ _ _ iht ihe => simp only [stackUse]; omega
  | loop _ _ ih => simp only [stackUse]; exact ih
  | call _ _ _ ih => simp only [stackUse]; omega
  | frame _ _ _ ih => simp only [stackUse]; omega
  | icall _ _ _ _ ihb ihx => simp only [stackUse]; omega

/-- `b` has no MMX instruction if `a` has none: an implementation has none
(`calleeOk`). -/
theorem noMmx (h : Fill n a b) (ha : a.allInstrs (fun i => !i.isMmx) = true) :
    b.allInstrs (fun i => !i.isMmx) = true := by
  induction h with
  | block => exact ha
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    exact ((calleeOk_iff _).mp hd.2).2
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩
  | icall _ _ _ _ ihb ihx =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ihb ha.1.2⟩, ihx ha.2⟩

/-- The functions `b` may call indirectly are `a`'s: an implementation
calls none (`calleeOk`). -/
theorem inames_eq (h : Fill n a b) : inames b = inames a := by
  induction h with
  | block => rfl
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    exact (inames_of_noIcall ((calleeOk_iff _).mp hd.2).1).trans rfl
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [inames, iha, ihb]
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simp only [inames, ih]
  | icall _ _ _ _ ihb ihx => simp only [inames, ihb, ihx]

theorem mono {m : Nat} (hm : n ≤ m) (h : Fill n a b) : Fill m a b := by
  induction h with
  | block is => exact .block is
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at hd
    exact .hole (calleeSide_of_le hd.1 hd.2 hm)
  | seq _ _ iha ihb => exact .seq iha ihb
  | ite c _ _ iht ihe => exact .ite c iht ihe
  | loop c _ ih => exact .loop c ih
  | call f g _ ih => exact .call f g ih
  | frame i j _ ih => exact .frame i j ih
  | icall i f _ _ ihb ihx => exact .icall i f ihb ihx

/-- `Fill` into code that the implementation chooses (`if p then x else y`,
as `vg_cmac_aes_update` chooses its chaining by its callee's name), where
it chooses `x`: the function proves it of each choice, with a stub of
each. -/
theorem if_pos {p : Prop} [Decidable p] {x y : Prog isa} (h : Fill n a x) (hp : p) :
    Fill n a (if p then x else y) := by
  rw [ite_eq_left hp]; exact h

/-- `Fill` into code that the implementation chooses, where it chooses `y`. -/
theorem if_neg {p : Prop} [Decidable p] {x y : Prog isa} (h : Fill n a y) (hp : ¬p) :
    Fill n a (if p then x else y) := by
  rw [ite_eq_right hp]; exact h

end Fill

/-- `scrubFSide` of a function's code `b` over `W` bytes with the tables
`ts`, whatever the implementations it calls (`Fill n a b`), from
`scrubFSide` of its code `a` with a stub, which the kernel evaluates once,
over `m` bytes, `m + n ≤ W`, and `W` a multiple of 4. -/
theorem scrubFSide_of_fill {n m W : Nat} {ts : List (String × List FnTable)} {a b : Prog isa}
    (hf : Fill n a b) (ha : scrubFSide a ts m = true) (hW : m + n ≤ W ∧ W % 4 = 0 := by decide) :
    scrubFSide b ts W = true := by
  obtain ⟨hs, ht, hm, hp, -⟩ := of_scrubFSide ha
  have hsb := hf.stackUse_le
  have ht' : tablesCall b ts = true := by rw [tablesCall, hf.inames_eq]; exact ht
  simp only [scrubFSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨by omega, ht'⟩, hf.noMmx hm⟩, by omega⟩, hW.2⟩

/-- Proves `Fill n a b` of a function's code with a stub (`a`) and with
implementations (`b`), from hypotheses `calleeSide c n = true` of each
implementation's code `c`: it walks the function's code, unfolding its
definitions, and closes each place it calls an implementation by its
hypothesis (`Fill.hole`). Where the function's code depends on the
implementation otherwise, by an `if p` (`Fill.if_pos`, `Fill.if_neg`), a
hypothesis `p` or `¬p` chooses the branch, and the stub is one that the
same branch is chosen for. -/
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

/-! ## Holes with a budget

`Fill` adds the stack of the implementations, `n`, to the whole of the
function's: too much when the function's deepest path does not call them.
`FillB` instead gives each hole of the stub the stack of what fills it
(`holeStub k`, a frame of `k` bytes around nothing), so that the stub's
`scrubFSide`, over the function's own stack, holds of the code with any
implementation (`scrubFSide_of_fillB`), with nothing added. -/

/-- A stub's place for an implementation that uses at most `k` bytes of
stack: a frame of `k` bytes around nothing, whose stack use is `k`. -/
def holeStub (k : Nat) : Prog isa := .frame (.alloc k) (.block []) (.free k)

/-- `b` is `a` with some of its holes (`holeStub k`) replaced by code that
meets `calleeSide _ k`, and the names of its calls changed: as `Fill`, but
each hole with its budget, and any code matching itself (`refl`), so that
code the function calls whatever the implementation is not walked. -/
inductive FillB : Prog isa → Prog isa → Prop
  | refl (a : Prog isa) : FillB a a
  | hole {k : Nat} {d : Prog isa} : calleeSide d k = true → FillB (holeStub k) d
  | seq {a b a' b' : Prog isa} : FillB a a' → FillB b b' → FillB (.seq a b) (.seq a' b')
  | ite {t e t' e' : Prog isa} (c : Cond) : FillB t t' → FillB e e' → FillB (.ite c t e) (.ite c t' e')
  | loop {b b' : Prog isa} (c : Cond) : FillB b b' → FillB (.loop b c) (.loop b' c)
  | call {b b' : Prog isa} (f g : String) : FillB b b' → FillB (.call f b) (.call g b')
  | frame {b b' : Prog isa} (i j : Instr) : FillB b b' → FillB (.frame i b j) (.frame i b' j)
  | icall {b x b' x' : Prog isa} (i : Instr) (f : String) :
      FillB b b' → FillB x x' → FillB (.icall i f b x) (.icall i f b' x')

namespace FillB

variable {a b : Prog isa}

theorem stackUse_le (h : FillB a b) : stackUse b ≤ stackUse a := by
  induction h with
  | refl => exact Nat.le_refl _
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at hd
    simp only [holeStub, stackUse, frameBytes, Nat.zero_add]; exact hd.1
  | seq _ _ iha ihb => simp only [stackUse]; omega
  | ite _ _ _ iht ihe => simp only [stackUse]; omega
  | loop _ _ ih => simp only [stackUse]; exact ih
  | call _ _ _ ih => simp only [stackUse]; omega
  | frame _ _ _ ih => simp only [stackUse]; omega
  | icall _ _ _ _ ihb ihx => simp only [stackUse]; omega

theorem noMmx (h : FillB a b) (ha : a.allInstrs (fun i => !i.isMmx) = true) :
    b.allInstrs (fun i => !i.isMmx) = true := by
  induction h with
  | refl => exact ha
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    exact ((calleeOk_iff _).mp hd.2).2
  | seq _ _ iha ihb | ite _ _ _ iha ihb =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨iha ha.1, ihb ha.2⟩
  | loop _ _ ih | call _ _ _ ih => simp only [Code.allInstrs] at ha ⊢; exact ih ha
  | frame _ _ _ ih =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ih ha.1.2⟩, ha.2⟩
  | icall _ _ _ _ ihb ihx =>
    simp only [Code.allInstrs, Bool.and_eq_true] at ha ⊢; exact ⟨⟨ha.1.1, ihb ha.1.2⟩, ihx ha.2⟩

theorem inames_eq (h : FillB a b) : inames b = inames a := by
  induction h with
  | refl => rfl
  | hole hd =>
    simp only [calleeSide, Bool.and_eq_true] at hd
    exact (inames_of_noIcall ((calleeOk_iff _).mp hd.2).1).trans rfl
  | seq _ _ iha ihb | ite _ _ _ iha ihb => simp only [inames, iha, ihb]
  | loop _ _ ih | call _ _ _ ih | frame _ _ _ ih => simp only [inames, ih]
  | icall _ _ _ _ ihb ihx => simp only [inames, ihb, ihx]

/-- `FillB` into code that the implementation chooses, where it chooses `x`. -/
theorem if_pos {p : Prop} [Decidable p] {x y : Prog isa} (h : FillB a x) (hp : p) :
    FillB a (if p then x else y) := by
  rw [ite_eq_left hp]; exact h

/-- `FillB` into code that the implementation chooses, where it chooses `y`. -/
theorem if_neg {p : Prop} [Decidable p] {x y : Prog isa} (h : FillB a y) (hp : ¬p) :
    FillB a (if p then x else y) := by
  rw [ite_eq_right hp]; exact h

end FillB

/-- `scrubFSide` of a function's code `b` with the tables `ts`, whatever the
implementations it calls (`FillB a b`), from `scrubFSide` of its code `a`
with stubs that use their implementations' stack (`holeStub`), over the
same `W` bytes, which the kernel evaluates once. -/
theorem scrubFSide_of_fillB {W : Nat} {ts : List (String × List FnTable)} {a b : Prog isa}
    (hf : FillB a b) (ha : scrubFSide a ts W = true) : scrubFSide b ts W = true := by
  obtain ⟨hs, ht, hm, hp, -⟩ := of_scrubFSide ha
  have hsb := hf.stackUse_le
  have ht' : tablesCall b ts = true := by rw [tablesCall, hf.inames_eq]; exact ht
  have h4 : W % 4 = 0 := (of_scrubFSide ha).2.2.2.2
  simp only [scrubFSide, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨by omega, ht'⟩, hf.noMmx hm⟩, hp⟩, h4⟩

/-- `fill_calls` for `FillB`: proves `FillB a b` of a function's code with
stubs (`a`, its holes `holeStub k`) and with implementations (`b`), from
hypotheses `calleeSide c k = true` of each implementation's code `c`. Code
the two share (the code of the functions it calls whatever the
implementation) is matched as one term (`FillB.refl`, at reducible
transparency, so it is not unfolded), and a branch on the implementation is
chosen by a hypothesis `p` or `¬p`. -/
macro "fillB_calls" : tactic => `(tactic| repeat' (first
  | with_reducible exact FillB.refl _
  | exact FillB.hole (by assumption)
  | refine FillB.seq ?_ ?_
  | refine FillB.ite _ ?_ ?_
  | refine FillB.loop _ ?_
  | refine FillB.call _ _ ?_
  | refine FillB.frame _ _ ?_
  | refine FillB.icall _ _ ?_ ?_
  | refine FillB.if_pos ?_ (by assumption)
  | refine FillB.if_neg ?_ (by assumption)))

end VG.X86.Scrub
