module

public import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-!
# Code templates over a Montgomery multiplication, with calls

Code built from a template by a Montgomery multiplication `mul` (FFDH's
domain operations) is emitted with `mul` calling a function, and proven
for its inlined form. When the template's own code has no calls, the
template commutes with inlining, and its calls can be inlined if `mul`'s
can (`Code.InlineOk`). These are the lemmas for `seqs`, through which the
templates' proofs (the FFDH `Safety` files) rewrite.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64

theorem noCalls_seqs (l : List (Prog isa)) : (seqs l).noCalls = l.all Code.noCalls := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.noCalls, List.all_cons] at ih ⊢; rw [ih]

theorem inlineOk_seqs (l : List (Prog isa)) : (seqs l).InlineOk = l.all Code.InlineOk := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.InlineOk, List.all_cons] at ih ⊢; rw [ih]

/-! `simp` finds the lemmas about `Code.inline` below only when they name its
types as `Instr` and `Cond`, which are what `isa.Instr` and `isa.Cond` in
code reduce to. -/

theorem inline_seqs (l : List (Code Instr Cond)) :
    @Code.inline Instr Cond (seqs l) = seqs (l.map (@Code.inline Instr Cond)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [seqs, Code.inline, List.map_cons] at ih ⊢; rw [ih]

theorem inline_of_noCalls {c : Prog isa} (h : c.noCalls = true) : @Code.inline Instr Cond c = c :=
  Code.inline_of_noCalls h

/-- As `List.map_append` leaves the lists of `inline_seqs`. -/
theorem map_inline_of_noCalls {l : List (Code Instr Cond)} (h : l.all Code.noCalls = true) :
    @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, inline_of_noCalls h.1, ih h.2]

theorem allInstrs_inline (p : Instr → Bool) (c : Prog isa) : c.inline.allInstrs p = c.allInstrs p := by
  induction c with
  | icall => rfl
  | block _ => rfl
  | seq a b iha ihb => simp only [Code.inline, Code.allInstrs, iha, ihb]
  | ite _ t e iht ihe => simp only [Code.inline, Code.allInstrs, iht, ihe]
  | loop b _ ih => simp only [Code.inline, Code.allInstrs, ih]
  | call _ _ _ => rfl
  | frame _ _ _ ih => simp only [Code.inline, Code.allInstrs, ih]

/-- The arguments of a Montgomery multiplication do not write `rsp`. -/
theorem args_inlineOk (o a b : Nat) :
    (Code.block (Impl.Bignum.X86_64.MontFn.args o a b) : Prog isa).InlineOk = true := rfl

/-- A call of a function that calls none and leaves `rsp` alone can be inlined. -/
theorem call_inlineOk {name : String} {body : Prog isa}
    (h : (body.noCalls && body.allInstrs Instr.rspFree) = true) (o a b : Nat) :
    (Impl.Bignum.X86_64.MontFn.call name body o a b).InlineOk = true := by
  simp only [Impl.Bignum.X86_64.MontFn.call, Code.InlineOk, h, Bool.and_true]
  exact args_inlineOk o a b

/-- The inlined form of such a call can be inlined too: it has no calls. -/
theorem inline_call_inlineOk {name : String} {body : Prog isa} (h : body.InlineOk = true) (o a b : Nat) :
    (Impl.Bignum.X86_64.MontFn.call name body o a b).inline.InlineOk = true := by
  simp only [Impl.Bignum.X86_64.MontFn.call, Code.inline, Code.InlineOk, h, Bool.and_true]
  exact args_inlineOk o a b

theorem inline_call_inline {name : String} {body : Prog isa} (h : body.noCalls = true) (o a b : Nat) :
    (Impl.Bignum.X86_64.MontFn.call name body o a b).inline.inline =
      (Impl.Bignum.X86_64.MontFn.call name body o a b).inline := by
  simp only [Impl.Bignum.X86_64.MontFn.call, Code.inline, Code.inline_of_noCalls h]

/-- `Verified.of_inline`, from the inlined code's proof against `k₀`. -/
theorem Verified.of_inline_verified {c : Prog isa} (hc : c.InlineOk = true) {k₀ k : Contract isa}
    (hv : Verified target c.inline k₀) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (hole (s.gpr .rsp)) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (hole (s.gpr .rsp)) hv u))
    (hrsp : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp) : Verified target c k :=
  Verified.of_inline hc hv.1 hv.2.1 himp hclear hpost hrsp

end VG.Proof.Bignum.X86_64
