module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! # Instruction safety of the x86-64 FFDH domain validator -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

private def codeWith (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code mul ex (.seq (.block r2Head) (R2Words.choice mul))

/-! The same lemmas with the instruction and condition types as the code has them (`simp` matches
them by their names, where `rw` unfolds `isa`). -/

private theorem all_seqs' (p : Instr → Bool) (l : List (Code Instr Cond)) :
    @Code.allInstrs Instr Cond p (seqs l) = l.all (fun c => @Code.allInstrs Instr Cond p c) := all_seqs p l
private theorem i_seq' (p : Instr → Bool) (a b : Code Instr Cond) :
    @Code.allInstrs Instr Cond p (@Code.seq Instr Cond a b) = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_ite' (p : Instr → Bool) (c : Cond) (a b : Code Instr Cond) :
    @Code.allInstrs Instr Cond p (@Code.ite Instr Cond c a b) = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop' (p : Instr → Bool) (a : Code Instr Cond) (c : Cond) :
    @Code.allInstrs Instr Cond p (@Code.loop Instr Cond a c) = a.allInstrs p := rfl
private theorem k_seq' (a b : Code Instr Cond) :
    Code.InlineOk (@Code.seq Instr Cond a b) = (Code.InlineOk a && Code.InlineOk b) := rfl
private theorem k_ite' (c : Cond) (a b : Code Instr Cond) :
    Code.InlineOk (@Code.ite Instr Cond c a b) = (Code.InlineOk a && Code.InlineOk b) := rfl
private theorem k_loop' (a : Code Instr Cond) (c : Cond) :
    Code.InlineOk (@Code.loop Instr Cond a c) = Code.InlineOk a := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (he : (ex sEp sEl).all (fun c => c.allInstrs p) = true) :
    (codeWith mul ex).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 Crt.redc pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  simp only [all_seqs', i_seq', i_ite', i_loop', List.all_append, List.all_cons] at hp ⊢
  repeat' rw [hm]
  rw [he]
  repeat' rw [i_empty] at hp
  exact hp

/-- The template's calls can be inlined if `mul`'s and `ex`'s can. -/
private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) (he : (ex sEp sEl).all Code.InlineOk = true) :
    (codeWith mul ex).InlineOk = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 Crt.redc pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  simp only [inlineOk_seqs, k_seq', k_ite', k_loop', List.all_append, List.all_cons] at hp ⊢
  repeat' rw [hm]
  rw [he]
  repeat' rw [k_empty] at hp
  exact hp

/-- The template has no calls of its own: it commutes with inlining. -/
private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) (ex ex' : Nat → Nat → List (Prog isa))
    (he : @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (ex sEp sEl) = ex' sEp sEl) :
    (codeWith mul ex).inline = codeWith (fun o a b => (mul o a b).inline) ex' := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 Crt.redc pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil, he]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The template loads MXCSR only where `ex` restores it. -/
private theorem template_ctl (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !loadsMxcsr i) = true) (he : (ex sEp sEl).all ctlOk = true) :
    ctlOk (codeWith mul ex) = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 Crt.redc pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- `ctl_tac hm he`, with its second alternative at reducible transparency: where the code is not `mul`'s,
  -- the `exact` otherwise compares `Code.allInstrs` of the two by evaluating it on the template's blocks
  repeat' first
    | with_reducible exact he
    | with_reducible exact ctlOk_of_noLoad (hm _ _ _)
    | decide +kernel
    | (apply ctlOk_seqs_of
       simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
       try and_intros)
    | apply ctlOk_seq_of
    | apply ctlOk_ite_of
    | apply ctlOk_loop_of

/-- The validator as proven: `mont.mm` inline. -/
def domainInline (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code v.mont.mm (e.code v.mont.mm)
    (.seq (.block r2Head) (R2Words.choice v.mont.mm))

/-- The validator as emitted: `mm`, which inlines to `domainInline`. -/
def domainCode (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code v.mm (e.code v.mm) (.seq (.block r2Head) (R2Words.choice v.mm))

theorem domainCode_inline (v : RoundImpl) (e : ExpImpl) : (domainCode v e).inline = domainInline v e := by
  have h := template_inline v.mm (e.code v.mm) (e.code fun o a b => (v.mm o a b).inline)
    (e.inline v.mm _ _ (Or.inr ⟨rfl, rfl⟩))
  simp only [v.mmInline] at h
  exact h

theorem domainCode_inlineOk (v : RoundImpl) (e : ExpImpl) : (domainCode v e).InlineOk = true :=
  template_inlineOk v.mm _ (by decide +kernel) v.mmOk (e.inlineOk v.mm v.mmOk _ _ (Or.inr ⟨rfl, rfl⟩))

theorem domainInline_ctl (v : RoundImpl) (e : ExpImpl) : ctlOk (domainInline v e) = true :=
  template_ctl _ _ (mul_and_left v.arithSafe) (e.ctl _ (mul_and_left v.arithSafe) _ _ (Or.inr ⟨rfl, rfl⟩))

theorem domainCode_sp (v : RoundImpl) (e : ExpImpl) :
    (domainCode v e).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [← allInstrs_inline, domainCode_inline]
  exact template_instrs _ _ _ (by decide +kernel) (mul_and_right v.arithSafe)
    (e.spSafe _ (mul_and_right v.arithSafe) _ _ (Or.inr ⟨rfl, rfl⟩))

end VG.Proof.Ffdh.X86_64.CheckDomain
