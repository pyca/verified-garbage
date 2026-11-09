module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.ExpImpl
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! # Instruction safety of the x86-64 FFDH private-key validator -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

private def codeWith (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code mul ex (.seq (.block r2Head) (R2Words.choice mul))

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (he : (ex sX sXl).all (fun c => c.allInstrs p) = true) :
    (codeWith mul ex).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [he]
  repeat' rw [i_empty] at hp
  exact hp

/-- The template's calls can be inlined if `mul`'s and `ex`'s can. -/
private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hp : (codeWith (fun _ _ _ => .block []) (fun _ _ => [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) (he : (ex sX sXl).all Code.InlineOk = true) :
    (codeWith mul ex).InlineOk = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [he]
  repeat' rw [k_empty] at hp
  exact hp

/-- The template has no calls of its own: it commutes with inlining. -/
private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) (ex ex' : Nat → Nat → List (Prog isa))
    (he : @List.map (Code Instr Cond) (Prog isa) (@Code.inline Instr Cond) (ex sX sXl) = ex' sX sXl) :
    (codeWith mul ex).inline = codeWith (fun o a b => (mul o a b).inline) ex' := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil, he]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The template loads MXCSR only where `ex` restores it. -/
private theorem template_ctl (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa))
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !loadsMxcsr i) = true) (he : (ex sX sXl).all ctlOk = true) :
    ctlOk (codeWith mul ex) = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  ctl_tac hm he

/-- The function as proven: `mont.mm` inline. -/
def privateInline (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code v.mont.mm (e.code v.mont.mm)
    (.seq (.block r2Head) (R2Words.choice v.mont.mm))

/-- The function as emitted: `mm`, which inlines to `privateInline`. -/
def privateCode (v : RoundImpl) (e : ExpImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code v.mm (e.code v.mm) (.seq (.block r2Head) (R2Words.choice v.mm))

theorem privateCode_inline (v : RoundImpl) (e : ExpImpl) : (privateCode v e).inline = privateInline v e := by
  have h := template_inline v.mm (e.code v.mm) (e.code fun o a b => (v.mm o a b).inline)
    (e.inline v.mm _ _ (Or.inl ⟨rfl, rfl⟩))
  simp only [v.mmInline] at h
  exact h

theorem privateCode_inlineOk (v : RoundImpl) (e : ExpImpl) : (privateCode v e).InlineOk = true :=
  template_inlineOk v.mm _ (by decide +kernel) v.mmOk (e.inlineOk v.mm v.mmOk _ _ (Or.inl ⟨rfl, rfl⟩))

theorem privateInline_ctl (v : RoundImpl) (e : ExpImpl) : ctlOk (privateInline v e) = true :=
  template_ctl _ _ (mul_and_left v.arithSafe) (e.ctl _ (mul_and_left v.arithSafe) _ _ (Or.inl ⟨rfl, rfl⟩))

theorem privateCode_sp (v : RoundImpl) (e : ExpImpl) :
    (privateCode v e).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  rw [← allInstrs_inline, privateCode_inline]
  exact template_instrs _ _ _ (by decide +kernel) (mul_and_right v.arithSafe)
    (e.spSafe _ (mul_and_right v.arithSafe) _ _ (Or.inl ⟨rfl, rfl⟩))

end VG.Proof.Ffdh.X86_64.CheckPrivate
