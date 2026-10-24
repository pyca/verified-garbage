module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate

/-! # Instruction safety of the x86-64 FFDH exchange -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls allInstrs_inline)

private def codeWith (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.Exchange.code mul (Crt.expLoop mul Crt.tabSelect)
    (.seq (.block r2Head) (R2Words.choice mul))

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

private theorem i_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).allInstrs p = a.allInstrs p := rfl
private theorem i_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).allInstrs p = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa)
    (hp : (codeWith (fun _ _ _ => .block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) :
    (codeWith mul).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.Exchange.code
    VG.Impl.Ffdh.X86_64.Domain.Exchange.body VG.Impl.Ffdh.X86_64.Domain.Exchange.main
    pow Crt.expLoop Crt.expLoopS Crt.expWin
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [i_empty] at hp
  exact hp

private theorem k_seq (a b : Prog isa) : (Code.seq a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_ite (c : Cond) (a b : Prog isa) : (Code.ite c a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_loop (a : Prog isa) (c : Cond) : (Code.loop a c).InlineOk = a.InlineOk := rfl
private theorem k_empty : (Code.block ([] : List Instr) : Prog isa).InlineOk = true := rfl

/-- The template's calls can be inlined if `mul`'s can. -/
private theorem template_inlineOk (mul : Nat → Nat → Nat → Prog isa)
    (hp : (codeWith (fun _ _ _ => .block [])).InlineOk = true)
    (hm : ∀ o a b, (mul o a b).InlineOk = true) :
    (codeWith mul).InlineOk = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.Exchange.code
    VG.Impl.Ffdh.X86_64.Domain.Exchange.body VG.Impl.Ffdh.X86_64.Domain.Exchange.main
    pow Crt.expLoop Crt.expLoopS Crt.expWin
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [k_empty] at hp
  exact hp

/-- The template has no calls of its own: it commutes with inlining. -/
private theorem template_inline (mul : Nat → Nat → Nat → Prog isa) :
    (codeWith mul).inline = codeWith (fun o a b => (mul o a b).inline) := by
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.Exchange.code
    VG.Impl.Ffdh.X86_64.Domain.Exchange.body VG.Impl.Ffdh.X86_64.Domain.Exchange.main
    pow Crt.expLoop Crt.expLoopS Crt.expWin
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

/-- The function as proven: `mont.mm` inline. -/
def exchangeInline (v : RoundImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.Exchange.code v.mont.mm (Crt.expLoop v.mont.mm Crt.tabSelect)
    (.seq (.block r2Head) (R2Words.choice v.mont.mm))

/-- The function as emitted: `mm`, which inlines to `exchangeInline`. -/
def exchangeCode (v : RoundImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.Exchange.code v.mm (Crt.expLoop v.mm Crt.tabSelect)
    (.seq (.block r2Head) (R2Words.choice v.mm))

theorem exchangeCode_inline (v : RoundImpl) : (exchangeCode v).inline = exchangeInline v := by
  have h := template_inline v.mm
  simp only [v.mmInline] at h
  exact h

theorem exchangeCode_inlineOk (v : RoundImpl) : (exchangeCode v).InlineOk = true :=
  template_inlineOk v.mm (by decide +kernel) v.mmOk

private theorem exchangeCode_safe (v : RoundImpl) :
    (exchangeCode v).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := by
  rw [← allInstrs_inline, exchangeCode_inline]
  exact template_instrs _ _ (by decide +kernel) v.arithSafe

theorem exchangeInline_mx (v : RoundImpl) :
    (exchangeInline v).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := exchangeCode_safe v
  rw [← allInstrs_inline, exchangeCode_inline] at h
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem exchangeCode_sp (v : RoundImpl) :
    (exchangeCode v).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := exchangeCode_safe v
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

end VG.Proof.Ffdh.X86_64.Exchange
