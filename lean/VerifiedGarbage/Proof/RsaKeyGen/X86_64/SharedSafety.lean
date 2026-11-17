module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! # Instruction safety of generic RSA candidate callers -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

private theorem all_seqs' (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).all p = l.all (fun c => c.all p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.all, List.all_cons] at ih ⊢; rw [ih]

/-! The lemmas about `Code.allInstrs`, `Code.all` and `ctlC` with the code's types written as `simp` finds
them: it reduces `isa.Instr` in the code before it looks a lemma up, and a lemma stated with `Prog isa`
never matches. -/

private theorem i_seqs (p : Instr → Bool) (l : List (Code Instr Cond)) :
    @Code.allInstrs Instr Cond p (seqs l) = l.all (fun c => @Code.allInstrs Instr Cond p c) := all_seqs p l
private theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Code Instr Cond) :
    @Code.allInstrs Instr Cond p (@Code.ite Instr Cond c a b) = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop (p : Instr → Bool) (a : Code Instr Cond) (c : Cond) :
    @Code.allInstrs Instr Cond p (@Code.loop Instr Cond a c) = a.allInstrs p := rfl
private theorem i_empty (p : Instr → Bool) :
    @Code.allInstrs Instr Cond p (@Code.block Instr Cond []) = true := rfl

private theorem a_seqs (p : Instr → Bool) (l : List (Code Instr Cond)) :
    @Code.all Instr Cond p (seqs l) = l.all (fun c => @Code.all Instr Cond p c) := all_seqs' p l
private theorem a_ite (p : Instr → Bool) (c : Cond) (a b : Code Instr Cond) :
    @Code.all Instr Cond p (@Code.ite Instr Cond c a b) = (a.all p && b.all p) := rfl
private theorem a_loop (p : Instr → Bool) (a : Code Instr Cond) (c : Cond) :
    @Code.all Instr Cond p (@Code.loop Instr Cond a c) = a.all p := rfl
private theorem a_empty (p : Instr → Bool) :
    @Code.all Instr Cond p (@Code.block Instr Cond []) = true := rfl

private theorem c_seqs (l : List (Code Instr Cond)) : ctlC (seqs l) = l.all ctlC := ctlC_seqs l
private theorem c_ite (c : Cond) (a b : Code Instr Cond) :
    ctlC (@Code.ite Instr Cond c a b) = (ctlC a && ctlC b) := rfl
private theorem c_loop (a : Code Instr Cond) (c : Cond) : ctlC (@Code.loop Instr Cond a c) = ctlC a := rfl
private theorem c_empty : ctlC (@Code.block Instr Cond []) = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (hb : body.allInstrs p = true) :
    (codeWith mul body).allInstrs p = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  simp only [i_seqs, i_ite, i_loop, List.all_append, List.all_cons, hm, hb, i_empty] at hp ⊢
  exact hp

private theorem template_ctlC (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : ctlC (codeWith (fun _ _ _ => .block []) (.block [])) = true)
    (hm : ∀ o a b, ctlC (mul o a b) = true) (hb : ctlC body = true) :
    ctlC (codeWith mul body) = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  simp only [c_seqs, c_ite, c_loop, List.all_append, List.all_cons, hm, hb, c_empty] at hp ⊢
  exact hp

private theorem template_all (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).all p = true)
    (hm : ∀ o a b, (mul o a b).all p = true) (hb : body.all p = true) :
    (codeWith mul body).all p = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  simp only [a_seqs, a_ite, a_loop, List.all_append, List.all_cons, hm, hb, a_empty] at hp ⊢
  exact hp

private theorem arith_mx (v : RoundImpl) (o a b : Nat) :
    (v.mm o a b).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := v.arithSafe o a b
  rw [← VG.Proof.Bignum.X86_64.allInstrs_inline, v.mmInline, Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at h
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

private theorem arith_sp (v : RoundImpl) (o a b : Nat) :
    (v.mm o a b).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := v.arithSafe o a b
  rw [← VG.Proof.Bignum.X86_64.allInstrs_inline, v.mmInline, Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at h
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

/-- The candidate as emitted: its products call `v.mm`'s function. -/
def sharedCandidateCode (v : RoundImpl) : Prog isa :=
  codeWith v.mm (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code)

/-- The candidate loads MXCSR only where the round restores it. -/
theorem sharedCandidate_ctlC (v : RoundImpl) : ctlC (sharedCandidateCode v) = true := by
  apply template_ctlC _ _ (by decide +kernel) (fun o a b => ctlC_of_noLoad (arith_mx v o a b))
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  rw [ctlC_seq, ctlC_seq, ctlC_call, v.ctl,
    show ctlC (Code.block VG.Impl.MillerRabin.X86_64.Caller.save : Prog isa) = true from by decide +kernel,
    show ctlC (Code.block VG.Impl.MillerRabin.X86_64.Caller.restore : Prog isa) = true from by decide +kernel]
  rfl

theorem sharedCandidate_ctl (v : RoundImpl) : ctlOk (sharedCandidateCode v) = true :=
  ctlOk_of_ctlC (sharedCandidate_ctlC v)

theorem sharedCandidate_sp (v : RoundImpl) :
    (sharedCandidateCode v).all (fun i => !isa.writesSp i) = true := by
  apply template_all _ _ _ (by decide +kernel) (arith_sp v)
  have h : v.code.all (fun i => !isa.writesSp i) = true := v.spSafe
  simp only [VG.Impl.MillerRabin.X86_64.Caller.call, Code.all, h]
  decide +kernel

end VG.Proof.RsaKeyGen.X86_64
