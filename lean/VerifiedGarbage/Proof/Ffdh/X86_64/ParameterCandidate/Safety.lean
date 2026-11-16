module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Caller
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: instruction safety and stack depth -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

private def codeWith (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.ParameterCandidate.code mul (R2Words.choice mul) round

/-! The lemmas about `ctlC` and `Code.all` with the code's types written as `simp` finds them: it reduces
`isa.Instr` in the code before it looks a lemma up, and a lemma stated with `Prog isa` never matches. -/

private theorem ctlC_seqs' (l : List (Code Instr Cond)) : ctlC (seqs l) = l.all ctlC := ctlC_seqs l
private theorem ctlC_seq' (a b : Code Instr Cond) : ctlC (@Code.seq Instr Cond a b) = (ctlC a && ctlC b) := rfl
private theorem ctlC_ite' (c : Cond) (a b : Code Instr Cond) :
    ctlC (@Code.ite Instr Cond c a b) = (ctlC a && ctlC b) := rfl
private theorem ctlC_loop' (a : Code Instr Cond) (c : Cond) : ctlC (@Code.loop Instr Cond a c) = ctlC a := rfl
private theorem ctlC_empty' : ctlC (@Code.block Instr Cond []) = true := rfl

private theorem template_ctlC (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hp : ctlC (codeWith (fun _ _ _ => .block []) (.block [])) = true)
    (hm : ∀ o a b, ctlC (mul o a b) = true) (hr : ctlC round = true) :
    ctlC (codeWith mul round) = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.ParameterCandidate.code VG.Impl.Ffdh.X86_64.ParameterCandidate.body VG.Impl.Ffdh.X86_64.ParameterCandidate.testCandidate VG.Impl.Ffdh.X86_64.ParameterCandidate.candidateFilter VG.Impl.Ffdh.X86_64.ParameterCandidate.sieveQ VG.Impl.Ffdh.X86_64.ParameterCandidate.sieveP VG.Impl.Ffdh.X86_64.ParameterCandidate.testFirst VG.Impl.Ffdh.X86_64.ParameterCandidate.testQ VG.Impl.Ffdh.X86_64.ParameterCandidate.testP VG.Impl.Ffdh.X86_64.ParameterCandidate.phaseTest VG.Impl.Ffdh.X86_64.ParameterCandidate.modulusPolicy VG.Impl.Ffdh.X86_64.ParameterCandidate.rounds VG.Impl.Ffdh.X86_64.ParameterCandidate.roundBody VG.Impl.Ffdh.X86_64.ParameterCandidate.roundRun VG.Impl.Ffdh.X86_64.ParameterCandidate.witnessRound VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareModulus VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareR2 VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  simp only [ctlC_seqs', ctlC_seq', ctlC_ite', ctlC_loop', List.all_cons, hm, hr, ctlC_empty'] at hp ⊢
  exact hp

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).all p = l.all (fun c => c.all p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.all, List.all_cons] at ih ⊢; rw [ih]

private theorem all_seqs' (p : Instr → Bool) (l : List (Code Instr Cond)) :
    @Code.all Instr Cond p (seqs l) = l.all (fun c => @Code.all Instr Cond p c) := all_seqs p l
private theorem all_seq' (p : Instr → Bool) (a b : Code Instr Cond) :
    @Code.all Instr Cond p (@Code.seq Instr Cond a b) = (a.all p && b.all p) := rfl
private theorem all_ite' (p : Instr → Bool) (c : Cond) (a b : Code Instr Cond) :
    @Code.all Instr Cond p (@Code.ite Instr Cond c a b) = (a.all p && b.all p) := rfl
private theorem all_loop' (p : Instr → Bool) (a : Code Instr Cond) (c : Cond) :
    @Code.all Instr Cond p (@Code.loop Instr Cond a c) = a.all p := rfl
private theorem all_empty' (p : Instr → Bool) :
    @Code.all Instr Cond p (@Code.block Instr Cond []) = true := rfl
private theorem all_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).all p = (a.all p && b.all p) := rfl

private theorem template_all (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).all p = true)
    (hm : ∀ o a b, (mul o a b).all p = true) (hr : round.all p = true) :
    (codeWith mul round).all p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.ParameterCandidate.code VG.Impl.Ffdh.X86_64.ParameterCandidate.body VG.Impl.Ffdh.X86_64.ParameterCandidate.testCandidate VG.Impl.Ffdh.X86_64.ParameterCandidate.candidateFilter VG.Impl.Ffdh.X86_64.ParameterCandidate.sieveQ VG.Impl.Ffdh.X86_64.ParameterCandidate.sieveP VG.Impl.Ffdh.X86_64.ParameterCandidate.testFirst VG.Impl.Ffdh.X86_64.ParameterCandidate.testQ VG.Impl.Ffdh.X86_64.ParameterCandidate.testP VG.Impl.Ffdh.X86_64.ParameterCandidate.phaseTest VG.Impl.Ffdh.X86_64.ParameterCandidate.modulusPolicy VG.Impl.Ffdh.X86_64.ParameterCandidate.rounds VG.Impl.Ffdh.X86_64.ParameterCandidate.roundBody VG.Impl.Ffdh.X86_64.ParameterCandidate.roundRun VG.Impl.Ffdh.X86_64.ParameterCandidate.witnessRound VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareModulus VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareR2 VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  simp only [all_seqs', all_seq', all_ite', all_loop', List.all_cons, hm, hr, all_empty'] at hp ⊢
  exact hp

def candidateCode (v : RoundImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.ParameterCandidate.code v.mont.mm (R2Words.choice v.mont.mm)
    (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code)

private theorem all_call (p : Instr → Bool) (name : String) (c : Prog isa) :
    (Code.call name c).all p = c.all p := rfl

private theorem call_ctlC (v : RoundImpl) :
    ctlC (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code) = true := by
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  rw [ctlC_seq, ctlC_seq, ctlC_call, v.ctl,
    show ctlC (Code.block VG.Impl.MillerRabin.X86_64.Caller.save : Prog isa) = true from by decide +kernel,
    show ctlC (Code.block VG.Impl.MillerRabin.X86_64.Caller.restore : Prog isa) = true from by decide +kernel]
  rfl

private theorem call_sp (v : RoundImpl) :
    (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code).all (fun i => !isa.writesSp i) = true := by
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  rw [all_seq, all_seq, all_call,
    show (Code.block VG.Impl.MillerRabin.X86_64.Caller.save : Prog isa).all (fun i => !isa.writesSp i) = true from by decide,
    show (Code.block VG.Impl.MillerRabin.X86_64.Caller.restore : Prog isa).all (fun i => !isa.writesSp i) = true from by decide]
  have hv : v.code.all (fun i => !isa.writesSp i) = true := v.spSafe
  simpa only [Bool.true_and, Bool.and_true] using hv

/-- The candidate loads MXCSR only where the round restores it. -/
theorem candidateCode_ctlC (v : RoundImpl) : ctlC (candidateCode v) = true := by
  apply template_ctlC _ _ (by decide +kernel) _ (call_ctlC v)
  intro o a b
  apply ctlC_of_noLoad
  have h := v.arithSafe o a b
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem candidateCode_ctl (v : RoundImpl) : ctlOk (candidateCode v) = true :=
  ctlOk_of_ctlC (candidateCode_ctlC v)

theorem candidateCode_sp (v : RoundImpl) : (candidateCode v).all (fun i => !isa.writesSp i) = true := by
  apply template_all _ _ _ (by decide +kernel) _ (call_sp v)
  intro o a b
  apply Code.all_of_allInstrs
  have h := v.arithSafe o a b
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

end VG.Proof.Ffdh.X86_64.ParameterCandidate
