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

private theorem instrs_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).allInstrs p = l.all (fun c => c.allInstrs p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.allInstrs, List.all_cons] at ih ⊢; rw [ih]

private theorem instrs_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem instrs_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem instrs_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).allInstrs p = a.allInstrs p := rfl
private theorem instrs_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).allInstrs p = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (hr : round.allInstrs p = true) :
    (codeWith mul round).allInstrs p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.ParameterCandidate.code VG.Impl.Ffdh.X86_64.ParameterCandidate.body VG.Impl.Ffdh.X86_64.ParameterCandidate.testCandidate VG.Impl.Ffdh.X86_64.ParameterCandidate.candidateFilter VG.Impl.Ffdh.X86_64.ParameterCandidate.testQ VG.Impl.Ffdh.X86_64.ParameterCandidate.testP VG.Impl.Ffdh.X86_64.ParameterCandidate.modulusPolicy VG.Impl.Ffdh.X86_64.ParameterCandidate.rounds VG.Impl.Ffdh.X86_64.ParameterCandidate.roundBody VG.Impl.Ffdh.X86_64.ParameterCandidate.roundRun VG.Impl.Ffdh.X86_64.ParameterCandidate.witnessRound VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareModulus VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareR2 VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [instrs_seqs] at *
    | rw [instrs_seq] at *
    | rw [instrs_ite] at *
    | rw [instrs_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [hr]
  repeat' rw [instrs_empty] at hp
  exact hp

private theorem all_seqs (p : Instr → Bool) (l : List (Prog isa)) :
    (seqs l).all p = l.all (fun c => c.all p) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [seqs, List.all_cons, List.all_nil, Bool.and_true]
    | cons b l => simp only [seqs, Code.all, List.all_cons] at ih ⊢; rw [ih]

private theorem all_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).all p = (a.all p && b.all p) := rfl
private theorem all_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).all p = (a.all p && b.all p) := rfl
private theorem all_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).all p = a.all p := rfl
private theorem all_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).all p = true := rfl

private theorem template_all (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).all p = true)
    (hm : ∀ o a b, (mul o a b).all p = true) (hr : round.all p = true) :
    (codeWith mul round).all p = true := by
  unfold codeWith VG.Impl.Ffdh.X86_64.ParameterCandidate.code VG.Impl.Ffdh.X86_64.ParameterCandidate.body VG.Impl.Ffdh.X86_64.ParameterCandidate.testCandidate VG.Impl.Ffdh.X86_64.ParameterCandidate.candidateFilter VG.Impl.Ffdh.X86_64.ParameterCandidate.testQ VG.Impl.Ffdh.X86_64.ParameterCandidate.testP VG.Impl.Ffdh.X86_64.ParameterCandidate.modulusPolicy VG.Impl.Ffdh.X86_64.ParameterCandidate.rounds VG.Impl.Ffdh.X86_64.ParameterCandidate.roundBody VG.Impl.Ffdh.X86_64.ParameterCandidate.roundRun VG.Impl.Ffdh.X86_64.ParameterCandidate.witnessRound VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareModulus VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareR2 VG.Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [all_seq] at *
    | rw [all_ite] at *
    | rw [all_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [hr]
  repeat' rw [all_empty] at hp
  exact hp

def candidateCode (v : RoundImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.ParameterCandidate.code v.mont.mm (R2Words.choice v.mont.mm)
    (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code)

private theorem instrs_call (p : Instr → Bool) (name : String) (c : Prog isa) :
    (Code.call name c).allInstrs p = c.allInstrs p := rfl
private theorem all_call (p : Instr → Bool) (name : String) (c : Prog isa) :
    (Code.call name c).all p = c.all p := rfl

private theorem call_mx (v : RoundImpl) :
    (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  rw [instrs_seq, instrs_seq, instrs_call,
    show (Code.block VG.Impl.MillerRabin.X86_64.Caller.save : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true from by decide,
    show (Code.block VG.Impl.MillerRabin.X86_64.Caller.restore : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true from by decide]
  have hv : v.code.allInstrs (fun i => !loadsMxcsr i) = true := v.mxSafe
  simpa only [Bool.true_and, Bool.and_true] using hv

private theorem call_sp (v : RoundImpl) :
    (VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code).all (fun i => !isa.writesSp i) = true := by
  unfold VG.Impl.MillerRabin.X86_64.Caller.call
  rw [all_seq, all_seq, all_call,
    show (Code.block VG.Impl.MillerRabin.X86_64.Caller.save : Prog isa).all (fun i => !isa.writesSp i) = true from by decide,
    show (Code.block VG.Impl.MillerRabin.X86_64.Caller.restore : Prog isa).all (fun i => !isa.writesSp i) = true from by decide]
  have hv : v.code.all (fun i => !isa.writesSp i) = true := v.spSafe
  simpa only [Bool.true_and, Bool.and_true] using hv

theorem candidateCode_mx (v : RoundImpl) : (candidateCode v).allInstrs (fun i => !loadsMxcsr i) = true := by
  apply template_instrs _ _ _ (by decide +kernel) _ (call_mx v)
  intro o a b
  have h := v.arithSafe o a b
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem candidateCode_sp (v : RoundImpl) : (candidateCode v).all (fun i => !isa.writesSp i) = true := by
  apply template_all _ _ _ (by decide +kernel) _ (call_sp v)
  intro o a b
  apply Code.all_of_allInstrs
  have h := v.arithSafe o a b
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

end VG.Proof.Ffdh.X86_64.ParameterCandidate
