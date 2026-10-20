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

private theorem i_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).allInstrs p = (a.allInstrs p && b.allInstrs p) := rfl
private theorem i_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).allInstrs p = a.allInstrs p := rfl
private theorem i_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).allInstrs p = true := rfl

private theorem a_seq (p : Instr → Bool) (a b : Prog isa) :
    (Code.seq a b).all p = (a.all p && b.all p) := rfl
private theorem a_ite (p : Instr → Bool) (c : Cond) (a b : Prog isa) :
    (Code.ite c a b).all p = (a.all p && b.all p) := rfl
private theorem a_loop (p : Instr → Bool) (a : Prog isa) (c : Cond) :
    (Code.loop a c).all p = a.all p := rfl
private theorem a_empty (p : Instr → Bool) :
    (Code.block ([] : List Instr) : Prog isa).all p = true := rfl

private theorem template_instrs (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).allInstrs p = true)
    (hm : ∀ o a b, (mul o a b).allInstrs p = true) (hb : body.allInstrs p = true) :
    (codeWith mul body).allInstrs p = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  repeat' first
    | rw [all_seqs] at *
    | rw [i_seq] at *
    | rw [i_ite] at *
    | rw [i_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [hb]
  repeat' rw [i_empty] at hp
  exact hp

private theorem template_all (p : Instr → Bool) (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa)
    (hp : (codeWith (fun _ _ _ => .block []) (.block [])).all p = true)
    (hm : ∀ o a b, (mul o a b).all p = true) (hb : body.all p = true) :
    (codeWith mul body).all p = true := by
  unfold codeWith kMainWith millerRabinWith mrRoundWith montSetup at hp ⊢
  repeat' first
    | rw [all_seqs'] at *
    | rw [a_seq] at *
    | rw [a_ite] at *
    | rw [a_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  rw [hb]
  repeat' rw [a_empty] at hp
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

theorem sharedCandidate_mx (v : RoundImpl) :
    (sharedCandidateCode v).allInstrs (fun i => !loadsMxcsr i) = true := by
  apply template_instrs _ _ _ (by decide +kernel) (arith_mx v)
  have h : v.code.allInstrs (fun i => !loadsMxcsr i) = true := v.mxSafe
  simp only [VG.Impl.MillerRabin.X86_64.Caller.call, Code.allInstrs, h]
  decide +kernel

theorem sharedCandidate_sp (v : RoundImpl) :
    (sharedCandidateCode v).all (fun i => !isa.writesSp i) = true := by
  apply template_all _ _ _ (by decide +kernel) (arith_sp v)
  have h : v.code.all (fun i => !isa.writesSp i) = true := v.spSafe
  simp only [VG.Impl.MillerRabin.X86_64.Caller.call, Code.all, h]
  decide +kernel

end VG.Proof.RsaKeyGen.X86_64
