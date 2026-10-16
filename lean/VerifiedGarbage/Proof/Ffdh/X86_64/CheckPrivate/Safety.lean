module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Words
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Instruction safety of the x86-64 FFDH private-key validator -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Rsa.X86_64

private def codeWith (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code mul (Crt.expLoop mul Crt.tabSelect)
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
  unfold codeWith VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.main
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail pow Crt.expLoop Crt.expLoopS Crt.expWin
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old at hp ⊢
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

def privateCode (v : RoundImpl) : Prog isa :=
  VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code v.mont.mm (Crt.expLoop v.mont.mm Crt.tabSelect)
    (.seq (.block r2Head) (R2Words.choice v.mont.mm))

private theorem privateCode_safe (v : RoundImpl) :
    (privateCode v).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true := by
  exact template_instrs _ _ (by decide +kernel) v.arithSafe

theorem privateCode_mx (v : RoundImpl) :
    (privateCode v).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := privateCode_safe v
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).1

theorem privateCode_sp (v : RoundImpl) :
    (privateCode v).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have h := privateCode_safe v
  rw [Code.allInstrs_eq] at h ⊢
  exact List.all_eq_true.mpr fun i hi => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h i hi)).2

end VG.Proof.Ffdh.X86_64.CheckPrivate
