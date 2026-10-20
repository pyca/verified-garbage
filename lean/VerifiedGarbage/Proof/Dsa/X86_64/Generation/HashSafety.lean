module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Instruction safety of every seed hash and wrapped-seed contribution -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

structure HashSafety (H : Stream) : Prop where
  init : generationSafe H.initC
  update : generationSafe H.updC
  finish : generationSafe H.finC

theorem hashLabel_safe {H : Stream} (h : HashSafety H) (o : Nat) :
    generationSafe (Impl.RsaOaep.X86_64.hashLabel H o) := by
  unfold Impl.RsaOaep.X86_64.hashLabel Impl.Mgf1.X86_64.seqs
  repeat' apply generationSafe.seq
  all_goals first | exact h.init | exact h.update | exact h.finish | rfl

theorem seedAdd_safe (n : Nat) : generationSafe (seedAdd n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (show generationSafe (.block (seedAddByte n)) from rfl).seq ih

theorem seedHash_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256) :
    generationSafe (seedHash H1 H256) := by
  exact (show generationSafe (.block hashTest) from rfl).seq
    ((hashLabel_safe h1 _).ite (hashLabel_safe h256 _) _)

theorem pHashOne_safe {H : Stream} (h : HashSafety H) (len count j : Nat) :
    generationSafe (pHashOne H len count j) := by
  exact ((show generationSafe (.block (seedInputArgs j)) from rfl).seq
    ((seedAdd_safe len).seq (hashLabel_safe h _))).seq
    ((show generationSafe (.block (hashCopyArgs len count j)) from rfl).seq (by unfold generationSafe; decide +kernel))

theorem pHashPrefix_safe {H : Stream} (h : HashSafety H) (len count k : Nat) :
    generationSafe (pHashPrefix H len count k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih.seq (pHashOne_safe h len count k)

theorem pHashes_safe {H : Stream} (h : HashSafety H) (len count : Nat) :
    generationSafe (pHashes H len count) := pHashPrefix_safe h len count (count + 1)

end VG.Proof.Dsa.X86_64.Generation
