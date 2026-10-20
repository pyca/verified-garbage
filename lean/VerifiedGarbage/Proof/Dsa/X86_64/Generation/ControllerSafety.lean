module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerSafety
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Bounded seed, prime, and generator controllers inherit their bodies' safety -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_safe {body : Prog isa} (hb : generationSafe body) (limit stride : Nat) :
    generationSafe (pSearch body limit stride) := by
  unfold generationSafe at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, Code.allInstrs, hb]
  rfl

theorem tapeLoop_safe {body : Prog isa} (hb : generationSafe body) (slots : TapeSlots) (width : Nat) :
    generationSafe (tapeLoop slots width body) := by
  unfold generationSafe at hb ⊢
  simp only [tapeLoop, tapeIteration, Code.allInstrs, hb]
  rfl

theorem primeSearch_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) (pLen qLen : Nat) :
    generationSafe (primeSearch H1 H256 mul round pLen qLen) :=
  (show generationSafe (.block controlBase) from rfl).seq
    (pSearch_safe (pAttempt_safe h1 h256 mul round hm hr pLen qLen) _ _)

theorem generatorSearch_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorSearch sq mul len) :=
  tapeLoop_safe (generatorStep_safe sq mul hs hm len) _ _

theorem onSuccess_safe {body : Prog isa} (hb : generationSafe body) :
    generationSafe (onSuccess body) :=
  (show generationSafe (.block successStatus) from rfl).seq (hb.ite (show generationSafe (.block []) from rfl) _)

end VG.Proof.Dsa.X86_64.Generation
