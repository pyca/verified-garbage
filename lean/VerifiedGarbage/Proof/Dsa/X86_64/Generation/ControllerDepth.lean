module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerDepth
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Search controllers inherit their bodies’ stack bounds -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_depth {body : Prog isa} (hb : callerDepth body) (limit stride : Nat) :
    callerDepth (pSearch body limit stride) := by
  unfold callerDepth at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 192 by decide)

theorem tapeLoop_depth {body : Prog isa} (hb : callerDepth body) (slots : TapeSlots) (width : Nat) :
    callerDepth (tapeLoop slots width body) := by
  unfold callerDepth at hb ⊢
  simp only [tapeLoop, tapeIteration, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 192 by decide)

theorem primeSearch_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Nat → Prog isa) (hp : ∀ bits, callerDepth (prime bits)) (pLen qLen : Nat) :
    callerDepth (primeSearch H1 H256 prime pLen qLen) :=
  (callerDepth.of (generationDepth.block _)).seq
    (pSearch_depth (pAttempt_depth h1 h256 prime hp pLen qLen) _ _)

theorem generatorSearch_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    callerDepth (generatorSearch sq mul len) :=
  tapeLoop_depth (callerDepth.of (generatorStep_depth sq mul hs hm len)) _ _

theorem onSuccess_depth {body : Prog isa} (hb : callerDepth body) :
    callerDepth (onSuccess body) :=
  (callerDepth.of (generationDepth.block _)).seq (hb.ite (callerDepth.of (generationDepth.block _)) _)

end VG.Proof.Dsa.X86_64.Generation
