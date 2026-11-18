module

import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytes
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytes
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ProbablePrime
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ProbablePrime
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopInit
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRound
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawCopyCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawRound
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawBuffer
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SampleRound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sample
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sample
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TestWitness
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
meta import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceSample
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TestWitness
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleState
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoadWitness
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import Aesop.BuiltinRules
import VerifiedGarbage.Proof.RsaKeyGen.Gcd
meta import VerifiedGarbage.Proof.RsaKeyGen.Gcd
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sample
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.RoundTail
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SampleRound
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.LoopStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HeaderCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTrial
meta import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyR1CT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyR1CT
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Impl.Bignum.X86_64
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Impl.Bignum.X86_64
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
meta import VerifiedGarbage.Impl.Dsa.Generation.Layout
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ProbablePrime
meta import VerifiedGarbage.Proof.Bignum.WorkFrame
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup

/-! ### `Dsa.X86_64.ProbablePrime.Body`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.ProbablePrime.Exit`, which only this module used -/

section

/-! # The probable-prime test's exit: `used`, and the status in `rax` -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The test's status as the function returns it. -/
def returned (stat : BitVec 64) : BitVec 64 := stat - (stat >>> 1)

theorem exit_ok {s : State} {B U : Addr} (hdi : s.gpr .rdi = B)
    (hu1 : InRegions (s.rd ++ s.wr) (off B 200) 8) (hs1 : InRegions (s.rd ++ s.wr) (off B 232) 8)
    (hf : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 48) 8)
    (hU : word s.mem (s.gpr .rsp) 48 = U) (hu : InRegions s.wr U 8)
    (hsep : Mem.Sep (off B 232) 8 U 8) :
    WP isa (.block exit) s fun t =>
      t.gpr .rax = returned (word s.mem B 232) ∧
      t.mem = s.mem.writeW U (word s.mem B 200) ∧
      Keep [.rax, .rcx, .r8] s t := by
  obtain hread : (s.mem.writeW U (word s.mem B 200)).readW (off B 232) 64 = word s.mem B 232 := by
    rw [Mem.readW_writeW_sep hsep (by decide)]
  obtain h0 : ∀ a : Addr, a + BitVec.ofInt 64 0 = a := fun a => by
    rw [show BitVec.ofInt 64 0 = 0 by decide]; exact BitVec.add_zero a
  refine WP.mono (WP.keep [.rax, .rcx, .r8] (Q := fun t =>
      t.gpr .rax = returned (word s.mem B 232) ∧
      t.mem = s.mem.writeW U (word s.mem B 200)) (by
    xrun [Impl.Dsa.X86_64.ProbablePrime.exit, sp, State.ea, BitVec.ofInt_natCast,
      Impl.Bignum.X86_64.hdr, hdi, kUsed, kStat, VG.Impl.Bignum.sFn, hdrOff, Nat.reduceAdd, Nat.reduceMul,
      h0, hu1, hs1, hf, hU, hu, hread]
    rfl) rfl) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

/-! ### `Dsa.X86_64.ProbablePrime.Args`, which only this module used -/

section

/-! # The probable-prime test's arguments in the arithmetic workspace's header

The block writes the test's header arguments from registers, and those of
the size from the size in `r8`: as `argumentWrites` of `argList`, whose
frame words are the registers `rsi`, `r9` and `rcx`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.X86_64.ProbablePrime
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Dsa.X86_64.Generation (argumentWrites argumentValue argumentFits)

/-- The arguments, with the working space, `rand` and `rand_len` as the
words 0, 1 and 2. -/
def argList (bits : Nat) : List HeaderArgument :=
  [⟨kOut, .frame 0 Impl.Dsa.Generation.Layout.witness⟩, ⟨kLen, .literal (draw bits)⟩,
   ⟨kUsedP, .literal (len bits)⟩, ⟨kChecks, .literal (checks bits)⟩,
   ⟨20, .frame 0 (candidate bits)⟩, ⟨kRand, .frame 1 0⟩, ⟨kRandLen, .frame 2 0⟩,
   ⟨kUsed, .literal 0⟩]

/-- The registers the arguments come from. -/
def argWords (s : State) (k : Nat) : BitVec 64 :=
  if k = 0 then s.gpr .rsi else if k = 1 then s.gpr .r9 else s.gpr .rcx

theorem argList_fits {bits : Nat} (hb : bits ≤ 3072) : ∀ a ∈ argList bits, argumentFits a := by
  intro a ha
  simp only [argList, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  · decide
  · refine ⟨by decide, by decide, ?_⟩; unfold draw; split <;> omega_arith
  · refine ⟨by decide, by decide, ?_⟩; unfold len; omega_using [hb]
  · refine ⟨by decide, by decide, ?_⟩; unfold checks; split <;> omega_using []
  · refine ⟨by decide, by decide, by decide, ?_⟩; unfold candidate; split <;> decide
  · decide
  · decide
  · decide

/-- The arithmetic's words, from the size in `r8`, which `cmp` keeps. -/
theorem sizeWords_ok {bits : Nat} (hb : Supported bits) {s : State} (h8 : s.gpr .r8 = BitVec.ofNat 64 bits) :
    WP isa (.block sizeWords) s fun t => t.gpr .r12 = BitVec.ofNat 64 (words bits) ∧
      t.gpr .r8 = s.gpr .r8 ∧ t.mem = s.mem ∧ Keep [.rax, .r12, .r8] s t := by
  refine WP.mono (WP.keep [.rax, .r12, .r8] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (words bits) ∧
    t.gpr .r8 = s.gpr .r8 ∧ t.mem = s.mem) ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    xrun [Impl.Dsa.X86_64.ProbablePrime.sizeWords, h8, execCmov, eval]

theorem args_ok {bits : Nat} (hb : Supported bits) {s : State} {B : Addr} (hB : Scr s B 256)
    (hdi : s.gpr .rdi = B) (h8 : s.gpr .r8 = BitVec.ofNat 64 bits) :
    WP isa (.block args) s fun t =>
      t.mem = argumentWrites B (argWords s) s.mem (argList bits) ∧ Keep [.rax, .rdx, .r10, .r8] s t := by
  obtain hw : BitVec.signExtend 64 (BitVec.ofNat 32 Impl.Dsa.Generation.Layout.witness) =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness := by decide
  refine WP.mono (WP.keep [.rax, .rdx, .r10, .r8] (Q := fun t =>
      t.mem = argumentWrites B (argWords s) s.mem (argList bits)) ?_ (by decide)) fun t ⟨hm, hk⟩ => ⟨hm, hk⟩
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  · xrun [Impl.Dsa.X86_64.ProbablePrime.args, State.ea, Impl.Bignum.X86_64.hdr, hdi, h8, kOut, kLen,
      kUsedP, kChecks, kE, kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, hdrOff, Nat.reduceMul,
      Nat.reduceAdd, hw, execCmov, eval,
      hB.st (d := 128) (by decide), hB.st (d := 136) (by decide), hB.st (d := 144) (by decide),
      hB.st (d := 152) (by decide), hB.st (d := 160) (by decide), hB.st (d := 184) (by decide),
      hB.st (d := 192) (by decide), hB.st (d := 200) (by decide)]
    simp only [argumentWrites, argList, argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_zero, ite_true, ite_false, Nat.one_ne_zero, Nat.reduceEqDiff]
    rfl

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

/-! ### `Dsa.X86_64.Generation.PrimeFootprint`, which only this module used -/

section

/-! # Bound every write of the complete native primality operation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64

theorem primeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ primeRanges w, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  simp only [primeRanges, primeTrialRanges, modulusRanges, prepareRanges, r2Ranges, constantRanges,
    drawRoundRanges, sampleRoundRanges, testRanges, witnessRoundRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
    aTab, aAcc, aTmp, aY, aXm, aOne, aR2, aR1, aRm1, aE,
    kElen, kP, kT0, kT1, kT2, kUsed, kI, kUni, kStat, kU, sMinv, sCnt, sFn,
    VG.Impl.Dsa.Generation.Layout.arithmeticBytes]
  and_intros <;> omega_arith

/-- Complete setup and loading fit in the same allocation as the round. -/
theorem checkPrimeRanges_bound {w : Nat} (hw : w ≤ 48) :
    ∀ r ∈ (48, 80) :: (224, 8) :: (128, 128) :: (slot w 0, 8 * (w + 2)) :: primeRanges w,
      r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | hr
  · decide
  · decide
  · decide
  · simp only [slot, hdrBytes, VG.Impl.Dsa.Generation.Layout.arithmeticBytes]; omega_using [hw]
  · exact primeRanges_bound hw r hr

/-- Convert an offset-based workspace frame to the global memory frame used
by hashing and the outer parameter-generation controllers. -/
theorem prime_global_frame {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {m m' : Mem}
    (hf : WorkFrame B rs extra m m')
    (hb : ∀ r ∈ rs, r.1 + r.2 ≤ VG.Impl.Dsa.Generation.Layout.arithmeticBytes) :
    Frame (⟨B, VG.Impl.Dsa.Generation.Layout.arithmeticBytes⟩ :: extra) m m' := by
  intro a ha
  apply hf a (fun r hr => ha r (List.mem_cons_of_mem _ hr))
  intro r hr
  right
  obtain h := ha ⟨B, VG.Impl.Dsa.Generation.Layout.arithmeticBytes⟩ (by simp)
  change ¬ ofs B a < VG.Impl.Dsa.Generation.Layout.arithmeticBytes at h
  exact Nat.le_trans (hb r hr) (Nat.le_of_not_gt h)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The probable-prime test's body, between its frame's push and pop -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Save.lean`, which only this module imported.
section

/-! # The probable-prime test keeps the callee-saved registers in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime

def spillSlots : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

theorem spillSlots_fit : ∀ p ∈ spillSlots, p.2 + 8 ≤ 56 := by decide

theorem save_ok {s : State} (hw : (⟨s.gpr .rsp, 56⟩ : Region) ∈ s.wr) :
    WP isa (.block saveRegisters) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Saved t.mem (s.gpr .rsp) s.gpr spillSlots ∧
      Frame [⟨s.gpr .rsp, 48⟩] s.mem t.mem := by
  change WP isa (.block (saveCode .rsp spillSlots)) s _
  apply WP.mono (VG.X86_64.Spill.save_ok .rsp spillSlots s (fun p hp =>
    ⟨_, hw, Offset.contains_base _ (spillSlots_fit p hp) (by have := spillSlots_fit p hp; omega_using [this])⟩))
  intro t ⟨hg, hr, hw, hm⟩
  refine ⟨hg, hr, hw, ?_, ?_⟩
  · rw [hm]; exact saveMem_saved _ _ _ _ (by decide)
  · rw [hm]; exact saveMem_frame_base _ _ _ _ (fun p hp => by revert p; decide) (by decide)

theorem restore_ok {s : State} (g : Reg → BitVec 64)
    (hw : (⟨s.gpr .rsp, 56⟩ : Region) ∈ s.wr)
    (hs : Saved s.mem (s.gpr .rsp) g spillSlots) :
    WP isa (.block restoreRegisters) s fun t =>
      (∀ r ∈ spillSlots.map Prod.fst, t.gpr r = g r) ∧
      (∀ r, r ∉ spillSlots.map Prod.fst → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  change WP isa (.block (restoreCode .rsp spillSlots)) s _
  exact VG.X86_64.Spill.restore_ok .rsp spillSlots g s (by decide) (fun p hp =>
    ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (spillSlots_fit p hp)
      (by have := spillSlots_fit p hp; omega_using [this])⟩) hs

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Entry.lean`, which only this module imported.
section

/-! # The probable-prime test's entry: `used` in the frame, the size in `r8`, the arithmetic workspace in `rdi` -/

section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime

theorem entry_ok {s : State} (hf : Scr s (s.gpr .rsp) 56) :
    WP isa (.block entry) s fun t =>
      t.gpr .rdi = off (s.gpr .rdi) Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .rsi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rdx ∧ t.gpr .r8 = s.gpr .r9 ∧
      t.mem = s.mem.writeW (off (s.gpr .rsp) 48) (s.gpr .r8) ∧
      Keep [.rdi, .rsi, .r9, .r8] s t := by
  refine WP.mono (WP.keep [.rdi, .rsi, .r9, .r8] (Q := fun t =>
      t.gpr .rdi = off (s.gpr .rdi) Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .rsi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rdx ∧ t.gpr .r8 = s.gpr .r9 ∧
      t.mem = s.mem.writeW (off (s.gpr .rsp) 48) (s.gpr .r8)) (by
    xrun [entry, sp, State.ea, BitVec.ofInt_natCast, hf.st (d := 48) (by decide)]
    rw [show BitVec.signExtend 64 (BitVec.ofNat 32 Impl.Dsa.Generation.Layout.arithmetic) =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic by decide]) rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Workspace.lean`, which only this module imported.
section

/-! # The probable-prime test's arithmetic workspace, of the words in `r12`

As `Generation.workspace_ok`, with the words from `r12` rather than an
immediate. -/

section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem sizedWorkspace_ok {s : State} {B : Addr} {Z w : Nat}
    (h : Scr s B Z) (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hZ : slot w 16 ≤ Z)
    (hw1 : 2 ≤ w) (hw2 : w < 2 ^ 24) :
    WP isa Impl.Dsa.X86_64.ProbablePrime.sizedWorkspace s fun t =>
      Ws t B Z w ∧ Good t B Z w 0 ∧
      Frm B [(48, 80), (224, 8)] s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  obtain hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  unfold Impl.Dsa.X86_64.ProbablePrime.sizedWorkspace
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = (s.mem.writeW (off B 48) (BitVec.ofNat 64 w)).writeW (off B 56) (0#64)) (by
    xrun [State.ea, hdr, hdrOff, sW, sMinv, hdi, h12, h.st (d := 48) (by omega_using [hz]), h.st (d := 56) (by omega_using [hz])]
    rfl) rfl) fun u ⟨hm, ku⟩ => ?_)
  obtain hu := h.congr ku.2.2
  obtain hudi := (ku.gpr (by decide)).trans hdi
  obtain hu12 := (ku.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (setBases_ok hu hudi hu12 (by unfold sArr; omega_using [hz]))
    fun v ⟨harr, fv, kv⟩ => ?_)
  obtain hv := hu.congr kv.2.2
  obtain hvdi := (kv.gpr (by decide)).trans hudi
  obtain hv12 := (kv.gpr (by decide)).trans hu12
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = v.mem.writeW (off B 224) (BitVec.ofNat 64 (8 * (w + 2)))) (by
    xrun [State.ea, hdr, hdrOff, sStride, sFn, hvdi, hv12, hv.st (d := 224) (by omega_using [hz])]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      show (2 : BitVec 64).toNat = 2 from rfl]
    omega_using []) rfl) fun t ⟨htm, kt⟩ => ?_
  obtain ft : Outside B 224 8 v.mem t.mem := by rw [htm]; exact writeW_outside _ _ _ (by decide)
  obtain allk := (ku.trans kv).trans kt
  obtain hw : word t.mem B 48 = BitVec.ofNat 64 w := by
    rw [ft.word (Or.inl (by decide)) (by decide), fv.word (Or.inl (by decide)) (by decide), hm,
      (writeW_outside _ B _ (d := 56) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  obtain hminv : word t.mem B 56 = 0 := by
    rw [ft.word (Or.inl (by decide)) (by decide), fv.word (Or.inl (by decide)) (by decide), hm, word_writeW_self]
    rfl
  obtain ha : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j) := by
    intro j hj
    rw [ft.word (Or.inl (by unfold sArr; omega_using [hj])) (by unfold sArr; omega_using [hj])]
    exact harr j hj
  obtain hs := h.congr allk.2.2
  obtain ht := allk.gpr (by decide) |>.trans hdi
  refine ⟨⟨hs, ht, hw, ?_, ha, hZ, hw1, hw2⟩, ⟨hs, ht, ⟨hw, hminv, ha⟩⟩, ?_, allk.mono (by decide)⟩
  · rw [htm]; exact word_writeW_self _ _ _ _
  · have fh : Outside B 48 16 s.mem u.mem := by
      rw [hm]
      exact ((writeW_outside _ B _ (d := 48) (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ B _ (d := 56) (by decide)).mono (by decide) (by decide))
    obtain fhv : Outside B 48 80 s.mem v.mem :=
      (fh.mono (by decide) (by decide)).trans (fv.mono (by decide) (by decide))
    exact (Frm.of_outside fhv (by simp)).trans (Frm.of_outside ft (by simp))

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.Dsa.X86_64.Generation (PrimeParams PrimeArguments primeExtras primeRanges)
open VG.Impl.Bignum.X86_64 (seqs)

/-- The body of the function, inside its frame. -/
abbrev body (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq setup
    (seqs [Impl.Dsa.X86_64.Generation.primeBytes mul round, .block exit, .block restoreRegisters])

/-- The memory the test may change. -/
def changed (bits : Nat) (s : State) : List Region :=
  [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩, ⟨off (s.gpr .rdi) witness, len bits⟩,
    below (frameSp s) 128, ⟨frameSp s, 56⟩, ⟨s.gpr .r8, 8⟩]

/-- The test's result as the function returns it. -/
def BodyPost (bits : Nat) (s t : State) : Prop :=
  let res := Spec.Dsa.probablePrime (candidateOf bits s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  t.gpr .rax = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) ∧
  (∀ b rest, res = some (b, rest) →
    t.mem.readW (s.gpr .r8) 64 = BitVec.ofNat 64 ((s.gpr .rcx).toNat - rest.length)) ∧
  Frame (changed bits s) s.mem t.mem ∧
  (∀ r ∈ spillSlots.map Prod.fst, t.gpr r = s.gpr r)

/-- What the test has set up when the shared prime test starts. -/
structure Ready {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  args : PrimeArguments (params hb A) 0 0 u
  ptr : word u.mem (params hb A).B 160 = off (s.gpr .rdi) (candidate bits)
  src : Src u (params hb A).B (params hb A).Z (off (s.gpr .rdi) (candidate bits))
    (Spec.Rsa.bytesAt s.mem (off (s.gpr .rdi) (candidate bits)) (len bits))
  saved : Saved u.mem (frameSp s) s.gpr spillSlots
  used : word u.mem (frameSp s) 48 = s.gpr .r8
  frame : Frame [⟨frameSp s, 56⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = (allocState 56 s).wr

theorem prep_ok {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) :
    WP isa setup (allocState 56 s) (Ready hb A) := by
  obtain hsize : domainCheck ≤ (s.gpr .rsi).toNat * 8 := by have := A.size; omega_using [this]
  obtain hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  obtain hS0 : Scr (allocState 56 s) (s.gpr .rdi) ((s.gpr .rsi).toNat * 8) :=
    Scr.of_mem (List.mem_cons_of_mem _ hws) A.wsBound
  have hF : (allocState 56 s).gpr .rsp = frameSp s := rfl
  have hFw : (⟨frameSp s, 56⟩ : Region) ∈ (allocState 56 s).wr := List.mem_cons_self
  obtain hFn : (frameSp s).toNat + 56 ≤ 2 ^ 64 := by
    have : 184 ≤ (s.gpr .rsp).toNat := A.stackLower
    change (s.gpr .rsp - BitVec.ofNat 64 56).toNat + 56 ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this])]
    have := (s.gpr .rsp).isLt
    simp only [BitVec.toNat_ofNat]
    omega_using []
  obtain hg0 : ∀ r, r ≠ .rsp → (allocState 56 s).gpr r = s.gpr r := fun r h => by
    simp [allocState, State.setReg, h]
  -- Regions of the frame and of `ws` are disjoint.
  obtain fws : ∀ {d n e k : Nat}, d + n ≤ 56 → e + k ≤ domainCheck →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨off (s.gpr .rdi) e, k⟩ := fun h h' =>
    (A.stackWs.sub_left (frame_stack_sub s h)).sub_right (ws_sub A h')
  simp only [setup, seqs]
  -- Save the callee-saved registers.
  refine WP.seq (WP.mono (save_ok (s := allocState 56 s) (by rw [hF]; exact hFw)) ?_)
  rintro u1 ⟨g1, r1, w1, sv1, f1⟩
  -- `used` in the frame; the arithmetic workspace in `rdi`.
  obtain hF1 : Scr u1 (u1.gpr .rsp) 56 := by
    rw [g1, hF]; exact Scr.of_mem (by rw [w1]; exact hFw) hFn
  refine WP.seq (WP.mono (entry_ok hF1) ?_)
  rintro u2 ⟨di2, si2, r92, r82, m2, k2⟩
  obtain h82 : u2.gpr .r8 = BitVec.ofNat 64 bits := by rw [r82, g1, hg0 _ (by decide)]; exact A.width
  refine WP.seq (WP.mono (sizeWords_ok hb h82) ?_)
  rintro u2' ⟨h12, r82', m2', k2'⟩
  obtain hdi2' : u2'.gpr .rdi = u2.gpr .rdi := k2'.gpr (by decide)
  obtain w2 : u2.wr = (allocState 56 s).wr := k2.2.2.trans w1
  obtain hS2 : Scr u2 (params hb A).B (params hb A).Z :=
    (hS0.congr w2).sub (o := arithmetic) (n := arithmeticBytes)
      (by have : arithmetic + arithmeticBytes = domainCheck := rfl; omega_using [hsize, this]) (by decide)
  obtain hdi2 : u2.gpr .rdi = (params hb A).B := by
    rw [di2, g1, hg0 _ (by decide)]; rfl
  refine WP.seq (WP.mono (sizedWorkspace_ok (hS2.congr k2'.2.2) (hdi2'.trans hdi2) h12
    (by change _ ≤ arithmeticBytes; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change 2 ≤ words bits; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change words bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)) ?_)
  rintro u3 ⟨_, gd3, f3, k3⟩
  obtain hB3 : Scr u3 (params hb A).B 256 := by
    simpa only [off, BitVec.add_zero] using gd3.scr.sub (o := 0) (n := 256)
      (by change 0 + 256 ≤ arithmeticBytes; decide) (by decide)
  refine WP.mono (args_ok hb hB3 gd3.rdi ((k3.gpr (by decide)).trans (r82'.trans h82))) ?_
  rintro u4 ⟨m4, k4⟩
  -- Registers.
  obtain hrsi : u3.gpr .rsi = s.gpr .rdi := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), si2, g1, hg0 _ (by decide)]
  obtain hr9 : u3.gpr .r9 = s.gpr .rdx := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), r92, g1, hg0 _ (by decide)]
  obtain hrcx : u3.gpr .rcx = s.gpr .rcx := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), k2.gpr (by decide), g1, hg0 _ (by decide)]
  obtain hrsp : u4.gpr .rsp = frameSp s := by
    rw [k4.gpr (by decide), k3.gpr (by decide), k2'.gpr (by decide), k2.gpr (by decide), g1, hF]
  obtain rd4 : u4.rd = s.rd := k4.2.1.trans (k3.2.1.trans (k2'.2.1.trans (k2.2.1.trans r1)))
  obtain wr4 : u4.wr = (allocState 56 s).wr := k4.2.2.trans (k3.2.2.trans (k2'.2.2.trans w2))
  -- Memory.
  obtain ho : Outside (params hb A).B 128 128 u3.mem u4.mem := by
    rw [m4]; exact VG.Proof.Dsa.X86_64.Generation.argumentWrites_outside _ _ _ _ (argList_fits hb.le.2)
  obtain F12 : Frame [⟨off (frameSp s) 48, 8⟩] u1.mem u2.mem := by
    rw [m2, g1, hF]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  obtain F23 : Frame [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] u2.mem u3.mem :=
    VG.Proof.Dsa.X86_64.Generation.prime_global_frame (extra := []) (m2' ▸ f3.work) (by decide)
  obtain F34 : Frame [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] u3.mem u4.mem :=
    VG.Proof.Dsa.X86_64.Generation.prime_global_frame (extra := [])
      (Frm.of_outside (rs := [(128, 128)]) ho List.mem_cons_self).work (by decide)
  obtain F14 : Frame [⟨off (frameSp s) 48, 8⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] u1.mem u4.mem :=
    (F12.mono (by simp)).trans ((F23.mono (by simp)).trans (F34.mono (by simp)))
  obtain F04 : Frame [⟨frameSp s, 56⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] s.mem u4.mem := by
    obtain F01 : Frame [⟨frameSp s, 56⟩] s.mem u1.mem :=
      Frame.sub f1 fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
    refine (F01.mono (by simp)).trans (Frame.sub F14 fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have wh (k : Nat) (hk32 : k < 32) : word u4.mem (params hb A).B (8 * k) =
      VG.Proof.Dsa.X86_64.Generation.argumentWords (argWords u3)
        (fun j => word u3.mem (params hb A).B (8 * j)) (argList bits) k := by
    rw [m4]; exact VG.Proof.Dsa.X86_64.Generation.argumentWrites_word _ _ _ _ (argList_fits hb.le.2) hk32
  obtain hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hcand : candidate bits + len bits ≤ witness := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  -- The candidate's and the tape's bytes are outside the frame and the workspace.
  obtain candOut : ∀ i < len bits, ∀ r ∈ [(⟨frameSp s, 56⟩ : Region),
      ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩],
      ¬ r.Contains (off (s.gpr .rdi) (candidate bits) + BitVec.ofNat 64 i) 1 := by
    intro i hi r hr hc
    obtain hb' := contains_byte (off (s.gpr .rdi) (candidate bits)) hi (by omega_using [hlen])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := fws (d := 0) (n := 56) (e := candidate bits) (k := len bits) (by decide)
        (by have : witness ≤ domainCheck := (by decide); omega_using [hcand, this])
      simp only [off, BitVec.add_zero] at this
      exact this _ hc hb'
    · exact Offset.disjoint (s.gpr .rdi) (d := candidate bits) (n := len bits) (e := arithmetic)
        (k := arithmeticBytes) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega_using [hcand, this]))
        (by have : witness < 2 ^ 64 := (by decide); omega_using [hcand, this]) (by decide) _ hb' hc
  obtain randOut : ∀ i < (s.gpr .rcx).toNat, ∀ r ∈ [(⟨frameSp s, 56⟩ : Region),
      ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩],
      ¬ r.Contains (s.gpr .rdx + BitVec.ofNat 64 i) 1 := by
    intro i hi r hr hc
    obtain hb' := contains_byte (s.gpr .rdx) hi (by have := A.randBound; omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
      simp only [off, BitVec.add_zero] at hs
      exact A.stackRand _ (hs _ hc) hb'
    · exact A.wsRand _ (ws_sub A (by decide) _ hc) hb'
  refine ⟨⟨⟨gd3.scr.congr k4.2.2, (k4.gpr (by decide)).trans gd3.rdi,
      gd3.hdr.of_frm (Frm.of_outside (rs := [(128, 128)]) ho List.mem_cons_self) (by simp)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, F04, rd4, wr4⟩
  · rw [wh kOut (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hrsi]
    rfl
  · rw [wh kUsedP (by decide)]; rfl
  · rw [wh kLen (by decide)]; rfl
  · rw [wh kRand (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false,
      hr9, BitVec.add_zero, Nat.one_ne_zero]
    rfl
  · rw [wh kRandLen (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false,
      hrcx, BitVec.add_zero]
    change s.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · rw [wh kUsed (by decide)]; rfl
  · rw [wh kChecks (by decide)]; rfl
  · change Src u4 (off (s.gpr .rdi) arithmetic) arithmeticBytes (s.gpr .rdx)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_left _ (by rw [rd4, A.rd]; exact List.mem_cons_self), ?_⟩
      exact contains_byte _ hi (by have := A.randBound; omega_using [])
    · have hi' : i < (s.gpr .rcx).toNat := by rw [bytesAt_length] at hi; exact hi
      rw [F04 _ (randOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < (s.gpr .rcx).toNat := by rw [bytesAt_length] at hi; exact hi
      exact out_scr ((A.wsRand.symm).sub_right (ws_sub A (by decide)))
        (contains_byte _ hi' (by have := A.randBound; omega_using []))
  · change ∀ i < len bits, InRegions u4.wr (off (off (s.gpr .rdi) witness) i) 1
    intro i hi
    refine ⟨_, by rw [wr4]; exact List.mem_cons_of_mem _ hws, ?_⟩
    change (wsRegion s).Contains (off (off (s.gpr .rdi) witness) i) 1
    rw [show off (off (s.gpr .rdi) witness) i = off (s.gpr .rdi) (witness + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact Offset.contains_base _ (by have : witness + 384 ≤ domainCheck := (by decide); omega_using [hsize, hlen, hi, this])
      (by have : witness + 384 < 2 ^ 64 := (by decide); omega_using [hlen, hi, this])
  · exact hrsp
  · rw [wh 20 (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hrsi]
  · change Src u4 (off (s.gpr .rdi) arithmetic) arithmeticBytes (off (s.gpr .rdi) (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .rdi) (candidate bits)) (len bits))
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_right _ (by rw [wr4]; exact List.mem_cons_of_mem _ hws), ?_⟩
      rw [show off (s.gpr .rdi) (candidate bits) + BitVec.ofNat 64 i = off (s.gpr .rdi) (candidate bits + i) by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
      exact Offset.contains_base _ (by have : witness ≤ domainCheck := (by decide); omega_using [hsize, hcand, hi, this])
        (by have : witness < 2 ^ 64 := (by decide); omega_using [hcand, hi, this])
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      rw [F04 _ (candOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      refine out_scr (r := ⟨off (s.gpr .rdi) (candidate bits), len bits⟩) ?_
        (contains_byte _ hi' (by omega_using [hlen]))
      exact Offset.disjoint (s.gpr .rdi) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega_using [hcand, this]))
        (by have : witness < 2 ^ 64 := (by decide); omega_using [hcand, this]) (by decide)
  · intro p hp
    obtain hne : p.1 ≠ .rsp := by revert p; decide
    obtain hp48 : ∀ q ∈ spillSlots, q.2 + 8 ≤ 48 := by decide
    rw [← hg0 _ hne, ← sv1 p hp, hF]
    exact F14.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (Or.inl (hp48 p hp)) (by have := hp48 p hp; omega_using [this]) (by decide)
      · exact fws (by have := hp48 p hp; omega_using [this]) (by decide)) (by decide)
  · have h2 : word u2.mem (frameSp s) 48 = s.gpr .r8 := by
      rw [m2, g1, hF, hg0 _ (by decide)]; exact word_writeW_self _ _ _ _
    rw [← h2]
    exact (F23.trans F34).readW (Region.contains_self _ _)
      (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact fws (by decide) (by decide)) (by decide)

/-- What the test leaves. -/
structure Tested {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  input : ∃ mi' used', VG.Proof.Dsa.X86_64.Generation.PrimeInput (params hb A) mi' used' u ∧
    used' ≤ (params hb A).rand.length ∧
    (Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = none →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = some (b, rest) →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      used' = (params hb A).rand.length - rest.length)
  saved : Saved u.mem (frameSp s) s.gpr spillSlots
  used : word u.mem (frameSp s) 48 = s.gpr .r8
  frame : Frame [⟨frameSp s, 56⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩,
    ⟨off (s.gpr .rdi) witness, len bits⟩, below (frameSp s) 128] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = (allocState 56 s).wr

theorem test_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) {u4 : State} (R : Ready hb A u4) :
    WP isa (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run) u4 (Tested hb A) := by
  obtain fws : ∀ {d n e k : Nat}, d + n ≤ 56 → e + k ≤ domainCheck →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨off (s.gpr .rdi) e, k⟩ := fun h h' =>
    (A.stackWs.sub_left (frame_stack_sub s h)).sub_right (ws_sub A h')
  obtain fused : ∀ {d n : Nat}, d + n ≤ 56 →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨s.gpr .r8, 8⟩ := fun h =>
    A.stackUsed.sub_left (frame_stack_sub s h)
  obtain hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hw : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  -- The test.
  obtain hlow := ((bitLength_iff_bounds (by have := hb.le; omega_using [this])).mp A.bits).1
  refine WP.mono (VG.Proof.Dsa.X86_64.Generation.primeBytes_ok M K R.args R.ptr
    (bytesAt_length _ _ _) rfl R.src (Nat.zero_le _) hw
    (by change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change 8161 < candidateOf bits s
      obtain h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega_using [this])
      have : (8161 : Nat) < 2 ^ 159 := by decide
      exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow))
    (by
      change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
      rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
      rw [A.bits]; rfl)) ?_
  rintro u5 ⟨mi', used', inp, hub, hnone, hsome, wf5, k5⟩
  obtain F45 : Frame [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩, ⟨off (s.gpr .rdi) witness, len bits⟩,
      below (frameSp s) 128] u4.mem u5.mem :=
    VG.Proof.Dsa.X86_64.Generation.prime_global_frame wf5 (fun r hr =>
      VG.Proof.Dsa.X86_64.Generation.checkPrimeRanges_bound hw r
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
  obtain frameOut : ∀ {d n : Nat}, d + n ≤ 56 → ∀ r ∈ [(⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩ : Region),
      ⟨off (s.gpr .rdi) witness, len bits⟩, below (frameSp s) 128],
      Region.Disjoint ⟨off (frameSp s) d, n⟩ r := by
    intro d n h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fws h (by decide)
    · exact fws h (by have : witness + 384 ≤ domainCheck := (by decide); omega_using [hlen, this])
    · exact Offset.disjoint_below _ (by omega_using [h])
  obtain hp48 : ∀ q ∈ spillSlots, q.2 + 8 ≤ 48 := by decide
  refine ⟨⟨mi', used', inp, hub, hnone, hsome⟩,
    R.saved.frame F45 fun p hp r hr => frameOut (by have := hp48 p hp; omega_using [this]) r hr,
    by rw [← R.used]; exact F45.readW (Region.contains_self _ _) (frameOut (by decide)) (by decide),
    ?_, k5.2.1.trans R.rd, k5.2.2.trans R.wr⟩
  refine (Frame.sub R.frame ?_).trans (Frame.sub F45 ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · intro r hr
    exact ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem finish_ok {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) {u5 : State} (T : Tested hb A u5) :
    WP isa (.seq (.block exit) (.block restoreRegisters)) u5 fun t =>
      t.gpr .rsp = (allocState 56 s).gpr .rsp ∧ t.wr = (allocState 56 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t := by
  obtain fws : ∀ {d n e k : Nat}, d + n ≤ 56 → e + k ≤ domainCheck →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨off (s.gpr .rdi) e, k⟩ := fun h h' =>
    (A.stackWs.sub_left (frame_stack_sub s h)).sub_right (ws_sub A h')
  obtain fused : ∀ {d n : Nat}, d + n ≤ 56 →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨s.gpr .r8, 8⟩ := fun h =>
    A.stackUsed.sub_left (frame_stack_sub s h)
  obtain hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hw : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain frameOut : ∀ {d n : Nat}, d + n ≤ 56 → ∀ r ∈ [(⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩ : Region),
      ⟨off (s.gpr .rdi) witness, len bits⟩, below (frameSp s) 128],
      Region.Disjoint ⟨off (frameSp s) d, n⟩ r := by
    intro d n h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fws h (by decide)
    · exact fws h (by have : witness + 384 ≤ domainCheck := (by decide); omega_using [hlen, this])
    · exact Offset.disjoint_below _ (by omega_using [h])
  obtain ⟨⟨mi', used', inp, hub, hnone, hsome⟩, sv5, hu5, F05, rd5, wr5⟩ := T
  have hsp5 : u5.gpr .rsp = frameSp s := inp.stack
  -- The exit.
  obtain hU : (⟨s.gpr .r8, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  refine WP.seq (WP.mono (exit_ok (U := s.gpr .r8) inp.good.rdi
    (inp.good.scr.ld (d := 200) (by change _ ≤ arithmeticBytes; decide))
    (inp.good.scr.ld (d := 232) (by change _ ≤ arithmeticBytes; decide))
    ⟨_, List.mem_append_right _ (by rw [wr5]; exact List.mem_cons_self),
      by rw [hsp5]; exact Offset.contains_base _ (by decide) (by decide)⟩
    (by rw [hsp5]; exact hu5)
    ⟨⟨s.gpr .r8, 8⟩, by rw [wr5]; exact List.mem_cons_of_mem _ hU, Region.contains_self _ _⟩
    (by
      obtain h := (A.wsUsed.sub_left (ws_sub A (d := arithmetic + 232) (n := 8) (by decide)))
      rw [show off (s.gpr .rdi) (arithmetic + 232) = off (params hb A).B 232 by
        simp only [params, off, BitVec.add_assoc, BitVec.ofNat_add]] at h
      exact fun x h₁ h₂ => h x h₁ h₂)) ?_)
  rintro u6 ⟨rax6, m6, k6⟩
  obtain F56 : Frame [⟨s.gpr .r8, 8⟩] u5.mem u6.mem := by
    rw [m6]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  obtain hsp6 : u6.gpr .rsp = frameSp s := (k6.gpr (by decide)).trans hsp5
  obtain wr6 : u6.wr = (allocState 56 s).wr := k6.2.2.trans wr5
  obtain hp48 : ∀ q ∈ spillSlots, q.2 + 8 ≤ 48 := by decide
  obtain sv6 : Saved u6.mem (u6.gpr .rsp) s.gpr spillSlots := by
    rw [hsp6]
    refine sv5.frame F56 ?_
    intro p hp r hr
    obtain rfl := List.mem_singleton.mp hr
    exact fused (by have := hp48 p hp; omega_using [this])
  -- Restore the callee-saved registers.
  refine WP.mono (restore_ok s.gpr (by rw [hsp6, wr6]; exact List.mem_cons_self) sv6) ?_
  rintro u7 ⟨g7, k7, m7, rd7, wr7⟩
  refine ⟨by rw [k7 _ (by decide), hsp6]; rfl, wr7.trans wr6, rd7.trans (k6.2.1.trans rd5),
    ?_, ?_, ?_, g7⟩
  · rw [k7 _ (by decide), rax6]
    change returned (word u5.mem (params hb A).B (8 * kStat)) = BitVec.ofNat 64
      (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand)))
    cases h : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) with
    | none => rw [hnone h]; decide
    | some r =>
      obtain ⟨b, rest⟩ := r
      rw [(hsome b rest h).1]
      cases b <;> simp only [Proof.Dsa.ProbablePrime.status] <;> decide
  · intro b rest h
    have h' : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) = some (b, rest) := h
    rw [m7, m6, Mem.readW_writeW_self64]
    change word u5.mem (params hb A).B (8 * kUsed) = _
    rw [inp.used, (hsome b rest h').2]
    change BitVec.ofNat 64 ((Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length - rest.length) = _
    rw [bytesAt_length]
  · rw [m7]
    refine (Frame.sub F05 ?_).trans (Frame.sub F56 ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp [changed], fun _ h => h⟩
      · exact ⟨_, by simp [changed], fun _ h => h⟩
      · exact ⟨_, by simp [changed], fun _ h => h⟩
      · exact ⟨_, by simp [changed], fun _ h => h⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [changed], fun _ h => h⟩


theorem body_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) :
    WP isa (body M.mm K.run) (allocState 56 s) fun t =>
      t.gpr .rsp = (allocState 56 s).gpr .rsp ∧ t.wr = (allocState 56 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t :=
  WP.seq (WP.mono (prep_ok hb A) fun _ R =>
    WP.seq (WP.mono (test_ok M K hb A R) fun _ T => finish_ok hb A T))

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

/-! ### `Dsa.X86_64.Generation.PrimeBytesCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.ProbablePrimeCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.PrimeSetupCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.PrimeConstantsCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.NegateR1CT`, which only this module used -/

section

/-! # Public-width subtraction for the Montgomery encoding of minus one -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def NegateR1Regs (p : PrimeParams) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r8 = off p.B (slot p.w aN) ∧
    s.gpr .r10 = off p.B (slot p.w aR1) ∧ s.gpr .rsi = off p.B (slot p.w aRm1)

theorem negateR1Args_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] : List Instr) ++
      extBase aR1 .r10 ++ extBase aRm1 .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))) s (NegateR1Regs p) := by
  obtain ⟨mi, hg⟩ := h
  have hw : p.w < 2 ^ 31 := by have := p.dims.w128; omega_using [this]
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .r8] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
    t.gpr .r8 = off p.B (slot p.w aN) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hdrOff, hg.rdi, hl sW (by decide), hl (sArr aN) (by decide),
        hg.hdr.hw, hg.hdr.harr aN (by decide)]) rfl) fun u ⟨⟨h12, h8, hm⟩, ku⟩ => ?_
  have hu : Good u p.B p.Z p.w mi :=
    ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hu p.dims.z hw (j := aR1) (by decide)
    (r := .r10) (by decide) rfl rfl) fun v ⟨h10, hmv, kv⟩ => ?_
  have hv : Good v p.B p.Z p.w mi :=
    ⟨hu.scr.congr kv.2.2, (kv.gpr (by decide)).trans hu.rdi, by rw [hmv]; exact hu.hdr⟩
  refine WP.mono (extBase_ok hv p.dims.z hw (j := aRm1) (by decide)
    (r := .rsi) (by decide) rfl rfl) fun z ⟨hsi, _, kz⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun _ => True) (by xrun; exact ⟨_, rfl⟩) rfl) fun t ⟨_, kt⟩ => ?_
  exact ⟨(((kv.trans kz).trans kt).gpr (by decide)).trans h12,
    (((kv.trans kz).trans kt).gpr (by decide)).trans h8,
    ((kz.trans kt).gpr (by decide)).trans h10, (kt.gpr (by decide)).trans hsi⟩

theorem negateR1_ct : RelCT isa (Two PrimeGood)
    Impl.Ffdh.X86_64.ParameterCandidate.negateR1 (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.negateR1
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => negateR1Args_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .r8, .r10, .rsi] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PrimeR2CT`, which this module and modules that import it used -/

section

/-! # Constant-time Montgomery initialization for full and padded DSA candidates -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def PrimeSetupBefore (p : PrimeParams) (s : State) : Prop :=
  (∃ mi, Good s p.B p.Z p.w mi) ∧ wv s.mem p.B (slot p.w aN) p.w = p.N ∧ p.w ≤ 48

def PrimeParams.product (p : PrimeParams) (mi : BitVec 64) : ProductPublic :=
  ⟨⟨p.B, p.Z, p.w, mi⟩, p.N, p.dims.z, by change 2 ≤ p.w; have := p.dims.w4; omega_using [this],
    by change p.w < 2 ^ 31; have := p.dims.w128; omega_using [this]⟩

def PrimeInverse (p : PrimeParams) (s : State) : Prop := ∃ mi, SetupPre (p.product mi) s

theorem primeHeadArgs_state {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block [.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))]) s
      (fun t => t.gpr .rdi = p.B ∧ t.gpr .r10 = off p.B (slot p.w aN)) := by
  obtain ⟨mi, hg⟩ := h.1
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega_arith)
  xrun [State.ea, hdr, hdrOff, hg.rdi, hl (sArr aN) (by decide), hl sW (by decide), hg.hdr.harr aN (by decide)]

theorem primeHead_ct : RelCT isa (Two PrimeSetupBefore)
    (.block Impl.Ffdh.X86_64.ParameterCandidate.prepareHead) (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.prepareHead
  change RelCT isa (Two PrimeSetupBefore) (.block
    (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))] : List Instr) ++
      ([.mov .rbx (.mem (at0 .r10))] ++ Impl.Bignum.X86_64.minv ++
        [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]))) _
  apply RelCT.block_append (M := isa)
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => primeHeadArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1
    obtain ⟨mi', ht⟩ := ht.1
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.rdi, .r10] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)

theorem primeHead_inverse {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block Impl.Ffdh.X86_64.ParameterCandidate.prepareHead) s (PrimeInverse p) := by
  obtain ⟨mi, hg⟩ := h.1
  have hw := p.dims.w4
  have hnow := hg.scr.nowrap
  have hfit := p.dims.z
  have hodd : (word s.mem p.B (slot p.w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega_using [hw]), h.2.1,
      Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact p.odd
  refine WP.mono (msHead_ok hg p.dims.z hodd) fun t ⟨ht, hi, _, _, _, hm, _⟩ => ?_
  have hn : wv t.mem p.B (slot p.w aN) p.w = p.N := by
    rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_using [hnow, hfit])]
    exact h.2.1
  have hinv : ((word t.mem p.B (slot p.w aN)).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm, hdrStore_word _ _ _ (by decide) (by decide) (by omega_using [hnow, hfit])]
    exact hi
  exact ⟨t.gpr .r15, ⟨ht, hn, hinv⟩, h.2.2, by change 1 < p.N; have := p.n3; omega_using [this], p.odd⟩

theorem primeInverse_public {s t : State} (h : Two PrimeInverse s t) : Two SetupPre s t := by
  obtain ⟨p, ⟨mi, hs⟩, ⟨mi', ht⟩⟩ := h
  have hw := p.dims.w4
  have low₁ : (word s.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega_using [hw]), show wv s.mem p.B (slot p.w aN) p.w = p.N from hs.1.modulus]
  have low₂ : (word t.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by omega_using [hw]), show wv t.mem p.B (slot p.w aN) p.w = p.N from ht.1.modulus]
  have hi := hs.1.inverse
  have hi' := ht.1.inverse
  change ((word s.mem p.B (slot p.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 at hi
  change ((word t.mem p.B (slot p.w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 at hi'
  rw [low₁] at hi
  rw [low₂] at hi'
  have he := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.odd) hi hi'
  subst mi'
  exact ⟨p.product mi, hs, ht⟩

theorem primeR2_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.X86_64.Generation.primeR2 M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeR2
  exact RelCT.seq (two_post primeHead_ct (fun _ _ h => primeHead_inverse h))
    ((constants_ct M).mono (fun _ _ h => primeInverse_public h) (fun _ _ h => h))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Constant-time derivation of the prepared Montgomery constants -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

def PrimeR2Ready (p : PrimeParams) (s : State) : Prop :=
  ∃ mi, ModCtx s p.B p.Z p.w mi p.N ∧ wv s.mem p.B (slot p.w aOne) p.w = 1 ∧
    wv s.mem p.B (slot p.w aR2) p.w = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N

theorem primeR2_ready (M : Mont) {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeR2 M.mm) s (PrimeR2Ready p) := by
  obtain ⟨mi, hg⟩ := h.1
  exact WP.mono (primeR2_ok M hg p.dims.z (by have := p.dims.w4; omega_using [this]) h.2.2 h.2.1 p.odd
    (by have := p.n3; omega_using [this])) fun _ ⟨mi', ht, hi, hn, hone, hr2, _⟩ =>
      ⟨mi', ⟨ht, hn, hi⟩, hone, hr2⟩

theorem primeMontOne_good (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (M.mm aY aR2 aOne) s (PrimeGood p) := by
  obtain ⟨mi, h, hone, _⟩ := h
  exact WP.mono (M.mm_ok h.good p.dims.z (by have := p.dims.w4; omega_using [this])
    (by have := p.dims.w128; omega_using [this]) (o := aY) (a := aR2) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.inverse (by rw [hone, h.modulus]; have := p.n3; omega_using [this])) fun _ ht => ⟨mi, ht.1⟩

theorem primeConstants_ct (M : Mont) : RelCT isa (Two PrimeR2Ready)
    (Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants M.mm) (fun _ _ => True) := by
  unfold Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants
  refine RelCT.seq (two_post
    (two_map (fun p : PrimeParams => (⟨p.B, p.Z, p.w⟩ : Ws)) (fun p s h => by
      obtain ⟨mi, h, _⟩ := h; exact ⟨mi, h.good, p.dims.z⟩)
      (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide)))
    (fun _ _ h => primeMontOne_good M h)) ?_
  exact RelCT.seq (two_post copyR1_ct (fun _ _ h => copyR1_good h)) negateR1_ct

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.ExponentCT`, which only this module used -/

section

/-! # Constant-time preparation of the windowed Miller–Rabin exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def ExponentBefore (p : PrimeParams) (s : State) : Prop :=
  PrimeGood p s ∧ wv s.mem p.B (slot p.w aN) p.w = p.N

theorem lowWordArgs_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))]) s
      (fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .r8 = off p.B (slot p.w aN)) := by
  obtain ⟨mi, hg⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega_arith)
  xrun [State.ea, hdr, hdrOff, hg.rdi, hl sW (by decide), hl (sArr aN) (by decide),
    hg.hdr.hw, hg.hdr.harr aN (by decide)]

theorem lowWord_ct : RelCT isa (Two PrimeGood) (seqs lowWord) (fun _ _ => True) := by
  unfold lowWord
  simp only [seqs]
  apply VG.Proof.Rsa.X86_64.RelCT.block_seq (l₁ :=
    [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))])
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => lowWordArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .r8] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)

theorem lowWord_good {p : PrimeParams} {s : State} (h : ExponentBefore p s) :
    WP isa (seqs lowWord) s (PrimeGood p) := by
  obtain ⟨mi, hg⟩ := h.1
  refine WP.mono (lowWord_ok hg p.dims.z (by have := p.dims.w4; omega_using [this])
    (by have := p.dims.w128; omega_using [this]) h.2 p.odd (by have := p.n3; omega_using [this])) fun t ⟨_, hm, hk⟩ => ?_
  exact ⟨mi, hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩

def ExponentRegs (p : PrimeParams) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rsi = off p.B (slot p.w aN) ∧
    s.gpr .rbx = off p.B (slot p.w aE)

theorem exponentArgs_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block (extBase aE .rbx ++
      ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN)))] : List Instr))) s (ExponentRegs p) := by
  obtain ⟨mi, hg⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg p.dims.z (by have := p.dims.w128; omega_using [this])
    (j := aE) (by decide) (r := .rbx) (by decide) rfl rfl) fun u ⟨hbx, hm, hk⟩ => ?_
  have hu : Good u p.B p.Z p.w mi :=
    ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  have hl : ∀ i < 32, InRegions (u.rd ++ u.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hu.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega_arith)
  xrun [ExponentRegs, State.ea, hdr, hdrOff, hu.rdi, hl sW (by decide), hl (sArr aN) (by decide),
    hu.hdr.hw, hu.hdr.harr aN (by decide), hbx]

theorem exponentTail_ct : RelCT isa (Two PrimeGood)
    (seqs (([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)),
      .mov .rsi (.mem (hdr (sArr aN))), .mov .r15 (.imm (BitVec.ofInt 32 (-1))),
      .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp), .alu .and .rax (.reg .rbp),
      .store (ix .rbx .r12) .rax] : List Instr))] : List (Prog isa)) ++
      (halfPass ++ (halfCond 1 ++ (halfCond 2 ++ halfCond 3))))) (fun _ _ => True) := by
  simp only [halfPass, halfCond, List.cons_append, List.nil_append, seqs]
  rw [show extBase aE .rbx ++
      ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
        .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0),
        .alu .sub .rax (.reg .rbp), .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr) =
      (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN)))] : List Instr)) ++
        ([.mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
          .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr) by
      simp only [List.append_assoc, List.cons_append, List.nil_append]]
  apply VG.Proof.Rsa.X86_64.RelCT.block_seq
    (l₁ := extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN)))] : List Instr))
    (l₂ := [.mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
      .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax])
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => exponentArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .rsi, .rbx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

theorem primeExponent_ct : RelCT isa (Two ExponentBefore) (seqs expSetup) (fun _ _ => True) := by
  rw [expSetup_eq]
  apply RelCT.seqs_append (by simp [lowWord]) (by simp)
  exact RelCT.seq (two_post (two_map id (fun _ _ h => h.1) lowWord_ct)
    (fun _ _ h => lowWord_good h)) exponentTail_ct

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Constant-time preparation of every shared primality-round input -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem primeConstants_exponent (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants M.mm) s (ExponentBefore p) := by
  obtain ⟨mi, h, hone, hr2⟩ := h
  have hnw := h.good.scr.nowrap
  have hNfit := Nat.le_trans (slot_le (w := p.w) (show aN < 8 by decide)) p.dims.z
  refine WP.mono (prepareConstants_ok M h.good p.dims.z p.dims.x
    (by have := p.dims.w4; omega_using [this]) (by have := p.dims.w128; omega_using [this]) h.modulus h.inverse
    hone p.odd (by have := p.n3; omega_using [this]) hr2) fun t ⟨ht, _, _, hf, _⟩ => ?_
  refine ⟨⟨mi, ht⟩, ?_⟩
  rw [hf.wv_eq (by simp only [constantRanges]; rng_disj) (by omega_using [hnw, hNfit])]
  exact h.modulus

theorem primeSetup_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.X86_64.Generation.primeSetup M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeSetup
  exact RelCT.seq (two_post (primeR2_ct M) (fun _ _ h => primeR2_ready M h))
    (RelCT.seq (two_post (primeConstants_ct M) (fun _ _ h => primeConstants_exponent M h)) primeExponent_ct)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.TrialCT`, which this module and modules that import it used -/

section

/-! # Trial division reads public workspace metadata in the generation arena -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen.X86_64

structure PrimeCallPublic where
  draw : DrawPublic
  arena : Addr
  wr : List Region
  /-- The arena is the generation's last writable region, or the second of
  a called test's (`vg_dsa_probable_prime_*`). -/
  layout : PrimeHeaderLayout arena wr ∨ CalleeHeaderLayout arena wr
  base : draw.prime.B = off arena 28672
  width : draw.prime.w ≤ 48
  tab : slot draw.prime.w aTab + 2048 ≤ draw.prime.Z
  large : 8161 < draw.prime.N
  policy : 1024 < Spec.Dsa.bitLength draw.prime.N ↔ 16 < draw.prime.w

def PrimeCallBefore (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  (∃ mi, PrimeInput p.draw.prime mi p.draw.used s) ∧ s.wr = p.wr ∧
    p.draw.used ≤ p.draw.prime.rand.length ∧ p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

theorem primeTrial_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeCallBefore len drawBytes))
    (seqs trial) (fun _ _ => True) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, h₁, h₂⟩ e₁ e₂
  rcases p.layout with hl | hl
  · refine primeHeader_ct (Φ := fun p s => PrimeCallBefore len drawBytes p s ∧ PrimeHeaderLayout p.arena p.wr)
      PrimeCallPublic.arena PrimeCallPublic.wr gS
      (fun p => gvs p.draw.prime.B p.draw.prime.w) [] (by decide) (fun _ => gvs_fst _ _) ?_
      (pins_nil _) (by taint_decide) (by taint_decide) _ _ _ _ _ _ ⟨p, ⟨h₁, hl⟩, h₂, hl⟩ e₁ e₂
    intro p s h
    obtain ⟨mi, hs⟩ := h.1.1
    exact ⟨h.2, by rw [← p.base]; exact good_hp hs.good h.1.2.1⟩
  · refine calleeHeader_ct (Φ := fun p s => PrimeCallBefore len drawBytes p s ∧ CalleeHeaderLayout p.arena p.wr)
      PrimeCallPublic.arena PrimeCallPublic.wr gS
      (fun p => gvs p.draw.prime.B p.draw.prime.w) [] (by decide) (fun _ => gvs_fst _ _) ?_
      (pins_nil _) (by taint_decide) _ _ _ _ _ _ ⟨p, ⟨h₁, hl⟩, h₂, hl⟩ e₁ e₂
    intro p s h
    obtain ⟨mi, hs⟩ := h.1.1
    exact ⟨h.2, by rw [← p.base]; exact good_hp hs.good h.1.2.1⟩

def PrimeCallTested (len drawBytes : Nat) (p : PrimeCallPublic) (s : State) : Prop :=
  PrimeCallBefore len drawBytes p s ∧
    s.zf = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength p.draw.prime.N) p.draw.prime.N)

theorem primeTrial_tested {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) :
    WP isa (seqs trial) s (PrimeCallTested len drawBytes p) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (primeTrial_ok hs p.width p.tab p.large p.policy) fun _ ⟨hz, ht, _, hk⟩ =>
    ⟨⟨⟨mi, ht⟩, hk.2.2.trans h.2.1, h.2.2⟩, hz⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PrimeLoopCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.PrimeLoopCTData`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.PrimeIterationCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.DrawRoundCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.SampleRoundCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.RoundTailCT`, which only this module used -/

section

/-! # The primality completion policy branches only on the public round result -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Bignum.X86_64

structure RoundTailPublic where
  B : Addr
  Z : Nat
  w : Nat
  pass : Bool

def RoundTailState (p : RoundTailPublic) (s : State) : Prop :=
  (∃ mi, Good s p.B p.Z p.w mi) ∧ slot p.w 8 ≤ p.Z ∧ word s.mem p.B (8 * kFlag) = mask p.pass

def RoundTailTested (p : RoundTailPublic) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ s.zf = some (!p.pass)

theorem roundTail_ct : RelCT isa (Two RoundTailState)
    Impl.Dsa.X86_64.Generation.roundTail (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.roundTail
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := RoundTailTested) (two_taint [.rdi] ?_ (by taint_decide)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1
    obtain ⟨mi', ht⟩ := ht.1
    exact hs.rdi.trans ht.rdi.symm
  · intro p s h
    obtain ⟨mi, hg⟩ := h.1
    exact WP.mono (flagTest_ok hg h.2.1 h.2.2) fun t ⟨hz, _, hk⟩ =>
      ⟨(hk.gpr (by decide)).trans hg.rdi, hz⟩
  · refine two_ite_seq (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    all_goals
      exact two_taint [.rdi] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact hs.1.1.trans ht.1.1.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.SampleCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.StoredWitnessCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.TestWitnessCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.PaddedLoadCT`, which this module and modules that import it used -/

section

/-! # Padded primality loads leak only their public workspace and source dimensions -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

structure PaddedPublic where
  B : Addr
  Z : Nat
  w : Nat
  source : Addr
  length : Nat

def PaddedPublic.workspace (p : PaddedPublic) : VG.Proof.Bignum.X86_64.Ws := ⟨p.B, p.Z, p.w⟩

structure PaddedState (ptr len : Nat) (p : PaddedPublic) (s : State) : Prop where
  good : ∃ mi, Good s p.B p.Z p.w mi
  room : slot p.w 8 ≤ p.Z
  positive : 1 ≤ p.w
  bound : p.w < 2 ^ 31
  pointer : word s.mem p.B (8 * ptr) = p.source
  length : word s.mem p.B (8 * len) = BitVec.ofNat 64 p.length

theorem paddedZero_state {a ptr len : Nat} (ha : a < 8) (hp : ptr < 32) (hl : len < 32)
    {p : PaddedPublic} {s : State} (h : PaddedState ptr len p s) :
    WP isa (Impl.Rsa.X86_64.Crt.zeroArr a) s (PaddedState ptr len p) := by
  obtain ⟨mi, hg⟩ := h.good
  have hn := hg.scr.nowrap
  have hhdr : 256 ≤ slot p.w a := by simp only [slot, hdrBytes]; omega_using []
  refine WP.mono (zeroArr_ok hg h.room h.positive h.bound ha) fun t ⟨_, ho, hk⟩ => ?_
  have ht : Good t p.B p.Z p.w mi :=
    ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, hg.hdr.outside ho hhdr⟩
  have header (i : Nat) (hi : i < 32) : word t.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    ho.word (Or.inl (by omega_using [hhdr, hi])) (by omega_using [hi])
  exact ⟨⟨mi, ht⟩, h.room, h.positive, h.bound,
    (header ptr hp).trans h.pointer, (header len hl).trans h.length⟩

def PaddedRegs (a : Nat) (p : PaddedPublic) (s : State) : Prop :=
  s.gpr .rsi = p.source ∧ s.gpr .rcx = BitVec.ofNat 64 p.length ∧
    s.gpr .rbx = off p.B (slot p.w a)

theorem paddedArgs_state {a ptr len : Nat} (ha : a < 8) (hp : ptr < 32) (hl : len < 32)
    {p : PaddedPublic} {s : State} (h : PaddedState ptr len p s) :
    WP isa (.block [.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len)),
      .mov .rbx (.mem (hdr (sArr a)))]) s (PaddedRegs a p) := by
  obtain ⟨mi, hg⟩ := h.good
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega_using [h.room, this])
  xrun [PaddedRegs, State.ea, hdr, hg.rdi, hdrOff, hld ptr hp, hld len hl,
    hld (sArr a) (by unfold sArr; omega_using [ha]), h.pointer, h.length, hg.hdr.harr a ha]

theorem loadPadded_ct {a ptr len : Nat} (ha : a < 8) (hp : ptr < 32) (hl : len < 32)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .r8 (.mem (hdr (sArr a))), .mov .r12 (.mem (hdr sW))]) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .rsi (.mem (hdr ptr)), .mov .rcx (.mem (hdr len)),
        .mov .rbx (.mem (hdr (sArr a)))]) hc₂).isSome = true) :
    RelCT isa (Two (PaddedState ptr len)) (Impl.Dsa.X86_64.Generation.loadPadded a ptr len)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.loadPadded
  simp only [seqs]
  refine RelCT.seq (two_post
    (two_map PaddedPublic.workspace (fun _ _ h => by
      obtain ⟨mi, hg⟩ := h.good
      exact ⟨mi, hg, h.room⟩) (zeroArr_ct ha ht₁))
    (fun _ _ h => paddedZero_state ha hp hl h)) ?_
  refine RelCT.seq (two_post (Ψ := PaddedRegs a) (two_taint [.rdi] ?_ ht₂)
    (fun _ _ h => paddedArgs_state ha hp hl h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.good
    obtain ⟨mi', ht⟩ := ht.good
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.rsi, .rcx, .rbx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of the DSA witness interval test -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

structure SamplePublic where
  prime : PrimeParams
  bytes : List Byte
  length : bytes.length = prime.len

def SampleBefore (p : SamplePublic) (s : State) : Prop :=
  ∃ mi, SampleState p.prime.B p.prime.p p.prime.Z p.prime.w p.prime.N mi p.bytes s

def SamplePublic.padded (p : SamplePublic) : PaddedPublic :=
  ⟨p.prime.B, p.prime.Z, p.prime.w, p.prime.p, p.bytes.length⟩

def SampleLoaded (p : SamplePublic) (s : State) : Prop :=
  ∃ mi, ModulusReady s p.prime.B p.prime.Z p.prime.w mi p.prime.N ∧
    wv s.mem p.prime.B (slot p.prime.w aXm) p.prime.w = Spec.Rsa.os2ip p.bytes

theorem sampleLoad_ct : RelCT isa (Two SampleBefore)
    (Impl.Dsa.X86_64.Generation.loadPadded aXm kOut kUsedP) (fun _ _ => True) := by
  refine two_map SamplePublic.padded (fun p s h => ?_)
    (loadPadded_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))
  obtain ⟨mi, h⟩ := h
  exact ⟨⟨mi, h.ready.good⟩, p.prime.dims.z,
    by have := p.prime.dims.w4; dsimp [SamplePublic.padded]; omega_using [this],
    by have := p.prime.dims.w128; dsimp [SamplePublic.padded]; omega_using [this], h.ptr, h.len⟩

theorem sampleLoad_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded aXm kOut kUsedP) s (SampleLoaded p) := by
  obtain ⟨mi, h⟩ := h
  have hl : 1 ≤ p.bytes.length := by rw [p.length]; have := p.prime.len2; omega_using [this]
  have hb : p.bytes.length < 2 ^ 31 := by
    rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega_arith
  exact WP.mono (loadWitness_ok h.ready p.prime.dims (by decide) (by decide) h.ptr h.len h.source
    hl hb (by rw [p.length]; exact p.prime.lenWords)) fun _ ht => ⟨mi, ht.1, ht.2.1⟩

theorem sampleRange_ct : RelCT isa (Two SampleLoaded)
    Impl.Ffdh.X86_64.ParameterCandidate.witnessRange (fun _ _ => True) := by
  refine two_map (fun p : SamplePublic => p.padded.workspace) (fun p s h => ?_) witnessRange_ct
  obtain ⟨mi, h, _⟩ := h
  exact ⟨⟨mi, h.good, p.prime.dims.z⟩,
    by have := p.prime.dims.w4; dsimp [SamplePublic.padded, PaddedPublic.workspace]; omega_using [this],
    by have := p.prime.dims.w128; dsimp [SamplePublic.padded, PaddedPublic.workspace]; omega_using [this]⟩

theorem sampleRange_state {p : SamplePublic} {s : State} (h : SampleLoaded p s) :
    WP isa Impl.Ffdh.X86_64.ParameterCandidate.witnessRange s
      (fun t => t.gpr .rdi = p.prime.B) := by
  obtain ⟨mi, h, hx⟩ := h
  exact WP.mono (witnessRange_ok h p.prime.dims p.prime.odd hx) fun _ ht => ht.2.2.1.good.rdi

theorem testWitness_ct : RelCT isa (Two SampleBefore)
    Impl.Dsa.X86_64.Generation.testWitness (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.testWitness
  simp only [seqs]
  refine RelCT.seq (two_post sampleLoad_ct (fun _ _ h => sampleLoad_state h)) ?_
  refine RelCT.seq (two_post sampleRange_ct (fun _ _ h => sampleRange_state h)) ?_
  exact two_taint [.rdi] (by
    intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Fixed-address transformation of a nonuniform DSA witness -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem forceSampleArgs_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .rcx (.mem (hdr kUsedP)), .mov .rdi (.mem (hdr kOut))]) s
      (fun t => t.gpr .rdi = p.prime.p ∧ t.gpr .rcx = BitVec.ofNat 64 p.bytes.length) := by
  obtain ⟨mi, h⟩ := h
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off p.prime.B (8 * k)) 8 := fun k hk =>
    h.ready.good.scr.ld (by
      have := hdr_lt_slot p.prime.w 8 hk
      have := p.prime.dims.z
      omega_arith)
  xrun [State.ea, hdr, hdrOff, h.ready.good.rdi, hl kOut (by decide), hl kUsedP (by decide), h.ptr, h.len]

theorem forceStoredWitness_ct : RelCT isa (Two SampleBefore)
    (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut kUsedP) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.forceStoredWitness
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => forceSampleArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · refine RelCT.seq (two_taint [.rdi, .rcx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)) ?_
    exact RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

def SamplePublic.forced (p : SamplePublic) : SamplePublic :=
  ⟨p.prime, VG.Proof.Dsa.Generation.forcedWitnessBytes p.bytes,
    (VG.Proof.Dsa.Generation.forcedWitnessBytes_length
      (by rw [p.length]; exact p.prime.len2)).trans p.length⟩

theorem forceSample_state {p : SamplePublic} {s : State} (h : SampleBefore p s) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness kOut kUsedP) s
      (SampleBefore p.forced) := by
  obtain ⟨mi, h⟩ := h
  exact WP.mono (forceSample_ok h p.prime.dims
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega_arith))
    fun _ ht => ⟨mi, ht.1⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # DSA witness selection branches only on the public sampled candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def SampleSized (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleBefore p s ∧ p.bytes.length = len

def SampleTested (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleSized len p s ∧
    s.zf = some (!decide (2 ≤ Spec.Rsa.os2ip p.bytes ∧ Spec.Rsa.os2ip p.bytes < p.prime.N - 1))

theorem sampleTest_state {len : Nat} {p : SamplePublic} {s : State} (h : SampleSized len p s) :
    WP isa Impl.Dsa.X86_64.Generation.testWitness s (SampleTested len p) := by
  obtain ⟨⟨mi, hs⟩, hl⟩ := h
  refine WP.mono (testWitness_ok hs p.prime.dims p.prime.odd
    (by rw [p.length]; have := p.prime.len2; omega_using [this])
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega_arith)
    (by rw [p.length]; exact p.prime.lenWords)) fun t ht => ?_
  exact ⟨⟨⟨mi, ht.1⟩, hl⟩, ht.2.2.2.1⟩

theorem sampleWitness_ct (len : Nat) : RelCT isa (Two (SampleSized len))
    (Impl.Dsa.X86_64.Generation.sampleWitness) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.sampleWitness
  refine RelCT.seq (two_post
    (two_map id (fun _ _ h => h.1) testWitness_ct)
    (fun _ _ h => sampleTest_state h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun p s => SampleBefore p.forced s)
      (two_map id (fun _ _ h => h.1.1.1) forceStoredWitness_ct) ?_) ?_
    · exact fun p s h => forceSample_state h.1.1.1
    · exact two_map SamplePublic.forced (fun _ _ h => h) sampleLoad_ct
  · exact RelCT.block_nil (fun _ _ _ => True.intro)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of witness selection, the shared round, and completion policy -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

def SampleRoundBefore (len : Nat) (p : SamplePublic) (s : State) : Prop :=
  SampleSized len p s ∧ s.gpr .rsp = p.prime.sp

def SamplePublic.round (p : SamplePublic) : RoundPublic :=
  ⟨p.padded.workspace, p.prime.N,
    (Spec.RsaKeyGen.witness (p.prime.N - 1) (Spec.Rsa.os2ip p.bytes)).1, p.prime.sp⟩

theorem sampleRound_ready {len : Nat} {p : SamplePublic} {s : State}
    (h : SampleRoundBefore len p s) :
    WP isa (Impl.Dsa.X86_64.Generation.sampleWitness) s (BeforeRound p.round) := by
  obtain ⟨⟨⟨mi, hs⟩, -⟩, hsp⟩ := h
  refine WP.mono (sampleWitness_ok hs p.prime.dims p.prime.odd
    (by rw [p.length]; exact p.prime.len2)
    (by rw [p.length]; have := p.prime.lenDraw; have := p.prime.drawMax; omega_arith)
    (by rw [p.length]; exact p.prime.lenWords)
    (by rw [p.length]; exact p.prime.predBits)) fun t ht => ?_
  have hst : t.gpr .rsp = p.prime.sp := (ht.2.2.2.2.gpr (by decide)).trans hsp
  exact ⟨mi, ht.1, p.prime.dims, p.prime.room,
    ⟨by rw [hst]; exact p.prime.stackSize, by rw [hst]; exact p.prime.stackSeparate⟩,
    hst, p.prime.odd, p.prime.n3, ht.2.1⟩

def roundTailPublic (p : RoundPublic) : RoundTailPublic :=
  ⟨p.ws.B, p.ws.Z, p.ws.w, Spec.RsaKeyGen.mrIteration p.N
    (Spec.Rsa.splitTwos (p.N - 1)).1 (Spec.Rsa.splitTwos (p.N - 1)).2 p.a⟩

theorem roundTail_ready (M : Mont) (K : Kernel) {p : RoundPublic} {s : State}
    (h : BeforeRound p s) :
    WP isa (Impl.Ffdh.X86_64.ParameterCandidate.witnessRound M.mm K.run) s
      (RoundTailState (roundTailPublic p)) := by
  obtain ⟨mi, h, hd, hz, hr, _, ho, hn, ha⟩ := h
  exact WP.mono (round_ok M K h hd hz hr ho hn ha) fun _ ht =>
    ⟨⟨mi, ht.1.good⟩, hd.z, ht.2.1⟩

theorem sampleRound_ct (M : Mont) (K : Kernel) (len : Nat) :
    RelCT isa (Two (SampleRoundBefore len))
      (Impl.Dsa.X86_64.Generation.sampleRound M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.sampleRound
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) (sampleWitness_ct len))
    (fun _ _ h => sampleRound_ready h)) ?_
  refine RelCT.seq (two_post
    (two_map SamplePublic.round (fun _ _ h => h) (witnessRound_ct M K))
    (fun _ _ h => roundTail_ready M K h)) ?_
  exact two_map (fun p : SamplePublic => roundTailPublic p.round) (fun _ _ h => h) roundTail_ct

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of a complete entropy draw and shared primality round -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def DrawSized (len drawBytes : Nat) (p : DrawPublic) (s : State) : Prop :=
  DrawBefore len drawBytes p s ∧ p.used + p.prime.drawBytes ≤ p.prime.rand.length

def DrawPublic.sample (p : DrawPublic) (h : p.used + p.prime.drawBytes ≤ p.prime.rand.length) : SamplePublic :=
  ⟨p.prime, p.prime.drawSlice p.used, p.prime.slice_length h⟩

theorem drawSample_state {len drawBytes : Nat} {p : DrawPublic} {s : State}
    (h : DrawSized len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.drawCopy) s
      (SampleRoundBefore len (p.sample h.2)) := by
  obtain ⟨mi, hs⟩ := h.1.1
  have hw := drawBuffer_ok hs h.2
  exact WP.mono hw fun _ ht =>
    ⟨⟨⟨mi, ht.2.1⟩, (p.prime.slice_length h.2).trans h.1.2.1⟩, ht.1.stack⟩

theorem drawRound_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) :
    RelCT isa (Two (DrawSized len drawBytes))
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.drawRound
  refine RelCT.seq (two_post (Ψ := fun p s => ∃ h, SampleRoundBefore len (p.sample h) s)
    (two_map id (fun _ _ h => h.1) (drawCopy_ct len drawBytes))
    (fun _ _ h => WP.mono (drawSample_state h) fun _ ht => ⟨h.2, ht⟩)) ?_
  apply (sampleRound_ct M K len).mono
  · rintro s t ⟨p, ⟨hs, h⟩, ⟨ht, h'⟩⟩
    exact ⟨p.sample hs, h, h'⟩
  · exact fun _ _ h => h

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The guarded primality iteration reveals only the public tape and round -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaKeyGen.X86_64

structure PrimeIterationPublic where
  draw : DrawPublic
  i : Nat
  uni : Nat

def IterationBefore (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  DrawBefore len drawBytes p.draw s ∧ p.draw.used ≤ p.draw.prime.rand.length ∧
    word s.mem p.draw.prime.B (8 * kI) = BitVec.ofNat 64 p.i ∧
    word s.mem p.draw.prime.B (8 * kUni) = BitVec.ofNat 64 p.uni ∧
    p.i < 2 ^ 62 ∧ p.uni < 2 ^ 62

def IterationChecked (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  IterationBefore len drawBytes p s ∧
    s.cf = some (decide (p.draw.prime.rand.length < p.draw.used + p.draw.prime.drawBytes))

theorem iterationCheck_state {len drawBytes : Nat} {p : PrimeIterationPublic} {s : State}
    (h : IterationBefore len drawBytes p s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeCheck) s (IterationChecked len drawBytes p) := by
  obtain ⟨mi, hs⟩ := h.1.1
  refine WP.mono (tapeCheck_ok hs h.2.1) fun t ⟨hcf, hm, hk⟩ => ?_
  exact ⟨⟨⟨⟨mi, hs.of_mem hm (hk.mono (by decide))⟩, h.1.2⟩, h.2.1,
    by rw [hm]; exact h.2.2.1, by rw [hm]; exact h.2.2.2.1, h.2.2.2.2⟩, hcf⟩

theorem iterationDraw_state (M : Mont) (K : Kernel) {len drawBytes : Nat}
    {p : PrimeIterationPublic} {s : State} (h : IterationBefore len drawBytes p s)
    (hr : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run) s
      (fun t => t.gpr .rdi = p.draw.prime.B) := by
  obtain ⟨mi, hs⟩ := h.1.1
  have hw := drawRound_ok M K hs hr h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  exact WP.mono hw fun _ ht => ht.1.ready.good.rdi

theorem primeIteration_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) :
    RelCT isa (Two (IterationBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.primeIteration
        (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeIteration
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => iterationCheck_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1.1
    obtain ⟨mi', ht⟩ := ht.1.1
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · refine two_ite_seq (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    · exact two_taint [.rdi] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        obtain ⟨mi, hs⟩ := hs.1.1.1.1
        obtain ⟨mi', ht⟩ := ht.1.1.1.1
        exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm) (by taint_decide)
    · have room (p : PrimeIterationPublic) (s : State)
          (h : IterationChecked len drawBytes p s ∧ isa.eval .b s = some false) :
          p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
        simpa only [eval, h.1.2, Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] using h.2
      refine RelCT.seq (two_post
        (two_map PrimeIterationPublic.draw (fun p s h => ⟨h.1.1.1, room p s h⟩)
          (drawRound_ct M K len drawBytes))
        (fun p s h => iterationDraw_state M K h.1.1 (room p s h))) ?_
      exact two_taint [.rdi] (by
        intro p s t hs ht r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Public transitions of the finite DSA witness loop -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/IterationPublic.lean`, which only this module imported.
section

/-! # The next primality branch and uniform counter are functions of public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaKeyGen.X86_64

def PrimeIterationPublic.witness (p : PrimeIterationPublic) : Nat × Bool :=
  Spec.RsaKeyGen.witness (p.draw.prime.N - 1)
    (Spec.Rsa.os2ip ((p.draw.prime.rand.drop p.draw.used).take p.draw.prime.drawBytes))

def PrimeIterationPublic.nextUniform (p : PrimeIterationPublic) : Nat := p.uni + p.witness.2.toNat

def PrimeIterationPublic.continues (p : PrimeIterationPublic) : Bool :=
  decide (p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length) &&
    Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 &&
    decide (p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks)

theorem iteration_public (M : Mont) (K : Kernel) {p : PrimeIterationPublic} {mi : BitVec 64}
    {s₀ s : State} {res : Option (Bool × List Byte)}
    (h : PrimeLoopState p.draw.prime mi s₀ res p.i p.uni p.draw.used s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) s
      (fun t => isa.eval .e t = some p.continues ∧
        (p.continues = true → word t.mem p.draw.prime.B (8 * kUni) = BitVec.ofNat 64 p.nextUniform)) := by
  unfold Impl.Dsa.X86_64.Generation.primeIteration
  simp only [seqs]
  refine WP.seq (WP.mono (tapeCheck_ok h.state h.usedBound) fun u ⟨hcf, hm, ku⟩ => ?_)
  have hu := h.of_mem hm (ku.mono (by decide))
  refine WP.seq (WP.ite (decide (p.draw.prime.rand.length < p.draw.used + p.draw.prime.drawBytes))
    (by simp [eval, hcf]) (fun hshort => ?_) (fun hroom => ?_))
  · have hs : ¬ p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
      simpa only [decide_eq_true_eq, Nat.not_le] using hshort
    exact WP.seq_iff.mp (WP.mono (loopExhausted_ok hu (by omega_using [hs])) fun _ ht => by
      simpa only [PrimeIterationPublic.continues, decide_eq_false hs, Bool.false_and,
        Bool.false_eq_true, false_implies, and_true] using ht.1)
  · have hr : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := by
      simpa only [decide_eq_false_iff_not, Nat.not_lt] using hroom
    apply WP.seq_iff.mp
    refine WP.seq (WP.mono (drawRound_ok M K hu.state hr hu.ki hu.kuni
      hu.counter_bound.1 hu.counter_bound.2) fun v ⟨hv, hstat, hcount, _, _⟩ => ?_)
    change word v.mem p.draw.prime.B (8 * kStat) = BitVec.ofNat 64
      (if Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 then
        (if p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks then 4 else 1) else 3) at hstat
    refine WP.mono (statCmp_ok hv.ready.good p.draw.prime.dims.z
      (by split <;> (try split) <;> decide) hstat) fun t ⟨hz, hmem, _⟩ => ?_
    constructor
    · by_cases hp : Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 = true <;>
        by_cases hg : p.i + 1 < 17 ∨ p.nextUniform < p.draw.prime.checks <;>
        simp [eval, hz, PrimeIterationPublic.continues, hr, hp, hg]
    · intro hg
      have hp : Proof.MillerRabin.Round.round p.draw.prime.N p.witness.1 = true := by
        have hh := hg
        simp only [PrimeIterationPublic.continues, Bool.and_eq_true] at hh
        exact hh.1.2
      rw [hmem]
      exact (hcount hp).2

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

def PrimeIterationPublic.next (p : PrimeIterationPublic) : PrimeIterationPublic :=
  ⟨⟨p.draw.prime, p.draw.used + p.draw.prime.drawBytes⟩, p.i + 1, p.nextUniform⟩

def LoopBefore (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  (∃ mi s₀ res, PrimeLoopState p.draw.prime mi s₀ res p.i p.uni p.draw.used s) ∧
    p.draw.prime.len = len ∧ p.draw.prime.drawBytes = drawBytes

theorem LoopBefore.iteration {len drawBytes : Nat} {p : PrimeIterationPublic} {s : State}
    (h : LoopBefore len drawBytes p s) : IterationBefore len drawBytes p s := by
  obtain ⟨mi, s₀, res, hs⟩ := h.1
  exact ⟨⟨⟨mi, hs.state⟩, h.2⟩, hs.usedBound, hs.ki, hs.kuni, hs.counter_bound⟩

def LoopAfter (len drawBytes : Nat) (p : PrimeIterationPublic) (s : State) : Prop :=
  isa.eval .e s = some p.continues ∧ (p.continues = true → LoopBefore len drawBytes p.next s)

theorem primeIteration_transition (M : Mont) (K : Kernel) {len drawBytes : Nat}
    {p : PrimeIterationPublic} {s : State} (h : LoopBefore len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) s (LoopAfter len drawBytes p) := by
  obtain ⟨mi, s₀, res, hs⟩ := h.1
  have hw := (primeIteration_ok M K hs).and (iteration_public M K hs)
  refine WP.mono hw fun t ⟨ht, hz, huni⟩ => ⟨hz, fun hgo => ?_⟩
  rcases ht with ⟨he, _⟩ | ⟨_, uni', hn⟩
  · rw [hz, hgo] at he
    cases he
  · have heq : BitVec.ofNat 64 uni' = BitVec.ofNat 64 p.nextUniform := hn.kuni.symm.trans (huni hgo)
    have hb : p.witness.2.toNat ≤ 1 := by cases p.witness.2 <;> decide
    have hsmall : p.nextUniform < 2 ^ 64 := by
      unfold PrimeIterationPublic.nextUniform
      have := hs.counter_bound.2
      omega_using [hb, this]
    have hsmall' : uni' < 2 ^ 64 := by have := hn.counter_bound.2; omega_using [this]
    have he : uni' = p.nextUniform := by
      have hh := congrArg BitVec.toNat heq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall'] using hh
    subst uni'
    exact ⟨⟨mi, s₀, res, by simpa only [PrimeIterationPublic.next, h.2.2] using hn⟩, h.2⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Constant-time composition of the complete blinded primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

private def loopInv (len drawBytes n : Nat) : State → State → Prop :=
  Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopBefore len drawBytes p s

section
variable (M : Mont) (K : Kernel) (len drawBytes : Nat)

private theorem loop_step (n : Nat) :
    RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.X86_64.Generation.primeIteration
        (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run))
      (fun s t => isa.eval .e s = isa.eval .e t ∧
        (isa.eval .e s = some false → True) ∧
        (isa.eval .e s = some true → ∃ m < n, loopInv len drawBytes m s t)) := by
  have hw : RelCT isa (loopInv len drawBytes n)
      (Impl.Dsa.X86_64.Generation.primeIteration
        (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run))
      (Two fun p s => p.draw.prime.rand.length - p.draw.used = n ∧ LoopAfter len drawBytes p s) :=
    two_post (two_map id (fun _ _ h => h.2.iteration) (primeIteration_ct M K len drawBytes))
      (fun _ _ h => WP.mono (primeIteration_transition M K h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hw.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have hg : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have hnext := hs.2 hg
  obtain ⟨mi, s₀, res, hstate⟩ := hnext.1
  have hroom : p.draw.used + p.draw.prime.drawBytes ≤ p.draw.prime.rand.length := hstate.usedBound
  have hdraw := p.draw.prime.drawMin
  refine ⟨p.draw.prime.rand.length - (p.draw.used + p.draw.prime.drawBytes), by omega_using [hn, hroom, hdraw],
    p.next, ⟨rfl, hnext⟩, rfl, ht.2 hg⟩

theorem primeLoop_ct : RelCT isa (Two (LoopBefore len drawBytes))
    (.loop (Impl.Dsa.X86_64.Generation.primeIteration
      (Impl.Dsa.X86_64.Generation.drawRound M.mm K.run)) .e) (fun _ _ => True) := by
  rintro s t tr₁ tr₂ u v ⟨p, hs, ht⟩ e₁ e₂
  exact RelCT.loop (loopInv len drawBytes) (loop_step M K len drawBytes)
    (p.draw.prime.rand.length - p.draw.used) s t tr₁ tr₂ u v ⟨p, ⟨rfl, hs⟩, rfl, ht⟩ e₁ e₂

theorem millerRabin_ct :
    RelCT isa (Two fun p s => DrawBefore len drawBytes p s ∧ p.used ≤ p.prime.rand.length)
      (Impl.Dsa.X86_64.Generation.millerRabin M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.millerRabin
  refine RelCT.seq (two_post (Ψ := fun p s => LoopBefore len drawBytes ⟨p, 1, 0⟩ s)
    (two_taint [.rdi] ?_ (by taint_decide)) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs.1.1
    obtain ⟨mi', ht⟩ := ht.1.1
    exact hs.ready.good.rdi.trans ht.ready.good.rdi.symm
  · intro p s h
    obtain ⟨mi, hs⟩ := h.1.1
    exact WP.mono (primeLoopInit_ok hs h.2) fun _ ht =>
      ⟨⟨mi, s, primeRest p.prime 1 0 p.used, ht⟩, h.1.2⟩
  · exact two_map (fun p : DrawPublic => (⟨p, 1, 0⟩ : PrimeIterationPublic))
      (fun _ _ h => h) (primeLoop_ct M K len drawBytes)

end
end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of the complete DSA probable-prime operation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem primeCall_setup {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) : PrimeSetupBefore p.draw.prime s := by
  obtain ⟨mi, hs⟩ := h.1
  exact ⟨⟨mi, hs.good⟩, hs.n, p.width⟩

theorem primeCall_ready (M : Mont) {len drawBytes : Nat} {p : PrimeCallPublic} {s : State}
    (h : PrimeCallBefore len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSetup M.mm) s
      (fun t => DrawBefore len drawBytes p.draw t ∧ p.draw.used ≤ p.draw.prime.rand.length) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (primeInputSetup_ok M hs p.width) fun _ ⟨mi', ht, _, _⟩ =>
    ⟨⟨⟨mi', ht⟩, h.2.2.2⟩, h.2.2.1⟩

theorem probablePrime_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) :
    RelCT isa (Two (PrimeCallBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.probablePrime M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.probablePrime
  refine RelCT.seq (two_post (primeTrial_ct len drawBytes) (fun _ _ h => primeTrial_tested h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun p : PrimeCallPublic => p.draw.prime) (fun _ _ h => primeCall_setup h.1.1)
        (primeSetup_ct M)) (fun _ _ h => primeCall_ready M h.1.1)) ?_
    exact two_map PrimeCallPublic.draw (fun _ _ h => h) (millerRabin_ct M K len drawBytes)
  · exact two_taint [.rdi] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr
      subst r
      obtain ⟨mi, hs⟩ := hs.1.1.1
      obtain ⟨mi', ht⟩ := ht.1.1.1
      exact hs.good.rdi.trans ht.good.rdi.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of primality testing directly from the saved candidate bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

structure PrimeBytesPublic where
  call : PrimeCallPublic
  source : Addr
  bytes : List Byte
  length : bytes.length = call.draw.prime.len
  value : Spec.Rsa.os2ip bytes = call.draw.prime.N

def PrimeBytesBefore (len drawBytes : Nat) (p : PrimeBytesPublic) (s : State) : Prop :=
  (∃ mi, PrimeArguments p.call.draw.prime mi p.call.draw.used s) ∧
    word s.mem p.call.draw.prime.B 160 = p.source ∧ Src s p.call.draw.prime.B p.call.draw.prime.Z p.source p.bytes ∧
    s.wr = p.call.wr ∧ p.call.draw.used ≤ p.call.draw.prime.rand.length ∧
    p.call.draw.prime.len = len ∧ p.call.draw.prime.drawBytes = drawBytes

def PrimeBytesPublic.padded (p : PrimeBytesPublic) : PaddedPublic :=
  ⟨p.call.draw.prime.B, p.call.draw.prime.Z, p.call.draw.prime.w, p.source, p.call.draw.prime.len⟩

theorem primeBytesLoad_ct (len drawBytes : Nat) : RelCT isa (Two (PrimeBytesBefore len drawBytes))
    (Impl.Dsa.X86_64.Generation.loadPadded 0 20 18) (fun _ _ => True) := by
  refine two_map PrimeBytesPublic.padded (fun p s h => ?_)
    (loadPadded_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))
  obtain ⟨mi, hs⟩ := h.1
  exact ⟨⟨mi, hs.good⟩, p.call.draw.prime.dims.z,
    by change 1 ≤ p.call.draw.prime.w; have := p.call.draw.prime.dims.w4; omega_using [this],
    by change p.call.draw.prime.w < 2 ^ 31; have := p.call.draw.prime.dims.w128; omega_using [this],
    h.2.1, hs.len⟩

theorem primeBytesLoad_ready {len drawBytes : Nat} {p : PrimeBytesPublic} {s : State}
    (h : PrimeBytesBefore len drawBytes p s) :
    WP isa (Impl.Dsa.X86_64.Generation.loadPadded 0 20 18) s (PrimeCallBefore len drawBytes p.call) := by
  obtain ⟨mi, hs⟩ := h.1
  exact WP.mono (loadPrimeBytes_ok hs h.2.1 p.length p.value h.2.2.1) fun _ ⟨ht, _, hk⟩ =>
    ⟨⟨mi, ht⟩, hk.2.2.trans h.2.2.2.1, h.2.2.2.2⟩

theorem primeBytes_ct (M : Mont) (K : Kernel) (len drawBytes : Nat) :
    RelCT isa (Two (PrimeBytesBefore len drawBytes))
      (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.primeBytes
  exact RelCT.seq (two_post (primeBytesLoad_ct len drawBytes) (fun _ _ h => primeBytesLoad_ready h))
    (two_map PrimeBytesPublic.call (fun _ _ h => h) (probablePrime_ct M K len drawBytes))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The probable-prime test's timing depends only on its public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- What the contract makes public: the arguments, the size among them, the
stack pointer, the candidate and the tape. -/
structure View where
  rdi : Addr
  rsi : Addr
  rdx : Addr
  rcx : Addr
  r8 : Addr
  r9 : Addr
  rsp : Addr
  N : Nat
  rand : List Byte

def view (s : State) : View :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, s.gpr .rsp,
    candidateOf (s.gpr .r9).toNat s, Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem view_of_pub {s₁ s₂ : State} (h : contract.pub s₁ s₂) : view s₁ = view s₂ := by
  sig_pub [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi,
    argRegs] at h
  obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  obtain ⟨-, hl⟩ := List.cons.inj hl
  obtain ⟨hN, hr⟩ := List.cons.inj hl
  have hr' := map_toNat_inj hr
  unfold view candidateOf
  rw [hN, hr', hsp, hdi, hsi, hdx, hcx, h8, h9]

/-- Big-endian octet strings of one length are equal if their values are. -/
theorem os2ip_inj : ∀ {l₁ l₂ : List Byte}, l₁.length = l₂.length →
    Spec.Rsa.os2ip l₁ = Spec.Rsa.os2ip l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [os2ip_cons, os2ip_cons, hl] at h
    have h₁ := os2ip_lt l₁
    have h₂ := os2ip_lt l₂
    rw [hl] at h₁
    have hd : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) / 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) / 256 ^ l₂.length := by rw [h]
    have hm : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) % 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) % 256 ^ l₂.length := by rw [h]
    have hp : 0 < 256 ^ l₂.length := Nat.pow_pos (by decide)
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₁, Nat.zero_add,
      Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₂, Nat.zero_add] at hd
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₁,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂] at hm
    rw [BitVec.eq_of_toNat_eq hd, os2ip_inj hl hm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Dsa.X86_64.Generation (PrimeParams PrimeCallPublic PrimeBytesPublic PrimeBytesBefore
  CalleeHeaderLayout DrawPublic)

theorem params_ext {P Q : PrimeParams} (hB : P.B = Q.B) (hp : P.p = Q.p) (hrp : P.rp = Q.rp)
    (hsp : P.sp = Q.sp) (hZ : P.Z = Q.Z) (hw : P.w = Q.w) (hN : P.N = Q.N) (hlen : P.len = Q.len)
    (hd : P.drawBytes = Q.drawBytes) (hc : P.checks = Q.checks) (hr : P.rand = Q.rand) : P = Q := by
  cases P; cases Q
  simp only at hB hp hrp hsp hZ hw hN hlen hd hc hr
  subst hB hp hrp hsp hZ hw hN hlen hd hc hr
  rfl

/-- The test's public parameters, as the generation's timing lemmas take them. -/
def callPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeCallPublic where
  draw := ⟨params hb A, 0⟩
  arena := s.gpr .rdi
  wr := (allocState 56 s).wr
  layout := by
    right
    have hw : (allocState 56 s).wr = [⟨frameSp s, 56⟩, wsRegion s, ⟨s.gpr .r8, 8⟩] := by
      change ⟨frameSp s, 56⟩ :: s.wr = _; rw [A.wr]
    rw [hw]
    refine ⟨⟨frameSp s, 56⟩, ⟨s.gpr .r8, 8⟩, (s.gpr .rsi).toNat * 8, rfl,
      by have := A.size; have : domainCheck = 40960 := rfl; omega_arith, ?_, ?_⟩
    · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
      simp only [off, BitVec.add_zero] at hs
      refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact A.stackWs.sub_left hs
        · exact A.stackUsed.sub_left hs
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact A.wsUsed
      · intro r hr; cases hr
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (by decide : (56 : Nat) ≤ 2 ^ 64)
      · have := A.wsBound; change (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64; omega_using [this]
      · exact (by decide : (8 : Nat) ≤ 2 ^ 64)
  base := rfl
  width := by change words bits ≤ 48; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  tab := by
    change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  large := by
    change 8161 < candidateOf bits s
    have hlow := ((bitLength_iff_bounds (by have := hb.le; omega_using [this])).mp A.bits).1
    have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega_using [this])
    have : (8161 : Nat) < 2 ^ 159 := by decide
    exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow)
  policy := by
    change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
    rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

def bytesPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeBytesPublic where
  call := callPublic hb A
  source := off (s.gpr .rdi) (candidate bits)
  bytes := Spec.Rsa.bytesAt s.mem (off (s.gpr .rdi) (candidate bits)) (len bits)
  length := bytesAt_length _ _ _
  value := rfl

theorem PrimeABI.toNat_r9 {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) :
    (s.gpr .r9).toNat = bits := by
  rw [A.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.le; omega_using [this])]

theorem bytesPublic_eq {bits : Nat} (hb : Supported bits) {s₁ s₂ : State} (A₁ : PrimeABI bits s₁)
    (A₂ : PrimeABI bits s₂) (hv : view s₁ = view s₂) : bytesPublic hb A₁ = bytesPublic hb A₂ := by
  simp only [view, View.mk.injEq, A₁.toNat_r9 hb, A₂.toNat_r9 hb] at hv
  obtain ⟨hdi, hsi, hdx, hcx, h8, -, hsp, hN, hr⟩ := hv
  have hP : params hb A₁ = params hb A₂ :=
    params_ext (by simp only [params, hdi]) (by simp only [params, hdi]) hdx (by simp only [params, frameSp, hsp])
      rfl rfl hN rfl rfl rfl hr
  have hwr : (allocState 56 s₁).wr = (allocState 56 s₂).wr := by
    change ⟨frameSp s₁, 56⟩ :: s₁.wr = ⟨frameSp s₂, 56⟩ :: s₂.wr
    rw [A₁.wr, A₂.wr, frameSp, frameSp, hsp, hdi, hsi, h8]
  have hbytes : Spec.Rsa.bytesAt s₁.mem (off (s₁.gpr .rdi) (candidate bits)) (len bits) =
      Spec.Rsa.bytesAt s₂.mem (off (s₂.gpr .rdi) (candidate bits)) (len bits) :=
    os2ip_inj (by rw [bytesAt_length, bytesAt_length]) hN
  rw [hdi] at hbytes
  unfold bytesPublic callPublic
  simp only [hP, hwr, hdi, hbytes]

theorem before_of_ready {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u : State}
    (R : Ready hb A u) : PrimeBytesBefore (len bits) (draw bits) (bytesPublic hb A) u :=
  ⟨⟨0, R.args⟩, R.ptr, R.src, R.wr, Nat.zero_le _, rfl, rfl⟩

/-! ## The stages, each with the public view of the arguments -/

def Entered (v : View) (u : State) : Prop :=
  ∃ s, ∃ _ : Supported v.r9.toNat, ∃ _ : PrimeABI v.r9.toNat s, view s = v ∧ u = allocState 56 s

def ReadyAt (v : View) (u : State) : Prop :=
  ∃ s, ∃ hb : Supported v.r9.toNat, ∃ A : PrimeABI v.r9.toNat s, view s = v ∧ Ready hb A u

def TestedAt (v : View) (u : State) : Prop :=
  ∃ s, ∃ hb : Supported v.r9.toNat, ∃ A : PrimeABI v.r9.toNat s, view s = v ∧ Tested hb A u

/-- The workspace, the stack pointer and `used` in their registers. -/
def Loaded (v : View) (u : State) : Prop :=
  u.gpr .rdi = off v.rdi arithmetic ∧ u.gpr .rsp = v.rsp - BitVec.ofNat 64 56 ∧ u.gpr .r8 = v.r8

theorem post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem setup_ct : RelCT isa (Two Entered) setup (Two ReadyAt) := by
  have pins : Pins Entered [.rdi, .rsp, .r9] := by
    rintro v u₁ u₂ ⟨s₁, -, -, h₁, rfl⟩ ⟨s₂, -, -, h₂, rfl⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have h := h₁.trans h₂.symm
    simp only [view, View.mk.injEq] at h
    rcases hr with rfl | rfl | rfl
    · simp [allocState, State.setReg, h.1]
    · simp [allocState, State.setReg, h.2.2.2.2.2.2.1]
    · simp [allocState, State.setReg, h.2.2.2.2.2.1]
  refine two_post (two_taint [.rdi, .rsp, .r9] pins (by taint_decide))
    fun v u ⟨s, hb, A, hv, hu⟩ => hu ▸ WP.mono (prep_ok hb A) fun t R => ⟨s, hb, A, hv, R⟩

theorem test_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two ReadyAt) (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run) (Two TestedAt) := by
  rintro u₁ u₂ t₁ t₂ u₁' u₂' ⟨v, ⟨s₁, hb, A₁, hv₁, R₁⟩, ⟨s₂, _, A₂, hv₂, R₂⟩⟩ e₁ e₂
  have hct := VG.Proof.Dsa.X86_64.Generation.primeBytes_ct M K (len v.r9.toNat) (draw v.r9.toNat)
  have hp₂ : PrimeBytesBefore (len v.r9.toNat) (draw v.r9.toNat) (bytesPublic hb A₁) u₂ := by
    rw [bytesPublic_eq hb A₁ A₂ (hv₁.trans hv₂.symm)]; exact before_of_ready hb A₂ R₂
  exact ⟨(hct _ _ _ _ _ _ ⟨_, before_of_ready hb A₁ R₁, hp₂⟩ e₁ e₂).1, v,
    ⟨s₁, hb, A₁, hv₁, post_of_exec (test_ok M K hb A₁ R₁) e₁⟩,
    ⟨s₂, hb, A₂, hv₂, post_of_exec (test_ok M K hb A₂ R₂) e₂⟩⟩

/-- The exit's loads of the workspace's word and of `used`. -/
abbrev exitLoad : List Instr :=
  [.mov .rax (.mem (Impl.Bignum.X86_64.hdr kUsed)), .mov .r8 (.mem (sp 48))]

abbrev exitStatus : List Instr :=
  [.store { base := .r8 } .rax, .mov .rax (.mem (Impl.Bignum.X86_64.hdr kStat)), .mov .rcx (.reg .rax),
    .shift .shr .rcx 1, .alu .sub .rax (.reg .rcx)]

theorem tested_regs {bits : Nat} {hb : Supported bits} {s u : State} {A : PrimeABI bits s}
    (T : Tested hb A u) : u.gpr .rdi = off (s.gpr .rdi) arithmetic ∧ u.gpr .rsp = frameSp s := by
  obtain ⟨⟨_, _, inp, _⟩, _⟩ := T
  exact ⟨inp.good.rdi, inp.stack⟩

theorem load_ok {v : View} {u : State} (h : TestedAt v u) :
    WP isa (.block exitLoad) u (Loaded v) := by
  obtain ⟨s, hb, A, rfl, T⟩ := h
  obtain ⟨hdi, hsp⟩ := tested_regs T
  obtain ⟨⟨_, _, inp, _⟩, _, hu, _, _, hwr⟩ := T
  have h200 := inp.good.scr.ld (d := 200) (by change _ ≤ arithmeticBytes; decide)
  have h48 : InRegions (u.rd ++ u.wr) (off (frameSp s) 48) 8 :=
    ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self),
      Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.gpr .r8 = s.gpr .r8) (by
    xrun [exitLoad, sp, State.ea, BitVec.ofInt_natCast, Impl.Bignum.X86_64.hdr, inp.good.rdi, kUsed,
      VG.Impl.Bignum.sFn, hdrOff, Nat.reduceAdd, Nat.reduceMul, h200, hsp, h48]
    exact hu) rfl) fun t ⟨h8, hk⟩ => ?_
  exact ⟨(hk.gpr (by decide)).trans hdi, (hk.gpr (by decide)).trans hsp, h8⟩

theorem finish_ct :
    RelCT isa (Two TestedAt) (.seq (.block exit) (.block restoreRegisters)) fun _ _ => True := by
  have pins : Pins TestedAt [.rdi, .rsp] := by
    rintro v u₁ u₂ ⟨s₁, _, A₁, h₁, T₁⟩ ⟨s₂, _, A₂, h₂, T₂⟩ r hr
    have h := h₁.trans h₂.symm
    simp only [view, View.mk.injEq] at h
    obtain ⟨d₁, p₁⟩ := tested_regs T₁
    obtain ⟨d₂, p₂⟩ := tested_regs T₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [d₁, d₂, h.1]
    · rw [p₁, p₂, frameSp, frameSp, h.2.2.2.2.2.2.1]
  refine RelCT.seq (R := fun (a b : State) => ∀ r ∈ [Reg.rsp], a.gpr r = b.gpr r) ?_ ?_
  · change RelCT isa _ (.block (exitLoad ++ exitStatus)) _
    refine RelCT.block_append (RelCT.seq
      (two_post (two_taint [.rdi, .rsp] pins (by taint_decide)) fun v u h => load_ok h) ?_)
    refine RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsp, .r8]) (fun x y ⟨v, h₁, h₂⟩ => Taint.agree_ofRegs ?_)
      [.rsp] (by taint_decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  · exact RelCT.mono (RelCT.taintRegs (τ := Taint.ofRegs [.rsp]) (fun x y h => Taint.agree_ofRegs h) []
      (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial

theorem code_ct (M : Mont) (K : Kernel) :
    ConstantTime isa contract.pre contract.pub (code M.mm K.run) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
  refine RelCT.mono (RelCT.seq setup_ct (RelCT.seq (test_ct M K) finish_ct)) ?_ fun _ _ h => h
  rintro a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
  have hv := view_of_pub hp
  have h9 : s₂.gpr .r9 = s₁.gpr .r9 := by
    simp only [view, View.mk.injEq] at hv; exact hv.2.2.2.2.2.1.symm
  obtain ⟨hb₁, A₁⟩ := primeABI_of h₁
  obtain ⟨-, A₂⟩ := primeABI_of h₂
  rw [h9] at A₂
  exact ⟨view s₁, ⟨s₁, hb₁, A₁, rfl, rfl⟩, ⟨s₂, hb₁, A₂, hv.symm, rfl⟩⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
