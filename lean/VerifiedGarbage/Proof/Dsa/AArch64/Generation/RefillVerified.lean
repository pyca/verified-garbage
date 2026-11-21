module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.CT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT -- shake: keep (pairs with its `public meta import` for `taint_decide`)
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Finish
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
public meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp -- shake: keep (the statements need `WP` and `preserved`; narrowing it does not build)
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Finish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generator
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopState
public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime

/-! ### `Dsa.AArch64.Generator.Verified`, which only this module used -/

section

/-! ### `Dsa.AArch64.ProbablePrime.Depth`, which this module and modules that import it used -/

section

/-! # The probable-prime test's frames: its own 272 bytes

The test itself has no frames (its arithmetic and the shared round have
none), so its stack is its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem aarch64Depth_of_noFrames : ∀ (c : Prog isa), c.noFrames = true → c.aarch64Depth = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames a h.1, aarch64Depth_of_noFrames b h.2, Nat.max_self]
  | .ite _ t e, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames t h.1, aarch64Depth_of_noFrames e h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames b h]
  | .call _ b, h => by
    simp only [Code.noFrames] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames b h]
  | .frame .., h => by simp [Code.noFrames] at h
  | .icall _ _ b n, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [Code.aarch64Depth, aarch64Depth_of_noFrames b h.1, aarch64Depth_of_noFrames n h.2, Nat.max_self]

theorem test_noFrames (v : RoundImpl) (bits : Nat) :
    (Impl.Dsa.AArch64.ProbablePrime.test bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run).noFrames = true := by
  simp only [Impl.Dsa.AArch64.ProbablePrime.test, checkPrime, workspace, primeFromFrame, primeBytes,
    probablePrime, primeSetup, primeR2, primeConstants, millerRabin, drawRound, primeIteration, sampleRound,
    witnessRound, roundTail, sampleWitness, forceStoredWitness, testWitness, loadWitness, testRange, witnessRange,
    drawCopy, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Rsa.AArch64.r2Steps,
    Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice, VG.Proof.Dsa.AArch64.Generation.publicKernel, VG.Proof.Dsa.AArch64.Generation.PublicKernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | rfl | exact VG.Proof.Dsa.AArch64.Generation.publicRound_noFrames v.noFrames

open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
  VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64 in
/-- The round for public candidates never touches PSTATE.DIT where the
shared round does not: they differ in the selection, which is blocks and a
loop without it. -/
theorem publicRound_noDit {mul : Nat → Nat → Nat → Prog isa}
    (h : (VG.Impl.MillerRabin.AArch64.round mul).all (fun i => !i.touchesDit) = true) :
    (publicRound mul).all (fun i => !i.touchesDit) = true := by
  simp only [VG.Impl.MillerRabin.AArch64.round, roundW, preparedRoundW, mrExpLoopW, mrWin, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, mrSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop, VG.Impl.Rsa.AArch64.Crt.selLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.all, Bool.and_eq_true] at h
  simp only [publicRound, publicWin, roundW, preparedRoundW, mrExpLoopW, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, publicSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.all, Bool.and_eq_true, h, and_true,
    true_and]
  decide

open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
  VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64 in
/-- As `publicRound_noDit`, for writes of PSTATE.DIT and indirect calls
(`Scrub.sideAll`): what a cleanup needs of the code it follows. -/
theorem publicRound_side {mul : Nat → Nat → Nat → Prog isa}
    (h : Scrub.sideAll (fun i => !i.writesDit) (VG.Impl.MillerRabin.AArch64.round mul) = true) :
    Scrub.sideAll (fun i => !i.writesDit) (publicRound mul) = true := by
  simp only [VG.Impl.MillerRabin.AArch64.round, roundW, preparedRoundW, mrExpLoopW, mrWin, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, mrSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop, VG.Impl.Rsa.AArch64.Crt.selLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Scrub.sideAll, Bool.and_eq_true] at h
  simp only [publicRound, publicWin, roundW, preparedRoundW, mrExpLoopW, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, publicSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Scrub.sideAll, Bool.and_eq_true, h, and_true,
    true_and]
  decide

/-- The test never touches PSTATE.DIT: neither its own code (decided for each
size, `Supported`, whose instruction lists are long) nor the round's. -/
theorem test_noDit (v : RoundImpl) {bits : Nat}
    (hb : bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072) :
    (Impl.Dsa.AArch64.ProbablePrime.test bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run).all
      (fun i => !i.touchesDit) = true := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Impl.Dsa.AArch64.ProbablePrime.test, checkPrime, workspace, primeFromFrame, primeBytes,
    probablePrime, primeSetup, primeR2, primeConstants, millerRabin, drawRound, primeIteration, sampleRound,
    witnessRound, roundTail, sampleWitness, forceStoredWitness, testWitness, loadWitness, testRange, witnessRange,
    drawCopy, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Rsa.AArch64.r2Steps,
    Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice, VG.Proof.Dsa.AArch64.Generation.publicKernel, VG.Proof.Dsa.AArch64.Generation.PublicKernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, Impl.Bignum.AArch64.seqs, Code.all, Bool.and_eq_true, v.mmNoDit,
    true_and] <;>
  and_intros <;>
  first | with_reducible exact publicRound_noDit v.noDit | lit_decide

/-- As `test_noDit`, for writes of PSTATE.DIT and indirect calls
(`Scrub.sideAll`). -/
theorem test_side (v : RoundImpl) {bits : Nat}
    (hb : bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072) :
    Scrub.sideAll (fun i => !i.writesDit)
      (Impl.Dsa.AArch64.ProbablePrime.test bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run) = true := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Impl.Dsa.AArch64.ProbablePrime.test, checkPrime, workspace, primeFromFrame, primeBytes,
    probablePrime, primeSetup, primeR2, primeConstants, millerRabin, drawRound, primeIteration, sampleRound,
    witnessRound, roundTail, sampleWitness, forceStoredWitness, testWitness, loadWitness, testRange, witnessRange,
    drawCopy, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Rsa.AArch64.r2Steps,
    Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Bignum.AArch64.R2Div.choice, VG.Proof.Dsa.AArch64.Generation.publicKernel, VG.Proof.Dsa.AArch64.Generation.PublicKernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, Impl.Bignum.AArch64.seqs, Scrub.sideAll, Bool.and_eq_true, v.mmSide,
    true_and] <;>
  and_intros <;>
  first | with_reducible exact publicRound_side v.side | lit_decide

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.Generator.CT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generator.Public`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.PackPartCT`, which only this module used -/

section

/-! # Copy generated components using only public addresses and lengths -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

structure PackPublic where
  B : Addr
  F : Addr
  S : Addr

def PackBefore (p : PackPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B

def PackReady (src dst len : Nat) (p : PackPublic) (s : State) : Prop :=
  s.gpr .x12 = VG.Proof.Bignum.off p.B src ∧ s.gpr .x2 = VG.Proof.Bignum.off p.B dst ∧
  s.gpr .x9 = BitVec.ofNat 64 len

theorem packPart_ct (src dst len : Nat) (hs : src < 2 ^ 16) (hd : dst < 2 ^ 16) (hl : len ≤ 1024)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two PackBefore) (packPart src dst len) (fun _ _ => True) := by
  unfold packPart
  refine RelCT.seq (two_post (Ψ := PackReady src dst len)
    (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht) ?_) ?_
  · intro p s ⟨L, V, W, R, hb⟩
    exact WP.mono (packArgs_ok L R hs hd hl) fun t ⟨hsi, hdi, hcx, _, _⟩ =>
      ⟨hb ▸ hsi, hb ▸ hdi, hcx⟩
  · exact two_taint [.x12, .x2, .x9] (fun p s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.ValidateCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.DomainCallCT`, which only this module used -/

section

/-! # Call the existing domain checker with public packed bytes and pointers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

structure DomainCallPublic where
  input : ParametersInput
  pointer : Addr

def DomainCallBefore (p : DomainCallPublic) (s : State) : Prop :=
  ParametersPre p.input s ∧ s.gpr .x0 = p.pointer

theorem domainCall_related {s t : State} (h : Two DomainCallBefore s t) : Two ParametersStart s t := by
  obtain ⟨p, ⟨hs, hp⟩, ⟨ht, hq⟩, hsp⟩ := h
  let a : ParametersCall := ⟨p.input, s, hs⟩
  let b : ParametersCall := ⟨p.input, t, ht⟩
  have fields : checkFieldValues t p.input.accepted = checkFieldValues s p.input.accepted := by
    funext f
    cases f <;> simp only [checkFieldValues, hp, hq, hs.pLength, ht.pLength, hs.qLength, ht.qLength]
  have layout : b.layout = a.layout := by
    change p.input.layout t ht.pLength ht.qLength = p.input.layout s hs.pLength hs.qLength
    simp only [ParametersInput.layout, fields]
  exact ⟨a, ⟨a, ⟨rfl, rfl⟩, rfl⟩, ⟨b, ⟨layout, rfl⟩, rfl⟩, hsp⟩

theorem domainCall_ct (M : Mont)  :
    RelCT isa (Two DomainCallBefore) (Generate.checkParameters M.mm) (fun _ _ => True) :=
  (parametersMain_ct M).mono (fun _ _ h => domainCall_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing of final parameter validation and its success/retry decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generation

structure ValidatePublic where
  input : ParametersInput
  B : Addr
  F : Addr
  S : Addr
  base : input.base = VG.Proof.Bignum.off B domainCheck
  frame : (⟨F, frameBytes⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩
  hash : (⟨S, oRsa⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩

def ValidatePublic.call (p : ValidatePublic) : DomainCallPublic := ⟨p.input, VG.Proof.Bignum.off p.B packed⟩

def ValidateBefore (pLen qLen : Nat) (p : ValidatePublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ (∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B) ∧
  Scr s p.input.base Impl.Dsa.Layout.usedBytes ∧
  Src s p.input.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off p.B packed) p.input.params ∧
  p.input.pLen = pLen ∧ p.input.qLen = qLen

theorem validateArgs_ready {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) (h : ValidateBefore pLen qLen p s) :
    WP isa (.block (validateArgs pLen qLen)) s (DomainCallBefore p.call) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  refine WP.mono (validateArgs_ok L R hp hq) fun t ⟨hd, h8, hdx, hcx, hm, hk⟩ => ?_
  have hd' : t.gpr .x0 = VG.Proof.Bignum.off p.B packed := hb ▸ hd
  refine ⟨⟨hs.congr hk.wr, (hb ▸ h8).trans p.base.symm,
    by change t.gpr .x2 = BitVec.ofNat 64 p.input.pLen; rw [heP]; exact hdx,
    by change t.gpr .x3 = BitVec.ofNat 64 p.input.qLen; rw [heQ]; exact hcx, ?_⟩, hd'⟩
  rw [hd']
  exact src.congrK (fun _ _ => by rw [hm]) hk

def ValidateResult (p : ValidatePublic) (s : State) : Prop :=
  s.sp = p.F ∧ s.gpr .x0 = BitVec.ofNat 64
    (if Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params then 1 else 0)

theorem validateCore_result (M : Mont)  {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) (h : ValidateBefore pLen qLen p s) :
    WP isa (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.AArch64.Generate.checkParameters M.mm))
      s (ValidateResult p) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  have step := validateCore_ok M p.input L R (by rw [hb]; exact p.base)
    (by rw [heP]; exact hp) (by rw [heQ]; exact hq) hs (hb ▸ src) p.frame p.hash
  rw [heP, heQ] at step
  exact WP.mono step fun t ⟨hr, Lt, _, _, _⟩ =>
    ⟨Lt.sp, by simpa only [heP, heQ] using hr⟩

theorem validate_ct_of (M : Mont)  (pLen qLen : Nat)
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (validateArgs pLen qLen)) hc).isSome = true) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate M.mm pLen qLen) (fun _ _ => True) := by
  have core : RelCT isa (Two (ValidateBefore pLen qLen))
      (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.AArch64.Generate.checkParameters M.mm))
      (Two ValidateResult) := by
    refine two_post (RelCT.seq (two_post
      (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht)
      (fun _ _ h => validateArgs_ready hp hq h))
      (two_map ValidatePublic.call (fun _ _ h => h) (domainCall_ct M)))
      (fun _ _ h => validateCore_result M hp hq h)
  unfold validate
  refine RelCT.seq core (two_ite (fun _ _ _ hs ht => by
    change some (_ == (0#64)) = some (_ == (0#64))
    simp only [State.read, Size.bits, BitVec.setWidth_eq, hs.2, ht.2]) ?_ ?_)
  all_goals exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

theorem validate_ct (M : Mont)  (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate M.mm pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact validate_ct_of M _ _ (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # What the stage's timing may depend on

Its arguments, the stack pointer, p, q and the h tape determine the
generator search's plan, and so everything the stage's timing depends on. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (GeneratorPlan GeneratorSearchPlan ValidatePublic PackPublic)

variable {pLen : Nat}

/-- The plan, and the separation of the domain check's workspace. -/
structure StagePublic where
  plan : GeneratorSearchPlan
  checkFrame : (⟨plan.core.F, frameBytes⟩ : Region).Disjoint ⟨off plan.core.B domainCheck, Impl.Dsa.Layout.usedBytes⟩
  checkHash : (⟨plan.core.S, oRsa⟩ : Region).Disjoint ⟨off plan.core.B domainCheck, Impl.Dsa.Layout.usedBytes⟩

theorem StagePublic.ext {a b : StagePublic} (h : a.plan = b.plan) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

def publicOf (hb : Supported pLen) {s : State} (A : StageABI pLen s) : StagePublic :=
  ⟨plan hb A, A.framePart hb (StageABI.domainCheck_room hb),
    A.parts hb (used_small hb (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide))
      (StageABI.domainCheck_room hb) (Or.inl (by decide))⟩

/-- The status the search leaves. -/
abbrev StagePublic.status (P : StagePublic) : BitVec 64 := statusOf P.plan

def StagePublic.pack (P : StagePublic) : PackPublic := ⟨P.plan.core.B, P.plan.core.F, P.plan.core.S⟩

/-- The domain check, with the domain the search finds. -/
def StagePublic.validate (hb : Supported pLen) (P : StagePublic) : ValidatePublic where
  input := ⟨off P.plan.core.B domainCheck, pLen, qLen pLen,
    Spec.Dsa.encodeParams pLen (qLen pLen) ⟨Spec.Dsa.decodeBE P.plan.core.pb, P.plan.q, gOf P.plan⟩, hb.lengths,
    VG.Proof.Dsa.Generation.encodeParams_length _ _ _⟩
  B := P.plan.core.B
  F := P.plan.core.F
  S := P.plan.core.S
  base := rfl
  frame := P.checkFrame
  hash := P.checkHash

theorem GeneratorPlan.ext' {a b : GeneratorPlan} (hB : a.B = b.B) (hA : a.A = b.A) (hF : a.F = b.F)
    (hS : a.S = b.S) (hp : a.hp = b.hp) (hZ : a.Z = b.Z) (hl : a.len = b.len) (hpb : a.pb = b.pb)
    (hhb : a.hb = b.hb) (heb : a.eb = b.eb) : a = b := by
  cases a; cases b
  simp only at hB hA hF hS hp hZ hl hpb hhb heb
  subst hB hA hF hS hp hZ hl hpb hhb heb
  rfl

theorem GeneratorSearchPlan.ext' {a b : GeneratorSearchPlan} (hc : a.core = b.core) (hs : a.saved = b.saved)
    (ht : a.tape = b.tape) (hp : a.tapePtr = b.tapePtr) (hq : a.q = b.q) : a = b := by
  cases a; cases b
  simp only at hc hs ht hp hq
  subst hc hs ht hp hq
  rfl

/-- What the contract makes public. -/
structure View where
  x0 : Addr
  x1 : Addr
  x2 : Addr
  x3 : Addr
  sp : Addr
  p : Nat
  q : Nat
  tape : List Byte

def view (pLen : Nat) (s : State) : View :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.sp, pOf pLen s.mem (s.gpr .x0), qOf pLen s.mem (s.gpr .x0), tape s⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem view_of_pub {s₁ s₂ : State} (h : (contract pLen).pub s₁ s₂) : view pLen s₁ = view pLen s₂ := by
  sig_pub [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := h
  obtain ⟨hp, hl⟩ := List.cons.inj hl
  obtain ⟨hq, hr⟩ := List.cons.inj hl
  have hr' := map_toNat_inj hr
  simp only [view, View.mk.injEq]
  exact ⟨h0, h1, h2, h3, hsp, hp, hq, hr'⟩

/-- p's bytes, from its value. -/
theorem pBytes_eq {s : State} : pBytes pLen s = Spec.Dsa.encodeBE pLen (pOf pLen s.mem (s.gpr .x0)) := by
  have := VG.Proof.Dsa.encodeBE_decodeBE (pBytes pLen s)
  rw [bytesAt_length] at this
  exact this.symm

theorem publicOf_eq (hb : Supported pLen) {s₁ s₂ : State} (A₁ : StageABI pLen s₁) (A₂ : StageABI pLen s₂)
    (hv : view pLen s₁ = view pLen s₂) : publicOf hb A₁ = publicOf hb A₂ := by
  simp only [view, View.mk.injEq] at hv
  obtain ⟨h0, -, h2, h3, hsp, hp, hq, ht⟩ := hv
  have he : ∀ {s : State} (A : StageABI pLen s), eBytes pLen s =
      Spec.Dsa.encodeBE pLen ((pOf pLen s.mem (s.gpr .x0) - 1) / qOf pLen s.mem (s.gpr .x0)) := fun A => A.exponent
  apply StagePublic.ext
  apply GeneratorSearchPlan.ext'
  · apply GeneratorPlan.ext'
    all_goals simp only [publicOf, plan, Arena.generatorPlan, arena]
    all_goals first
      | rw [h0]
      | rw [pBytes_eq, pBytes_eq, hp]
      | rw [he A₁, he A₂, hp, hq]
      | simp only [frameBase, hsp]
  · simp only [publicOf, plan, h0, h2, h3]
  · simp only [publicOf, plan]; exact ht
  · simp only [publicOf, plan, h2]
  · simp only [publicOf, plan, hq]

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generator.Body`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generator.Saves`, which this module and modules that import it used -/

section

/-! # The stage saves the callee-saved registers in the working space, and restores them

`str`/`ldr` of each register at its slot of the control area, the low halves
of v8–v15 through `x9` and `x10`. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Impl.Dsa.AArch64.Generator

/-- The slots of the vector registers' low halves, keyed by `x0`–`x7` as
`Spill`'s lists of registers are. -/
def vectorKeys : List (Reg × Nat) :=
  [(.x0, spill + 88), (.x1, spill + 96), (.x2, spill + 104), (.x3, spill + 112), (.x4, spill + 120),
   (.x5, spill + 128), (.x6, spill + 136), (.x7, spill + 144)]

/-- The low halves of v8–v15, keyed by `x0`–`x7`. -/
def laneValues (s : State) : Reg → BitVec 64
  | .x0 => laneOf s .v8 0 | .x1 => laneOf s .v9 0
  | .x2 => laneOf s .v10 0 | .x3 => laneOf s .v11 0
  | .x4 => laneOf s .v12 0 | .x5 => laneOf s .v13 0
  | .x6 => laneOf s .v14 0 | _ => laneOf s .v15 0

def savedMem (s : State) : Mem :=
  Spill.saveMem (Spill.saveMem s.mem (s.gpr .x0) s.gpr gprSlots) (s.gpr .x0) (laneValues s) vectorKeys

/-- The state after the saves. -/
def savedState (s : State) : State :=
  { s with gpr := fun r => if r = .x9 then laneOf s .v15 0 else s.gpr r, mem := savedMem s }

theorem save_ok {s : State}
    (hw : ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8) :
    WP isa (.block save) s (· = savedState s) := by
  simp only [save, gprSlots, vectorSlots, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, spill, VG.Impl.Dsa.Generation.Layout.control]
  have w (d : Nat) (h₁ : 27840 ≤ d) (h₂ : d + 8 ≤ 27992) := hw d (by unfold spill VG.Impl.Dsa.Generation.Layout.control; omega_using [h₁])
    (by unfold spill spillBytes VG.Impl.Dsa.Generation.Layout.control; omega_using [h₂])
  brun [exec_str_x (off := 27840) (by decide), exec_str_x (off := 27848) (by decide),
    exec_str_x (off := 27856) (by decide), exec_str_x (off := 27864) (by decide),
    exec_str_x (off := 27872) (by decide), exec_str_x (off := 27880) (by decide),
    exec_str_x (off := 27888) (by decide), exec_str_x (off := 27896) (by decide),
    exec_str_x (off := 27904) (by decide), exec_str_x (off := 27912) (by decide),
    exec_str_x (off := 27920) (by decide), exec_str_x (off := 27928) (by decide),
    exec_str_x (off := 27936) (by decide), exec_str_x (off := 27944) (by decide),
    exec_str_x (off := 27952) (by decide), exec_str_x (off := 27960) (by decide),
    exec_str_x (off := 27968) (by decide), exec_str_x (off := 27976) (by decide),
    exec_str_x (off := 27984) (by decide),
    w 27840 (by decide) (by decide), w 27848 (by decide) (by decide), w 27856 (by decide) (by decide),
    w 27864 (by decide) (by decide), w 27872 (by decide) (by decide), w 27880 (by decide) (by decide),
    w 27888 (by decide) (by decide), w 27896 (by decide) (by decide), w 27904 (by decide) (by decide),
    w 27912 (by decide) (by decide), w 27920 (by decide) (by decide), w 27928 (by decide) (by decide),
    w 27936 (by decide) (by decide), w 27944 (by decide) (by decide), w 27952 (by decide) (by decide),
    w 27960 (by decide) (by decide), w 27968 (by decide) (by decide), w 27976 (by decide) (by decide),
    w 27984 (by decide) (by decide),
    exec_umov (by decide : 0 < 2), savedMem, Spill.saveMem, gprSlots, vectorKeys, laneValues, savedState,
    laneOf, State.write, spill, VG.Impl.Dsa.Generation.Layout.control]
  congr 1
  funext r
  by_cases h : r = .x9 <;> simp only [h, ite_true, ite_false] <;> rfl

/-- What the restores leave. -/
structure Restored (s t u : State) : Prop where
  gprs : ∀ r ∈ preserved, u.gpr r = s.gpr r
  vectors : ∀ v ∈ preservedV, (u.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64
  memory : u.mem = t.mem
  stack : u.sp = t.sp
  read : u.rd = t.rd
  write : u.wr = t.wr
  result : u.gpr .x0 = t.gpr .x0

theorem restore_ok {s t : State} {B : Addr}
    (hB : t.mem.readW (t.sp + BitVec.ofNat 64 40) 64 = B)
    (r40 : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 40) 8)
    (read : ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 d) 8)
    (g : Spill.Saved B s.gpr gprSlots t.mem) (v : Spill.Saved B (laneValues s) vectorKeys t.mem) :
    WP isa (.block restore) t (Restored s t) := by
  simp only [restore, gprSlots, vectorSlots, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, spill, VG.Impl.Dsa.Generation.Layout.control]
  have r (d : Nat) (h₁ : 27840 ≤ d) (h₂ : d + 8 ≤ 27992) := read d (by unfold spill VG.Impl.Dsa.Generation.Layout.control; omega_using [h₁])
    (by unfold spill spillBytes VG.Impl.Dsa.Generation.Layout.control; omega_using [h₂])
  simp only [Spill.Saved, gprSlots, vectorKeys, spill, VG.Impl.Dsa.Generation.Layout.control, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Nat.reduceAdd] at g v
  obtain ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g30⟩ := g
  obtain ⟨v8, v9, v10, v11, v12, v13, v14, v15⟩ := v
  brun [exec_ldrSp (off := 40) (by decide),
    exec_ldr_x (off := 27840) (by decide), exec_ldr_x (off := 27848) (by decide),
    exec_ldr_x (off := 27856) (by decide), exec_ldr_x (off := 27864) (by decide),
    exec_ldr_x (off := 27872) (by decide), exec_ldr_x (off := 27880) (by decide),
    exec_ldr_x (off := 27888) (by decide), exec_ldr_x (off := 27896) (by decide),
    exec_ldr_x (off := 27904) (by decide), exec_ldr_x (off := 27912) (by decide),
    exec_ldr_x (off := 27920) (by decide), exec_ldr_x (off := 27928) (by decide),
    exec_ldr_x (off := 27936) (by decide), exec_ldr_x (off := 27944) (by decide),
    exec_ldr_x (off := 27952) (by decide), exec_ldr_x (off := 27960) (by decide),
    exec_ldr_x (off := 27968) (by decide), exec_ldr_x (off := 27976) (by decide),
    exec_ldr_x (off := 27984) (by decide),
    exec_ins (by decide : 0 < 2), hB, r40,
    r 27840 (by decide) (by decide), r 27848 (by decide) (by decide), r 27856 (by decide) (by decide),
    r 27864 (by decide) (by decide), r 27872 (by decide) (by decide), r 27880 (by decide) (by decide),
    r 27888 (by decide) (by decide), r 27896 (by decide) (by decide), r 27904 (by decide) (by decide),
    r 27912 (by decide) (by decide), r 27920 (by decide) (by decide), r 27928 (by decide) (by decide),
    r 27936 (by decide) (by decide), r 27944 (by decide) (by decide), r 27952 (by decide) (by decide),
    r 27960 (by decide) (by decide), r 27968 (by decide) (by decide), r 27976 (by decide) (by decide),
    r 27984 (by decide) (by decide),
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g30, v8, v9, v10, v11, v12, v13, v14, v15,
    laneValues, laneOf, State.write, State.setV]
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, ↓reduceIte]
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, ↓reduceIte, Nat.mul_zero]
    all_goals exact extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)

theorem saved_gprs (s : State) : Spill.Saved (s.gpr .x0) s.gpr gprSlots (savedState s).mem := by
  have g := Spill.saveMem_saved (l := gprSlots) (by decide) s.mem (s.gpr .x0) s.gpr
  have vf := Spill.saveMem_frame (l := vectorKeys) (lo := spill + 88) (n := 64) (by decide) (by decide)
    (Spill.saveMem s.mem (s.gpr .x0) s.gpr gprSlots) (s.gpr .x0) (laneValues s)
  exact g.frame_in (lo := spill) (n := 88) (by decide) vf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (s.gpr .x0) (by decide) (by decide) (by decide))

theorem saved_vectors (s : State) : Spill.Saved (s.gpr .x0) (laneValues s) vectorKeys (savedState s).mem :=
  Spill.saveMem_saved (l := vectorKeys) (by decide) _ (s.gpr .x0) (laneValues s)

theorem save_frame (s : State) :
    Frame [⟨s.gpr .x0 + BitVec.ofNat 64 spill, spillBytes⟩] s.mem (savedState s).mem := by
  have gp := Spill.saveMem_frame (l := gprSlots) (lo := spill) (n := spillBytes) (by decide) (by decide)
    s.mem (s.gpr .x0) s.gpr
  have vp := Spill.saveMem_frame (l := vectorKeys) (lo := spill) (n := spillBytes) (by decide) (by decide)
    (Spill.saveMem s.mem (s.gpr .x0) s.gpr gprSlots) (s.gpr .x0) (laneValues s)
  exact gp.trans vp

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! # The stage's body, between its frame's push and pop

The body saves the callee-saved registers in the working space's control
area, fills the frame words, runs the stage, returns its status as 1 or 0,
and restores the registers. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generator
open VG.Proof.Dsa.AArch64.Generation (allocState)
open VG.Proof.RsaOaep.AArch64 (Lay Rep)

/-- The body of the function, inside its frame. -/
abbrev body (mul : Nat → Nat → Nat → Prog isa) (pLen : Nat) : Prog isa :=
  Impl.Bignum.AArch64.seqs [.block save, .block entry, stage mul pLen, .block exit, .block restore]

variable {pLen : Nat} {s : State}

/-- The saved registers' region. -/
abbrev spillRegion (s : State) : Region := ⟨off (s.gpr .x0) spill, spillBytes⟩

/-- What the body leaves: the stage's status as 1 or 0, the packed domain,
the memory changed only in the stage's regions, the frame and the saved
registers' slots, and the callee-saved registers. -/
structure BodyPost (pLen : Nat) (s t : State) : Prop where
  status : t.gpr .x0 = BitVec.ofNat 64 (endCode pLen s + 4 * (pLen * readCount pLen s))
  packed : ∀ a, result pLen s = some a →
    Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a
  frame : Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem t.mem
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sp : t.sp = (allocState 272 s).sp
  wr : t.wr = (allocState 272 s).wr
  rd : t.rd = s.rd

theorem exit_ok {t : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t F S) (R : Rep t.mem F S V W) :
    WP isa (.block exit) t fun t' => t'.mem = t.mem ∧ t'.gpr .x0 = W 19 + (W 20 <<< 2) ∧
      Keep [.x0, .x3, .x4] t t' := by
  have hw : t.mem.readW (t.sp + BitVec.ofNat 64 152) 64 = W 19 := by rw [L.sp]; exact R.fr 19 (by decide)
  have hw' : t.mem.readW (t.sp + BitVec.ofNat 64 160) 64 = W 20 := by rw [L.sp]; exact R.fr 20 (by decide)
  have hl : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.ld (d := 152) (by decide)
  have hl' : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 160) 8 := by rw [L.sp]; exact L.ld (d := 160) (by decide)
  have run : WP isa (.block exit) t fun t' => t'.mem = t.mem ∧ t'.gpr .x0 = W 19 + (W 20 <<< 2) := by
    unfold exit
    brun [State.write, exec_ldrSp (off := 152) (by decide), exec_ldrSp (off := 160) (by decide),
      exec_lsl_x (by decide : 2 < 64), hw, hl, hw', hl']
  exact WP.mono (WP.keep [.x0, .x3, .x4] run (by decide)) fun t' ⟨⟨hm, hx⟩, k⟩ => ⟨hm, hx, k⟩

theorem savedState_gpr (s : State) {r : Reg} (h : r ≠ .x9) : (savedState s).gpr r = s.gpr r := by
  simp [savedState, h]

theorem StageABI.spill_in (hb : Supported pLen) (A : StageABI pLen s) :
    ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  intro d h₁ h₂
  have := spill_used hb
  have := A.size
  have := A.wsBound
  exact ⟨wsRegion s, by rw [A.wr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- The saves, from the frame's allocation. -/
theorem save_saved (hb : Supported pLen) (A : StageABI pLen s) :
    WP isa (.block save) (allocState 272 s) (· = savedState (allocState 272 s)) :=
  save_ok fun d h₁ h₂ => by
    obtain ⟨r, hr, hc⟩ := A.spill_in hb d h₁ h₂
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩

/-- The entry, from the saves' state, fills the frame words. -/
theorem entry_entered (s : State) :
    WP isa (.block entry) (savedState (allocState 272 s)) fun u => Entered pLen s u ∧
      Frame [⟨frameBase s, 272⟩] (savedState (allocState 272 s)).mem u.mem := by
  have hF : ∀ {d n : Nat}, d + n ≤ 272 → Region.Contains ⟨frameBase s, 272⟩ (off (frameBase s) d) n :=
    fun h => Offset.contains_base _ h (by omega_using [h])
  refine WP.mono (entry_ok (s := savedState (allocState 272 s)) (F := frameBase s) rfl
    (fun d hd => ⟨_, List.mem_cons_self, hF hd⟩)) fun u ⟨hmu, ku⟩ => ?_
  have g0 : (savedState (allocState 272 s)).gpr .x0 = s.gpr .x0 := savedState_gpr _ (by decide)
  have g2 : (savedState (allocState 272 s)).gpr .x2 = s.gpr .x2 := savedState_gpr _ (by decide)
  have g3 : (savedState (allocState 272 s)).gpr .x3 = s.gpr .x3 := savedState_gpr _ (by decide)
  have fl : Frame [spillRegion s] s.mem (savedState (allocState 272 s)).mem := save_frame (allocState 272 s)
  have fe : Frame [⟨frameBase s, 272⟩] (savedState (allocState 272 s)).mem u.mem := hmu ▸ entryMem_frame _ _
  refine ⟨{
    sp := ku.sp
    rd := ku.rd
    wr := ku.wr
    frame := (fl.mono (by simp)).trans (fe.mono (by simp))
    words := fun k hk => by rw [hmu, entryMem_word _ _ hk, g0, g2, g3] }, fe⟩

theorem body_ok (M : Mont) (hb : Supported pLen) (A : StageABI pLen s) :
    WP isa (body M.mm pLen) (allocState 272 s) (BodyPost pLen s) := by
  simp only [body, Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (save_saved hb A) fun l hl => ?_)
  subst hl
  refine WP.seq (WP.mono (entry_entered (pLen := pLen) s) fun u ⟨E, fe⟩ => ?_)
  refine WP.seq (WP.mono (stage_ok M hb A E) fun t T => ?_)
  obtain ⟨V, W, R, h5, h19, h20⟩ := T.rep
  refine WP.seq (WP.mono (exit_ok T.lay R) fun t' ⟨hm', hx, k'⟩ => ?_)
  -- The saved registers, which nothing but the saves wrote.
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have qn := hb.q_le
  have hs := spill_used hb
  have sep : ∀ r ∈ [(⟨frameBase s, 272⟩ : Region)] ++ stageChanged pLen s,
      Region.Disjoint ⟨s.gpr .x0 + BitVec.ofNat 64 spill, spillBytes⟩ r := by
    intro r hr
    simp only [stageChanged, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have c : spill = 27840 := rfl
    have c1 : packed = 27008 := rfl
    have c2 : g = 26240 := rfl
    have c5 : arithmetic = 28672 := rfl
    have c6 : domainCheck = 40960 := rfl
    have sp : ∀ {d n : Nat}, d + n ≤ usedBytes pLen → (d + n ≤ spill ∨ spill + spillBytes ≤ d) →
        Region.Disjoint ⟨s.gpr .x0 + BitVec.ofNat 64 spill, spillBytes⟩ ⟨off (s.gpr .x0) d, n⟩ := fun h h' =>
      A.parts hb hs h (h'.symm)
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))).sub_right (A.part_sub hs)).symm
    · exact sp (used_small hb (by decide) (by rfl)) (Or.inr (by decide))
    · have := sp (used_parent hb) (Or.inl (by decide)); simpa [off] using this
    · exact sp (used_small hb (by decide) (by unfold arithmeticBytes; omega_using [pn])) (Or.inl (by omega_using [pn, c, c2]))
    · exact sp (used_small hb (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])) (Or.inl (by omega_using [pn, qn, c, c1]))
    · exact sp (StageABI.domainCheck_room hb) (Or.inr (by decide))
    · exact ((A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega_using []))).sub_right (A.part_sub hs)).symm
  have fmid : Frame ([⟨frameBase s, 272⟩] ++ stageChanged pLen s) (savedState (allocState 272 s)).mem t'.mem := by
    rw [hm']
    exact (fe.mono (by simp)).trans (T.frame.mono (by intro r hr; simp [hr]))
  have saved_g := (saved_gprs (allocState 272 s)).frame_in (lo := spill) (n := spillBytes) (by decide) fmid sep
  have saved_v := (saved_vectors (allocState 272 s)).frame_in (lo := spill) (n := spillBytes) (by decide) fmid sep
  have sp' : t'.sp = frameBase s := k'.sp.trans T.lay.sp
  have wr' : t'.wr = (allocState 272 s).wr := k'.wr.trans (T.wr.trans E.wr)
  have hB : t'.mem.readW (t'.sp + BitVec.ofNat 64 40) 64 = s.gpr .x0 := by
    rw [sp', hm']; exact (R.fr 5 (by decide)).trans h5
  have r40 : InRegions (t'.rd ++ t'.wr) (t'.sp + BitVec.ofNat 64 40) 8 := by
    rw [k'.rd, k'.wr, sp']; exact T.lay.ld (d := 40) (by decide)
  have rd : ∀ d, spill ≤ d → d + 8 ≤ spill + spillBytes →
      InRegions (t'.rd ++ t'.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ => by
    obtain ⟨r, hr, hc⟩ := A.spill_in hb d h₁ h₂
    exact ⟨r, List.mem_append_right _ (by rw [wr']; exact List.mem_cons_of_mem _ hr), hc⟩
  refine WP.mono (restore_ok (s := allocState 272 s) hB r40 rd saved_g saved_v) fun t'' Rs => ?_
  refine ⟨?_, fun a ha => ?_, ?_, Rs.gprs, Rs.vectors, Rs.stack.trans sp', Rs.write.trans wr',
    Rs.read.trans (k'.rd.trans (T.rd.trans E.rd))⟩
  · rw [Rs.result, hx, h19, h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega_using []
  · rw [Rs.memory, hm']; exact T.packed a ha
  · rw [Rs.memory, hm']
    exact (E.frame.mono (by simp)).trans (T.frame.mono (by intro r hr; simp [hr]))

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! # The generator stage's timing depends only on its public inputs

Its arguments, the stack pointer, p, q and the h tape determine the stage's
public plan (`publicOf`), and each piece of the stage runs from states that
agree on it: the generation's own timing lemmas cover the search, the gate,
the packing and the domain check. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generator
open VG.Proof.Dsa.AArch64.Generation (allocState GeneratorSearchStart PackBefore
  ValidateBefore)
open VG.Proof.RsaOaep.AArch64 (Lay Rep)

variable {pLen : Nat}

def Start (hb : Supported pLen) (P : StagePublic) (u : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ u = allocState 272 s

def Linked (hb : Supported pLen) (P : StagePublic) (u : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ u = savedState (allocState 272 s)

def Ready (hb : Supported pLen) (P : StagePublic) (u : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ Entered pLen s u

def Srch (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, ∃ u, publicOf hb A = P ∧ Searched hb A u t

def PackMem (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ Lay t (frameBase s) (hashBase s) ∧
    (∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0) ∧ Scr t (s.gpr .x0) (usedBytes pLen)

def Pk (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, ∃ u, publicOf hb A = P ∧ Packed hb A u t

theorem save_ct (hb : Supported pLen) :
    RelCT isa (Two (Start hb)) (.block save) (Two (Linked hb)) :=
  two_piece [.x0] (by
      rintro P u₁ u₂ ⟨s₁, A₁, rfl, rfl⟩ ⟨s₂, A₂, h₂, rfl⟩ r hr
      obtain rfl := List.mem_singleton.mp hr
      have := congrArg (fun P => P.plan.core.B) h₂
      exact this.symm)
    (by taint_decide) fun P u ⟨s, A, hP, hu⟩ => by
    subst hu
    exact WP.mono (save_saved hb A) fun t ht => ⟨s, A, hP, ht⟩

theorem entry_ct (hb : Supported pLen) : RelCT isa (Two (Linked hb)) (.block entry) (Two (Ready hb)) :=
  two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun P u ⟨s, A, hP, hu⟩ => by
    subst hu
    exact WP.mono (entry_entered (pLen := pLen) s) fun t ⟨E, _⟩ => ⟨s, A, hP, E⟩

theorem search_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two (Ready hb)) (Impl.Dsa.AArch64.Generation.generatorSearch M.mm pLen) (Two (Srch hb)) :=
  two_post (two_map (fun P => P.plan) (fun P u ⟨s, A, hP, E⟩ => by
      subst hP; exact ⟨⟨_, prepared hb A E⟩, rfl⟩)
    (VG.Proof.Dsa.AArch64.Generation.nativeGenerator_ct M pLen hb))
    fun P u ⟨s, A, hP, E⟩ => WP.mono (search_ok M hb A E) fun t S => ⟨s, A, u, hP, S⟩

/-- Copying a part keeps the frame and the working space. -/
theorem packPart_stage (hb : Supported pLen) {s : State} (A : StageABI pLen s) {t : State}
    {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (frameBase s) (hashBase s)) (R : Rep t.mem (frameBase s) (hashBase s) V W)
    (h5 : W 5 = s.gpr .x0) (scr : Scr t (s.gpr .x0) (usedBytes pLen))
    (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384) :
    WP isa (Impl.Dsa.AArch64.Generation.packPart src dst len) t fun t' =>
      Lay t' (frameBase s) (hashBase s) ∧ Rep t'.mem (frameBase s) (hashBase s) V W ∧
        Scr t' (s.gpr .x0) (usedBytes pLen) := by
  have c1 : packed = 27008 := rfl
  have c6 : domainCheck = 40960 := rfl
  have c12 : usedBytes pLen = domainCheck + 128 * pLen := rfl
  have srcB := used_small hb (d := src) (n := len) (by omega_using [hsrc, c1, c6]) (by unfold arithmeticBytes; omega_using [hlen])
  have dstB := used_small hb (d := dst) (n := len) (by omega_using [hend, c1, c6]) (by unfold arithmeticBytes; omega_using [hlen])
  let bs := Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) src) len
  have bl : bs.length = len := bytesAt_length _ _ _
  have source : Src t (off (s.gpr .x0) dst) len (off (s.gpr .x0) src) bs := by
    apply VG.Proof.Dsa.AArch64.Generation.arena_source scr (by rw [bl]; exact srcB)
      (by rw [bl]; omega_using [hlen]) (by rw [bl])
    rw [bl]; exact A.parts hb srcB dstB (Or.inl (by omega_using [hsrc, hdst]))
  have hashSep : (⟨hashBase s, oRsa⟩ : Region).Disjoint ⟨off (s.gpr .x0) dst, len⟩ := by
    have hh := used_small hb (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
    have c8 : VG.Impl.Dsa.Generation.Layout.hash = 16384 := rfl
    have c9 : oRsa = 8192 := rfl
    exact A.parts hb hh dstB (Or.inl (by omega_using [hdst, c1, c8, c9]))
  have call := VG.Proof.Dsa.AArch64.Generation.packPart_ok (src := src) (dst := dst) (bs := bs) L R
    (by omega_using [hsrc, c1]) (by omega_using [hend, c1]) (by rw [bl]; omega_using [hlen])
  rw [h5] at call
  have run := call source.rd (fun i hi => by
    rw [off_off]; exact scr.region (by rw [bl] at hi; omega_using [dstB, hi]) (by decide))
    (fun i hi => by simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using source.val i hi)
    (fun i hi j hj heq => by
      have outside := source.out i hi
      change len ≤ ofs (off (s.gpr .x0) dst) (off (off (s.gpr .x0) src) i) at outside
      rw [heq] at outside
      rw [bl] at hj
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [hlen, hj] : j < 2 ^ 64)] at outside
      omega_using [h5, hsrc, hdst, hend, hlen, c1, c6, c12, srcB, dstB, bl, hi, hj, outside])
    (by rw [bl]; exact A.framePart hb dstB) (by rw [bl]; exact hashSep)
  rw [bl] at run
  exact WP.mono run fun t' ⟨_, Lt, Rt, _, kt⟩ => ⟨Lt, Rt, scr.congr kt.wr⟩

theorem packPart_mem_ct (hb : Supported pLen) (src dst len : Nat) (hsrc : src + len ≤ packed) (hdst : packed ≤ dst)
    (hend : dst + len ≤ packed + 800) (hlen : 2 ≤ len ∧ len ≤ 384)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two (PackMem hb)) (Impl.Dsa.AArch64.Generation.packPart src dst len) (Two (PackMem hb)) := by
  refine two_post (two_map StagePublic.pack (fun P t ⟨s, A, hP, L, ⟨V, W, R, h5⟩, _⟩ => by
      subst hP; exact ⟨L, V, W, R, h5⟩)
    (VG.Proof.Dsa.AArch64.Generation.packPart_ct src dst len (by unfold packed at *; omega_using [hsrc])
      (by unfold packed at *; omega_using [hend]) (by omega_using [hlen]) ht)) ?_
  intro P t ⟨s, A, hP, L, ⟨V, W, R, h5⟩, scr⟩
  exact WP.mono (packPart_stage hb A L R h5 scr src dst len hsrc hdst hend hlen)
    fun t' ⟨L', R', scr'⟩ => ⟨s, A, hP, L', ⟨V, W, R', h5⟩, scr'⟩

theorem pack_mem_ct (hb : Supported pLen) :
    RelCT isa (Two (PackMem hb)) (Impl.Dsa.AArch64.Generation.pack pLen (qLen pLen)) fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.pack
  simp only [Impl.Bignum.AArch64.seqs]
  have last : ∀ {c : Prog isa}, RelCT isa (Two (PackMem hb)) c (Two (PackMem hb)) →
      RelCT isa (Two (PackMem hb)) c fun _ _ => True := fun h => h.mono (fun _ _ h => h) fun _ _ _ => True.intro
  rcases hb with rfl | rfl | rfl
  all_goals
    exact RelCT.seq (packPart_mem_ct _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
      (RelCT.seq (packPart_mem_ct _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))
        (last (packPart_mem_ct _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by taint_decide))))

theorem Supported.sizes {pLen : Nat} (hb : Supported pLen) :
    (pLen = 128 ∧ qLen pLen = 20) ∨ (pLen = 256 ∧ qLen pLen = 32) ∨ (pLen = 384 ∧ qLen pLen = 32) := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem finish_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two fun P t => Srch hb P t ∧ P.status = 1)
      (Impl.Dsa.AArch64.Generation.finishDomain M.mm pLen (qLen pLen)) fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generation.finishDomain
  refine RelCT.seq (two_post (Ψ := Pk hb) (two_map (fun P => P) (fun P t ⟨⟨s, A, u, hP, S⟩, _⟩ => by
      obtain ⟨V, W, R, h5, _⟩ := S.rep
      exact ⟨s, A, hP, S.lay, ⟨V, W, R, h5⟩, S.scr⟩) (pack_mem_ct hb))
    fun P t ⟨⟨s, A, u, hP, S⟩, h1⟩ => by
      subst hP
      exact WP.mono (pack_stage_ok hb A S h1) fun t' Pd => ⟨s, A, u, rfl, Pd⟩) ?_
  refine two_map (StagePublic.validate hb) (fun P t ⟨s, A, u, hP, Pd⟩ => ?_)
    (VG.Proof.Dsa.AArch64.Generation.validate_ct M pLen (qLen pLen) hb.sizes)
  subst hP
  obtain ⟨V, W, R, h5, _⟩ := Pd.rep
  exact ⟨Pd.lay, ⟨V, W, R, h5⟩, Pd.check_scr, Pd.check_src, rfl, rfl⟩

theorem stage_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two (Ready hb)) (Impl.Dsa.AArch64.Generator.stage M.mm pLen) fun _ _ => True := by
  unfold Impl.Dsa.AArch64.Generator.stage
  refine RelCT.seq (search_ct M hb) (VG.Proof.Dsa.AArch64.Generation.onSuccess_ct_of StagePublic.status
    (fun P t ⟨s, A, u, hP, S⟩ => ?_) (fun P t t' ⟨s, A, u, hP, S⟩ hm hk => ⟨s, A, u, hP, S.congr hm hk⟩)
    (finish_ct M hb))
  subst hP
  obtain ⟨V, W, R, _, h19, _⟩ := S.rep
  exact ⟨_, _, V, W, S.lay, R, h19⟩

def Done (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, ∃ u, publicOf hb A = P ∧ Staged pLen s u t

def Exited (hb : Supported pLen) (P : StagePublic) (t : State) : Prop :=
  ∃ s, ∃ A : StageABI pLen s, publicOf hb A = P ∧ Lay t (frameBase s) (hashBase s) ∧
    ∃ V W, Rep t.mem (frameBase s) (hashBase s) V W ∧ W 5 = s.gpr .x0

def Based (P : StagePublic) (t : State) : Prop := t.gpr .x9 = P.plan.core.B

theorem staged_ct (M : Mont) (hb : Supported pLen) :
    RelCT isa (Two (Ready hb)) (Impl.Dsa.AArch64.Generator.stage M.mm pLen) (Two (Done hb)) :=
  two_post (stage_ct M hb) fun _ u ⟨s, A, hP, E⟩ => WP.mono (stage_ok M hb A E) fun _ T => ⟨s, A, u, hP, T⟩

theorem exit_ct (hb : Supported pLen) : RelCT isa (Two (Done hb)) (.block exit) (Two (Exited hb)) :=
  two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun P t ⟨s, A, u, hP, T⟩ => by
    obtain ⟨V, W, R, h5, _⟩ := T.rep
    exact WP.mono (exit_ok T.lay R) fun t' ⟨hm, _, k⟩ =>
      ⟨s, A, hP, T.lay.congr k.sp k.wr (by rw [hm]), V, W, hm ▸ R, h5⟩

theorem restore_ct (hb : Supported pLen) : RelCT isa (Two (Exited hb)) (.block restore) fun _ _ => True := by
  have base : RelCT isa (Two (Exited hb)) (.block [.ldrSp .x9 40]) (Two Based) :=
    two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun P t ⟨s, A, hP, L, V, W, R, h5⟩ => by
      subst hP
      have hw : t.mem.readW (t.sp + BitVec.ofNat 64 40) 64 = s.gpr .x0 := by
        rw [L.sp]; exact (R.fr 5 (by decide)).trans h5
      have hl : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 40) 8 := by rw [L.sp]; exact L.ld (d := 40) (by decide)
      brun [State.write, exec_ldrSp (off := 40) (by decide), hw, hl]
      rfl
  unfold restore
  rw [List.append_assoc]
  refine RelCT.block_append (RelCT.seq base ?_)
  exact two_taint [.x9] (fun P t₁ t₂ h₁ h₂ r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact h₁.trans h₂.symm) (by taint_decide)

theorem code_ct (M : Mont) (hb : Supported pLen) :
    ConstantTime isa (contract pLen).pre (contract pLen).pub (code M.mm pLen) := by
  intro s t xs ys u v hs ht hp es et
  have ct : RelCT isa (fun s t => (contract pLen).pre s ∧ (contract pLen).pre t ∧ (contract pLen).pub s t)
      (code M.mm pLen) (fun _ _ => True) := by
    apply RelCT.alloc
    refine RelCT.mono (RelCT.seq (save_ct hb) (RelCT.seq (entry_ct hb) (RelCT.seq (staged_ct M hb)
      (RelCT.seq (exit_ct hb) (restore_ct hb))))) ?_ fun _ _ _ => True.intro
    rintro a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
    have hv := view_of_pub hp
    have A₁ := stageABI_of h₁
    have A₂ := stageABI_of h₂
    refine ⟨publicOf hb A₁, ⟨s₁, A₁, rfl, rfl⟩, ⟨s₂, A₂, (publicOf_eq hb A₁ A₂ hv).symm, rfl⟩, ?_⟩
    simp only [view, View.mk.injEq] at hv
    change s₁.sp - _ = s₂.sp - _
    rw [hv.2.2.2.2.1]
  exact (ct _ _ _ _ _ _ ⟨hs, ht, hp⟩ es et).1

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generator.Correct`, which only this module used -/

section

/-! # The generator stage meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (allocState freeState alloc_frame_ok)

variable {pLen : Nat}

/-- No byte of `ws` but those of the stage's scratch ranges is in a region the stage changes. -/
theorem keeps_of_frame (hb : Supported pLen) {s : State} (A : StageABI pLen s) {m : Mem}
    (hf : Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .x0) (s.gpr .x1).toNat (Impl.Dsa.AArch64.Generator.layout pLen).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have qn := hb.q_le
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have hc : (wsRegion s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hw])
  have part : ∀ {e k : Nat}, (e, k) ∈ (Impl.Dsa.AArch64.Generator.layout pLen).scratch →
      e + k ≤ 2 ^ 64 → ¬ (⟨off (s.gpr .x0) e, k⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := by
    intro e k he hek hx
    have h := hout (e, k) he
    have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := e) (k := k) (by simp only at h; omega_using [h]) (by omega_using [hi, hw]) hek
    exact hd _ (Region.contains_self _ _) hx
  apply hf
  intro r hr hx
  simp only [stageChanged, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx
  · exact part (e := 0) (k := Impl.Dsa.Layout.activeBytes) (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch, parent])
      (by decide) (by simpa [off] using hx)
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by unfold g; omega_using [pn]) hx
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by unfold packed; omega_using [qn, pn]) hx
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx
  · exact (A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega_using []))) _ hx hc
  · exact (A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))) _ hx hc
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx

theorem correct (M : Mont) (hb : Supported pLen) (s : State) (pre : (contract pLen).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.AArch64.Generator.code M.mm pLen) s trace t ∧ abiPreserved s t ∧
      (contract pLen).post s t := by
  have A := stageABI_of pre
  obtain ⟨trace, t, he, hpre, hst, hpk, hf⟩ := alloc_frame_ok (bytes := 272) (by decide)
    (by have := A.stackLower; unfold stack at this; omega_using [this])
    (Q := fun t => abiPreserved s t ∧
      t.gpr .x0 = BitVec.ofNat 64 (endCode pLen s + 4 * (pLen * readCount pLen s)) ∧
      (∀ a, result pLen s = some a →
        Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a) ∧
      Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem t.mem)
    (WP.mono (body_ok M hb A) fun t P m u f => ⟨⟨P.regs, by
        change t.sp + BitVec.ofNat 64 272 = s.sp
        rw [P.sp]; exact BitVec.sub_add_cancel .., P.vectors⟩, P.status, fun a ha =>
        -- The frame's bytes are lost; the packed parameters are apart from them.
        (List.map_congr_left fun i hi => lost_byte f
          (A.framePart hb (used_small hb (by decide) (by
            have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
            have qn := hb.q_le
            unfold arithmeticBytes; omega_using [pn, qn]))).symm (List.mem_range.mp hi)).trans (P.packed a ha),
      P.frame.trans (f.sub fun R hR => ⟨⟨frameBase s, 272⟩,
        List.mem_append_right _ List.mem_cons_self, by obtain rfl := List.mem_singleton.mp hR; exact fun _ h => h⟩)⟩)
  refine ⟨trace, t, he, hpre, ?_⟩
  sig_post [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
  exact ⟨hst, keeps_of_frame hb A hf, fun a ha => hpk a ha⟩

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generator.Satisfiable`, which only this module used -/

section

/-! # A state meets the generator stage's precondition

p = 2^(8 * pLen) − 1 (all ones), q = 1 and the exponent p − 1 at their
offsets of a working space of the generation's size, and an empty h tape. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Impl.Dsa.Generation.Layout

def satBase : Addr := 0x100000

/-- The byte at offset `o` of the working space. -/
def satByte (pLen o : Nat) : Byte :=
  if p ≤ o ∧ o < p + pLen then 0xFF
  else if exponent ≤ o ∧ o < exponent + pLen then (if o + 1 = exponent + pLen then 0xFE else 0xFF)
  else if o + 1 = q + Impl.Dsa.AArch64.Generator.qLen pLen then 1 else 0

def satMemory (pLen : Nat) : Mem := fun a => satByte pLen (a - satBase).toNat

def satState (pLen : Nat) : State where
  gpr r := match r with
    | .x0 => satBase | .x1 => BitVec.ofNat 64 (usedBytes pLen / 8) | .x2 => 0x200000 | .x3 => 0
    | _ => 0
  sp := 0x400000
  mem := satMemory pLen
  rd := [⟨0x200000, 0⟩]
  wr := [⟨satBase, usedBytes pLen / 8 * 8⟩]

theorem sat_p {pLen : Nat} (hb : Supported pLen) : pOf pLen (satMemory pLen) satBase = 2 ^ (8 * pLen) - 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_odd {pLen : Nat} (hb : Supported pLen) : pOf pLen (satMemory pLen) satBase % 2 = 1 := by
  rw [sat_p hb]
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_bits {pLen : Nat} (hb : Supported pLen) :
    Spec.Dsa.bitLength (pOf pLen (satMemory pLen) satBase) = 8 * pLen := by
  rw [sat_p hb]
  have low : 1 ≤ 8 * pLen := by rcases hb with rfl | rfl | rfl <;> decide
  have half : 2 ^ (8 * pLen) = 2 ^ (8 * pLen - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega_using [low]
  have pos := Nat.two_pow_pos (8 * pLen - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [low])).mpr ⟨by omega_using [half], by omega_using [half, pos]⟩

theorem sat_q {pLen : Nat} (hb : Supported pLen) : qOf pLen (satMemory pLen) satBase = 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_exponent {pLen : Nat} (hb : Supported pLen) :
    Spec.Rsa.bytesAt (satMemory pLen) (satBase + BitVec.ofNat 64 exponent) pLen =
      Spec.Dsa.encodeBE pLen ((pOf pLen (satMemory pLen) satBase - 1) / qOf pLen (satMemory pLen) satBase) := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem satisfiable {pLen : Nat} (hb : Supported pLen) : ∃ s, (contract pLen).pre s := by
  refine ⟨satState pLen, ?_⟩
  sig_pre [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd hb
    | exact sat_bits hb
    | exact sat_exponent hb
    | (rw [sat_q hb]; decide)
    | (rcases hb with rfl | rfl | rfl <;> decide +kernel)
    | (rcases hb with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide +kernel))

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generator.Depth`, which only this module used -/

section

/-! # The generator stage's frames: its own 272 bytes

The stage itself has no frames (its arithmetic has none), so its stack is
its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem stage_noFrames (v : RoundImpl) (pLen : Nat) :
    (Impl.Dsa.AArch64.Generator.stage v.mont.mm pLen).noFrames = true := by
  simp only [Impl.Dsa.AArch64.Generator.stage, generatorSearch, tapeLoop, tapeIteration, generatorStep, generatorRangeFromFrame, generatorEvaluate, onSuccess, finishDomain, pack, packPart, validate, Code.noFrames, Impl.Bignum.AArch64.seqs, workspace, generatorRange, generatorResult, generatorPowerFresh, generatorModulus, generatorPower, generatorLoadPair, Impl.Dsa.AArch64.Random.copyRest, Impl.Dsa.AArch64.Generate.checkParameters, Impl.Dsa.AArch64.Core.publicPow, Impl.Dsa.AArch64.Checks.signingKey, Impl.Dsa.AArch64.Checks.publicPrefix, Impl.Dsa.AArch64.PublicPower.power, Impl.Dsa.AArch64.Core.reduce, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Dsa.AArch64.PublicPower.powerCore, Impl.Dsa.AArch64.Arithmetic.load, Impl.Dsa.AArch64.Core.finish, Impl.Rsa.AArch64.r2Steps, Impl.Dsa.AArch64.Arithmetic.encodePower, Impl.Dsa.AArch64.PublicPower.encodedPower, Impl.Dsa.AArch64.Arithmetic.reduce, Impl.Bignum.AArch64.R2Div.choice, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Dsa.AArch64.PublicPower.expLoop, Impl.Dsa.AArch64.Arithmetic.reduceSetup, Impl.Dsa.AArch64.Arithmetic.reduceByte, Impl.Rsa.AArch64.Crt.tabBuild, Impl.Rsa.AArch64.Crt.toEnt, Impl.Rsa.AArch64.Crt.copyArr, Impl.Rsa.AArch64.Crt.nextEnt, Impl.Dsa.AArch64.PublicPower.window, Impl.Dsa.AArch64.PublicPower.applyWindow, Impl.Dsa.AArch64.Arithmetic.reduceStep, List.append_assoc, v.mmNoFrames, Bool.and_eq_true, List.cons_append, List.nil_append]
  and_intros
  all_goals decide +kernel

/-- The stage never touches PSTATE.DIT: neither its own code (decided for each
size, `Generator.Supported`) nor its arithmetic. -/
theorem stage_noDit (v : RoundImpl) {pLen : Nat} (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    (Impl.Dsa.AArch64.Generator.stage v.mont.mm pLen).all (fun i => !i.touchesDit) = true := by
  rcases hp with rfl | rfl | rfl <;>
  simp only [Impl.Dsa.AArch64.Generator.stage, generatorSearch, tapeLoop, tapeIteration, generatorStep, generatorRangeFromFrame, generatorEvaluate, onSuccess, finishDomain, pack, packPart, validate, Code.all, Impl.Bignum.AArch64.seqs, workspace, generatorRange, generatorResult, generatorPowerFresh, generatorModulus, generatorPower, generatorLoadPair, Impl.Dsa.AArch64.Random.copyRest, Impl.Dsa.AArch64.Generate.checkParameters, Impl.Dsa.AArch64.Core.publicPow, Impl.Dsa.AArch64.Checks.signingKey, Impl.Dsa.AArch64.Checks.publicPrefix, Impl.Dsa.AArch64.PublicPower.power, Impl.Dsa.AArch64.Core.reduce, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Dsa.AArch64.PublicPower.powerCore, Impl.Dsa.AArch64.Arithmetic.load, Impl.Dsa.AArch64.Core.finish, Impl.Rsa.AArch64.r2Steps, Impl.Dsa.AArch64.Arithmetic.encodePower, Impl.Dsa.AArch64.PublicPower.encodedPower, Impl.Dsa.AArch64.Arithmetic.reduce, Impl.Bignum.AArch64.R2Div.choice, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Dsa.AArch64.PublicPower.expLoop, Impl.Dsa.AArch64.Arithmetic.reduceSetup, Impl.Dsa.AArch64.Arithmetic.reduceByte, Impl.Rsa.AArch64.Crt.tabBuild, Impl.Rsa.AArch64.Crt.toEnt, Impl.Rsa.AArch64.Crt.copyArr, Impl.Rsa.AArch64.Crt.nextEnt, Impl.Dsa.AArch64.PublicPower.window, Impl.Dsa.AArch64.PublicPower.applyWindow, Impl.Dsa.AArch64.Arithmetic.reduceStep, List.append_assoc, v.mmNoDit, Bool.and_eq_true, List.cons_append, List.nil_append] <;>
  and_intros <;>
  lit_decide

/-- As `stage_noDit`, for writes of PSTATE.DIT and indirect calls
(`Scrub.sideAll`). -/
theorem stage_side (v : RoundImpl) {pLen : Nat} (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.Dsa.AArch64.Generator.stage v.mont.mm pLen) = true := by
  rcases hp with rfl | rfl | rfl <;>
  simp only [Impl.Dsa.AArch64.Generator.stage, generatorSearch, tapeLoop, tapeIteration, generatorStep, generatorRangeFromFrame, generatorEvaluate, onSuccess, finishDomain, pack, packPart, validate, Scrub.sideAll, Impl.Bignum.AArch64.seqs, workspace, generatorRange, generatorResult, generatorPowerFresh, generatorModulus, generatorPower, generatorLoadPair, Impl.Dsa.AArch64.Random.copyRest, Impl.Dsa.AArch64.Generate.checkParameters, Impl.Dsa.AArch64.Core.publicPow, Impl.Dsa.AArch64.Checks.signingKey, Impl.Dsa.AArch64.Checks.publicPrefix, Impl.Dsa.AArch64.PublicPower.power, Impl.Dsa.AArch64.Core.reduce, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Dsa.AArch64.PublicPower.powerCore, Impl.Dsa.AArch64.Arithmetic.load, Impl.Dsa.AArch64.Core.finish, Impl.Rsa.AArch64.r2Steps, Impl.Dsa.AArch64.Arithmetic.encodePower, Impl.Dsa.AArch64.PublicPower.encodedPower, Impl.Dsa.AArch64.Arithmetic.reduce, Impl.Bignum.AArch64.R2Div.choice, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Dsa.AArch64.PublicPower.expLoop, Impl.Dsa.AArch64.Arithmetic.reduceSetup, Impl.Dsa.AArch64.Arithmetic.reduceByte, Impl.Rsa.AArch64.Crt.tabBuild, Impl.Rsa.AArch64.Crt.toEnt, Impl.Rsa.AArch64.Crt.copyArr, Impl.Rsa.AArch64.Crt.nextEnt, Impl.Dsa.AArch64.PublicPower.window, Impl.Dsa.AArch64.PublicPower.applyWindow, Impl.Dsa.AArch64.Arithmetic.reduceStep, List.append_assoc, v.mmSide, Bool.and_eq_true, List.cons_append, List.nil_append] <;>
  and_intros <;>
  lit_decide

/-- The stage's frames: its own 272 bytes. -/
theorem code_depth (v : RoundImpl) (pLen : Nat) :
    16 * (Impl.Dsa.AArch64.Generator.code v.mont.mm pLen).aarch64Depth ≤ 272 := by
  have h := ProbablePrime.aarch64Depth_of_noFrames _ (stage_noFrames v pLen)
  simp only [Impl.Dsa.AArch64.Generator.code, Impl.Bignum.AArch64.seqs, Code.aarch64Depth, h,
    AArch64.Instr.frameUnits]
  decide

/-- No instruction of the stage as called writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem code_side (v : RoundImpl) {pLen : Nat} (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    Scrub.sideAll (fun i => !i.writesDit) (Impl.Dsa.AArch64.Generator.code v.mont.mm pLen) = true := by
  have h := stage_side v hp
  simp only [Impl.Dsa.AArch64.Generator.code, Impl.Bignum.AArch64.seqs, Scrub.sideAll, h]
  rfl

end VG.Proof.Dsa.AArch64.Generator

end

end


/-! # `vg_dsa_generator_{bits}` on AArch64 is verified

For each Miller–Rabin round implementation, whose Montgomery multiplication
the stage's arithmetic inlines. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The stage's code with the round implementation `v`'s arithmetic. -/
abbrev stageCode (v : RoundImpl) (pLen : Nat) : Prog isa :=
  Impl.Dsa.AArch64.Generator.code v.mont.mm pLen

theorem verified (v : RoundImpl) {pLen : Nat} (hb : Supported pLen) :
    Verified target (stageCode v pLen) (contract pLen) :=
  ⟨correct v.mont hb, code_ct v.mont hb, satisfiable hb⟩

/-- The stages with the round implementation `v`, as parameter generation
calls them. -/
def generatorStage (v : RoundImpl) : VG.Proof.Dsa.AArch64.Generation.GeneratorStage where
  name pLen := s!"vg_dsa_generator_{8 * (Impl.Dsa.AArch64.Generator.layout pLen).pLen}" ++ v.suffix
  code := stageCode v
  verified _ hb := verified v hb
  depth := code_depth v
  noDit _ hb := by
    have h := stage_noDit v hb
    simp only [stageCode, Impl.Dsa.AArch64.Generator.code, Impl.Bignum.AArch64.seqs, Code.all, h]
    rfl

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.ProbablePrime.Verified`, which only this module used -/

section

/-! ### `Dsa.AArch64.ProbablePrime.Correct`, which only this module used -/

section

/-! # The probable-prime test meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (allocState freeState alloc_frame_ok)

/-- No byte of `ws` but those of the test's scratch ranges is in a region the test changes. -/
theorem keeps_of_frame {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {m : Mem}
    (hf : Frame (changed bits s) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .x0) (s.gpr .x1).toNat (layout bits).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := hout (witness, len bits) (by simp [layout])
  have h2 := hout (arithmetic, arithmeticBytes) (by simp [layout])
  have hc : (wsRegion s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hw])
  apply hf
  intro r hr hx
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := arithmetic) (k := arithmeticBytes)
      (by simp only at h2; omega_using [h2]) (by omega_using [hi, hw]) (by have : arithmetic + arithmeticBytes ≤ 2 ^ 64 := (by decide); omega_using [this])
    exact hd _ (Region.contains_self _ _) hx
  · have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := witness) (k := len bits)
      (by simp only at h1; omega_using [h1]) (by omega_using [hi, hw])
      (by have : witness + 384 ≤ 2 ^ 64 := (by decide); have := hlen; omega_arith)
    exact hd _ (Region.contains_self _ _) hx
  · exact (A.stackWs.sub_left (frame_sub s)) _ hx hc
  · exact A.wsUsed _ hc hx

theorem correct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {bits : Nat} (hb : Supported bits) (s : State)
    (pre : (contract bits).pre s) :
    ∃ trace t, Exec isa (code bits M.mm K.run) s trace t ∧ abiPreserved s t ∧ (contract bits).post s t := by
  have A := primeABI_of pre
  obtain ⟨trace, t, he, hpre, hpost⟩ := alloc_frame_ok (bytes := 272) (by decide) A.stackLower
    (Q := fun t => abiPreserved s t ∧ BodyPost bits s t)
    (WP.mono (body_ok M K hb A) fun t ⟨hsp, _, _, hp⟩ m u f => ⟨⟨hp.2.2.2.1, by
        change t.sp + BitVec.ofNat 64 272 = s.sp
        rw [hsp]; exact BitVec.sub_add_cancel .., hp.2.2.2.2⟩, by
      -- The frame's bytes are lost; `used` is apart from them.
      unfold BodyPost at hp ⊢
      refine ⟨hp.1, fun b rest hr => ?_, hp.2.2.1.trans (f.sub fun R hR => ⟨⟨frameBase s, 272⟩, by simp [changed],
        by obtain rfl := List.mem_singleton.mp hR; exact fun _ h => h⟩), hp.2.2.2.1, hp.2.2.2.2⟩
      exact (f.readW (r := ⟨s.gpr .x4, 8⟩) (Region.contains_self _ _)
        (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact A.stackUsed.symm.sub_right (frame_sub s))
        (by decide)).trans (hp.2.1 b rest hr)⟩)
  obtain ⟨hx0, hused, hframe, _, _⟩ := hpost
  refine ⟨trace, t, he, hpre, ?_⟩
  sig_post [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  refine ⟨?_, keeps_of_frame hb A hframe, fun b rest h => ?_⟩
  · rw [hx0]
    have st : ∀ o : Option (Bool × Spec.RsaKeyGen.Rand),
        (BitVec.setWidth 32 (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status o))).toNat =
          Proof.Dsa.ProbablePrime.status o := by
      intro o
      rcases o with _ | ⟨_ | _, _⟩ <;> rfl
    exact st _
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    rw [show s.gpr .x4 + BitVec.ofNat 64 0 = s.gpr .x4 from BitVec.add_zero _, hused b rest h]

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.ProbablePrime.Satisfiable`, which only this module used -/

section

/-! # A state meets the probable-prime test's precondition

An all-ones candidate of `bits` bits at its offset of a working space of 5120
words, and an empty tape. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Impl.Dsa.AArch64.ProbablePrime

def satBase : Addr := 0x100000

def satMemory (bits : Nat) : Mem := fun a =>
  if (a - (satBase + BitVec.ofNat 64 (candidate bits))).toNat < bits / 8 then 0xFF#8 else 0

def satState (bits : Nat) : State where
  gpr r := match r with
    | .x0 => 0x100000 | .x1 => 5120 | .x2 => 0x200000 | .x3 => 0
    | .x4 => 0x300000 | _ => 0
  sp := 0x400000
  mem := satMemory bits
  rd := [⟨0x200000, 0⟩]
  wr := [⟨0x100000, 40960⟩, ⟨0x300000, 8⟩]

theorem foldl_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, foldl_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    have pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega_using [pos]⟩
    grind

theorem sat_candidate {bits : Nat} (hb : Supported bits) :
    candidateOf bits (satState bits) = 2 ^ bits - 1 := by
  have hl : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bytes : Spec.Rsa.bytesAt (satMemory bits) (satBase + BitVec.ofNat 64 (candidate bits)) (bits / 8) =
      List.replicate (bits / 8) 0xFF#8 := by
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl, hi])]
    exact ite_eq_left hi
  change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (satMemory bits) (satBase + BitVec.ofNat 64 (candidate bits))
    (bits / 8)) = _
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [foldl_ones, Nat.zero_mul, Nat.zero_add]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide]

theorem sat_odd {bits : Nat} (hb : Supported bits) : candidateOf bits (satState bits) % 2 = 1 := by
  rw [sat_candidate hb]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide, Nat.pow_succ]; omega_using []
  have := Nat.two_pow_pos bits
  omega_arith

theorem sat_length {bits : Nat} (hb : Supported bits) :
    Spec.Dsa.bitLength (candidateOf bits (satState bits)) = bits := by
  rw [sat_candidate hb]
  have low : 1 ≤ bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega_using [low]
  have pos := Nat.two_pow_pos (bits - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [low])).mpr ⟨by omega_using [half], by omega_using [half, pos]⟩

theorem satisfiable {bits : Nat} (hb : Supported bits) : ∃ s, (contract bits).pre s := by
  refine ⟨satState bits, ?_⟩
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd hb
    | exact sat_length hb
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end


/-! # `vg_dsa_probable_prime_{bits}` on AArch64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) (bits : Nat) : Prog isa :=
  Impl.Dsa.AArch64.ProbablePrime.code bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run

theorem verified (v : RoundImpl) {bits : Nat} (hb : Supported bits) :
    Verified target (testCode v bits) (contract bits) :=
  ⟨correct v.mont (VG.Proof.Dsa.AArch64.Generation.publicKernel v) hb, code_ct v.mont (VG.Proof.Dsa.AArch64.Generation.publicKernel v) hb, satisfiable hb⟩

/-- Its frames: its own 272 bytes. -/
theorem testCode_depth (v : RoundImpl) (bits : Nat) : 16 * (testCode v bits).aarch64Depth ≤ stack := by
  have h := aarch64Depth_of_noFrames _ (test_noFrames v bits)
  simp only [testCode, Impl.Dsa.AArch64.ProbablePrime.code, Impl.Bignum.AArch64.seqs, Code.aarch64Depth, h,
    AArch64.Instr.frameUnits]
  decide

/-- No instruction of the test as called writes PSTATE.DIT, and it calls
nothing indirectly. -/
theorem testCode_side (v : RoundImpl) {bits : Nat} (hb : Supported bits) :
    Scrub.sideAll (fun i => !i.writesDit) (testCode v bits) = true := by
  have h := test_side v hb
  simp only [testCode, Impl.Dsa.AArch64.ProbablePrime.code, Impl.Bignum.AArch64.seqs, Scrub.sideAll, h]
  rfl

/-- The tests with the round implementation `v`, as parameter generation
calls them. -/
def primeTest (v : RoundImpl) : VG.Proof.Dsa.AArch64.Generation.PrimeTest where
  name bits := s!"vg_dsa_probable_prime_{(Impl.Dsa.AArch64.ProbablePrime.layout bits).bits}" ++ v.suffix
  code := testCode v
  verified _ hb := verified v hb
  depth := testCode_depth v
  noDit _ hb := by
    have h := test_noDit v hb
    simp only [testCode, Impl.Dsa.AArch64.ProbablePrime.code, Impl.Bignum.AArch64.seqs, Code.all, h]
    rfl

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.Generation.HashVariants`, which only this module used -/

section

/-! # Select the SHA-1 and SHA-256 stream implementations for DSA generation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Pbkdf2.Md.AArch64

theorem sha1_of_name (v : MdHash) (h : v.mgf.G.rust = "sha1") : v.mgf.G = Spec.Mgf1.sha1 := by
  have hm := v.mgf.mem
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  all_goals rw [hm] at h
  all_goals first | exact hm | contradiction

theorem sha256_of_name (v : MdHash) (h : v.mgf.G.rust = "sha256") : v.mgf.G = Spec.Mgf1.sha256 := by
  have hm := v.mgf.mem
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  all_goals rw [hm] at h
  all_goals first | exact hm | contradiction

theorem hashCode_size (v : MdHash) (x : List (BitVec 8)) : (v.mgf.G.hash x).length = v.H.D := by
  rw [v.mgf.hash, v.ok.hash, List.length_take, MdStream.Md.hash, v.ok.md.digest_length]
  exact Nat.min_eq_left v.ok.sizes.DN

def generationHashes (v1 v256 : MdHash) (h1 : v1.mgf.G.rust = "sha1")
    (h256 : v256.mgf.G.rust = "sha256") : GenerationHashes where
  sha1 := v1.H
  sha256 := v256.H
  h1 := v1.ok.stream
  h256 := v256.ok.stream
  hash1 x := by rw [← sha1_of_name v1 h1]; exact v1.mgf.hash x
  hash256 x := by rw [← sha256_of_name v256 h256]; exact v256.mgf.hash x
  size1 x := by rw [← sha1_of_name v1 h1]; exact hashCode_size v1 x
  size256 x := by rw [← sha256_of_name v256 h256]; exact hashCode_size v256 x
  width1 := by
    change v1.H.D = 20
    rw [← v1.mgf.len, sha1_of_name v1 h1]
    rfl
  width256 := by
    change v256.H.D = 32
    rw [← v256.mgf.len, sha256_of_name v256 h256]
    rfl

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # `vg_dsa_parameter_search` on AArch64, verified

`refill_correct` and `refill_ct` for the hash backends and Miller–Rabin
variants, and a state that meets the contract's precondition; and the pairs
of a SHA-1 and a SHA-256 implementation that the search is emitted for
(`hashPairs`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.MillerRabin.AArch64 VG.Proof.Dsa.AArch64.Generation

/-- `state`'s words `[0, 128, 32769 · 128, 0]` at `0x4000`. -/
def satMem : Mem :=
  Mem.writeW (Mem.writeW (fun _ => 0) (0x4008 : Addr) (128 : BitVec 64)) (0x4010 : Addr)
    (BitVec.ofNat 64 (Spec.Dsa.parameterEntropy 128))

/-- A search for width 128 with an empty tape. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 276 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x10000 | .x6 => 9216
    | .x7 => 0x4000 | _ => 0
  sp := 0x1000000000000
  mem := satMem
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x10000, 73728⟩, ⟨0x4000, 32⟩]

theorem refill_satisfiable : ∃ s, (Spec.Dsa.parameterSearchContract abi 768).pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (Impl.Dsa.AArch64.Generation.code v1.H v256.H (Generator.generatorStage v).run
      (ProbablePrime.primeTest v).run)
      (Spec.Dsa.parameterSearchContract abi 768) :=
  ⟨refill_correct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    refill_ct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    refill_satisfiable⟩

/-- A SHA-1 and a SHA-256 implementation, as the parameter search takes
them, and that they are SHA-1 and SHA-256. -/
structure Hashes where
  sha1 : MdHash
  sha256 : MdHash
  h1 : sha1.mgf.G.rust = "sha1"
  h256 : sha256.mgf.G.rust = "sha256"

open VG.Proof.Variants.MdHash.AArch64 (sha1Variants sha256Variants)

theorem sha1Variants_rust : ∀ v ∈ sha1Variants, v.mgf.G.rust = "sha1" := by
  intro v hv
  simp only [sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

theorem sha256Variants_rust : ∀ v ∈ sha256Variants, v.mgf.G.rust = "sha256" := by
  intro v hv
  simp only [sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

/-- The pairs the parameter search is emitted for, best first: a SHA-1 and
a SHA-256 implementation for the same CPUs (both baselines or both SHA-2
extensions). Either other pair needs the features of one of these, which
runs both hashes with them. -/
def hashPairs : List Hashes :=
  sha1Variants.attach.flatMap fun ⟨v1, h1⟩ => sha256Variants.attach.filterMap fun ⟨v256, h256⟩ =>
    if v1.suffix == v256.suffix then some ⟨v1, v256, sha1Variants_rust v1 h1, sha256Variants_rust v256 h256⟩
    else none

end VG.Proof.Dsa.AArch64.Generation.Refill
