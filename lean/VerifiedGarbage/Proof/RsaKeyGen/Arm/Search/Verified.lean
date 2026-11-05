module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CT
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Implies
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Verified
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! # The verified prime search (ARMv7)

For any candidate within 112 bytes of stack (`search_verified_of`), and for
the candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/Arm/RsaKeyGen.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

/-- The candidate's frame, 56 bytes, above the round's 56. -/
theorem cand_stack (v : RoundImpl) :
    FrameStack.armStack (Impl.RsaKeyGen.Arm.Candidate.code v.name v.code) ≤ 112 := by
  have := v.stack
  simp only [Impl.RsaKeyGen.Arm.Candidate.foL, Impl.RsaKeyGen.Arm.Candidate.foUsed, Impl.RsaKeyGen.Arm.Candidate.foE,
    Impl.RsaKeyGen.Arm.Candidate.foOut, Impl.RsaKeyGen.Arm.Candidate.aoEl, Impl.RsaKeyGen.Arm.Candidate.aoP,
    Impl.RsaKeyGen.Arm.Candidate.aoPl, Impl.RsaKeyGen.Arm.Candidate.aoR, Impl.RsaKeyGen.Arm.Candidate.aoRl,
    Impl.RsaKeyGen.Arm.Candidate.aoS, Impl.RsaKeyGen.Arm.Candidate.aoSl, Impl.RsaKeyGen.Arm.Candidate.mBase,
    Impl.RsaKeyGen.Arm.Candidate.aC, Impl.RsaKeyGen.Arm.Candidate.aTab, Impl.RsaKeyGen.Arm.Candidate.aE,
    Impl.RsaKeyGen.Arm.Candidate.aPr, Impl.RsaKeyGen.Arm.Candidate.aD1, Impl.RsaKeyGen.Arm.Candidate.aD2,
    Impl.RsaKeyGen.Arm.Candidate.aAbs, Impl.RsaKeyGen.Arm.Candidate.aBnd, Impl.RsaKeyGen.Arm.Candidate.aTmp,
    Impl.RsaKeyGen.Arm.Candidate.aOne, Impl.RsaKeyGen.Arm.Candidate.aTwo, Impl.RsaKeyGen.Arm.Candidate.aCm1,
    Impl.RsaKeyGen.Arm.Candidate.aX, Impl.RsaKeyGen.Arm.Candidate.aXf, Impl.RsaKeyGen.Arm.Candidate.aH1,
    Impl.RsaKeyGen.Arm.Candidate.aH2, Impl.RsaKeyGen.Arm.Candidate.aHm, Impl.RsaKeyGen.Arm.Candidate.aEx,
    Impl.RsaKeyGen.Arm.Candidate.nArr, Impl.RsaKeyGen.Arm.Candidate.sUsed, Impl.RsaKeyGen.Arm.Candidate.sCl,
    Impl.RsaKeyGen.Arm.Candidate.sLt, Impl.RsaKeyGen.Arm.Candidate.sTr, Impl.RsaKeyGen.Arm.Candidate.sEo,
    Impl.RsaKeyGen.Arm.Candidate.sE1, Impl.RsaKeyGen.Arm.Candidate.sG, Impl.RsaKeyGen.Arm.Candidate.sI,
    Impl.RsaKeyGen.Arm.Candidate.sUni, Impl.RsaKeyGen.Arm.Candidate.sU, Impl.RsaKeyGen.Arm.Candidate.sA,
    Impl.RsaKeyGen.Arm.Candidate.sBb, Impl.RsaKeyGen.Arm.Candidate.sTc, Impl.RsaKeyGen.Arm.Candidate.sBit,
    Impl.RsaKeyGen.Arm.Candidate.sCnt, Impl.RsaKeyGen.Arm.Candidate.sS1, Impl.RsaKeyGen.Arm.Candidate.sS2,
    Impl.RsaKeyGen.Arm.Candidate.sS3, Impl.RsaKeyGen.Arm.Candidate.sLo, Impl.RsaKeyGen.Arm.Candidate.sHi,
    Impl.RsaKeyGen.Arm.Candidate.sF, Impl.RsaKeyGen.Arm.Candidate.sStat, Impl.RsaKeyGen.Arm.Candidate.sChk,
    Impl.RsaKeyGen.Arm.Candidate.sMask, Impl.RsaKeyGen.Arm.Candidate.ctxB, Impl.RsaKeyGen.Arm.Candidate.ctxW,
    Impl.RsaKeyGen.Arm.Candidate.ctx, Impl.RsaKeyGen.Arm.Candidate.ltS, Impl.RsaKeyGen.Arm.Candidate.setS,
    Impl.RsaKeyGen.Arm.Candidate.invOf, Impl.RsaKeyGen.Arm.Candidate.finish, Impl.RsaKeyGen.Arm.Candidate.finNone,
    Impl.RsaKeyGen.Arm.Candidate.finUsed, Impl.RsaKeyGen.Arm.Candidate.finPrime,
    Impl.RsaKeyGen.Arm.Candidate.entry, Impl.RsaKeyGen.Arm.Candidate.lenCheck,
    Impl.RsaKeyGen.Arm.Candidate.setupC, Impl.RsaKeyGen.Arm.Candidate.topBits,
    Impl.RsaKeyGen.Arm.Candidate.candBits, Impl.RsaKeyGen.Arm.Candidate.loadC,
    Impl.RsaKeyGen.Arm.Candidate.closeCalc, Impl.RsaKeyGen.Arm.Candidate.closeCheck,
    Impl.RsaKeyGen.Arm.Candidate.tabStore, Impl.RsaKeyGen.Arm.Candidate.tabWrite,
    Impl.RsaKeyGen.Arm.Candidate.bigW, Impl.RsaKeyGen.Arm.Candidate.table, Impl.RsaKeyGen.Arm.Candidate.newton,
    Impl.RsaKeyGen.Arm.Candidate.entryS, Impl.RsaKeyGen.Arm.Candidate.redc,
    Impl.RsaKeyGen.Arm.Candidate.trialWord, Impl.RsaKeyGen.Arm.Candidate.trialFlag,
    Impl.RsaKeyGen.Arm.Candidate.trialPrime, Impl.RsaKeyGen.Arm.Candidate.trialStep,
    Impl.RsaKeyGen.Arm.Candidate.trial, Impl.RsaKeyGen.Arm.Candidate.gcdCheck,
    Impl.RsaKeyGen.Arm.Candidate.montSet, Impl.RsaKeyGen.Arm.Candidate.strideW,
    Impl.RsaKeyGen.Arm.Candidate.mont0, Impl.RsaKeyGen.Arm.Candidate.clrTop, Impl.RsaKeyGen.Arm.Candidate.montA,
    Impl.RsaKeyGen.Arm.Candidate.montB, Impl.RsaKeyGen.Arm.Candidate.cnt8, Impl.RsaKeyGen.Arm.Candidate.halfInit,
    Impl.RsaKeyGen.Arm.Candidate.halfBit, Impl.RsaKeyGen.Arm.Candidate.cntNext,
    Impl.RsaKeyGen.Arm.Candidate.halfBody, Impl.RsaKeyGen.Arm.Candidate.halving,
    Impl.RsaKeyGen.Arm.Candidate.sigMasks, Impl.RsaKeyGen.Arm.Candidate.powWord,
    Impl.RsaKeyGen.Arm.Candidate.halfIf, Impl.RsaKeyGen.Arm.Candidate.expTop,
    Impl.RsaKeyGen.Arm.Candidate.expSetup, Impl.RsaKeyGen.Arm.Candidate.ltAdd,
    Impl.RsaKeyGen.Arm.Candidate.checksC, Impl.RsaKeyGen.Arm.Candidate.mrInit,
    Impl.RsaKeyGen.Arm.Candidate.avFlag, Impl.RsaKeyGen.Arm.Candidate.witnessLoad,
    Impl.RsaKeyGen.Arm.Candidate.orTwo, Impl.RsaKeyGen.Arm.Candidate.clrTopBit,
    Impl.RsaKeyGen.Arm.Candidate.witnessFix, Impl.RsaKeyGen.Arm.Candidate.wsLen,
    Impl.RsaKeyGen.Arm.Candidate.mrCall, Impl.RsaKeyGen.Arm.Candidate.goFlag, Impl.RsaKeyGen.Arm.Candidate.onPass,
    Impl.RsaKeyGen.Arm.Candidate.mrBody, Impl.RsaKeyGen.Arm.Candidate.millerRabin,
    Impl.RsaKeyGen.Arm.Candidate.mrResult, Impl.RsaKeyGen.Arm.Candidate.mrPart, Impl.RsaKeyGen.Arm.Candidate.main,
    Impl.RsaKeyGen.Arm.Candidate.body, Impl.RsaKeyGen.Arm.Candidate.code, Impl.Bignum.Arm.TrialDivision16.newton,
    Impl.Bignum.Arm.TrialDivision16.redc, Impl.Bignum.Arm.TwoPower.code, Impl.Bignum.Arm.montOp,
    Impl.Bignum.Arm.precomputeInverse, Impl.Bignum.Arm.r2, Impl.Bignum.Arm.setup, Impl.Bignum.Arm.store64,
    Impl.Bignum.Arm.zero, Impl.Rsa.Arm.CrtValues.load, Impl.Rsa.Arm.CrtValues.store, Impl.Rsa.Arm.Keys.aM,
    Impl.Rsa.Arm.Keys.aNM, Impl.Rsa.Arm.Keys.aZero, Impl.Rsa.Arm.Keys.bitOf, Impl.Rsa.Arm.Keys.copy,
    Impl.Rsa.Arm.Keys.eqS, Impl.Rsa.Arm.Keys.half, Impl.Rsa.Arm.Keys.hdr, Impl.Rsa.Arm.Keys.inverse,
    Impl.Rsa.Arm.Keys.orOne, Impl.Rsa.Arm.Keys.ptr, Impl.Rsa.Arm.Keys.sel, Impl.Rsa.Arm.Keys.seqs,
    Impl.Rsa.Arm.Keys.stride, Impl.Rsa.Arm.Keys.sub3, Impl.Rsa.Arm.Recover.clrTop, Impl.RsaKeyGen.Arm.Key.andNotS,
    Impl.RsaKeyGen.Arm.Key.isOne, Impl.RsaKeyGen.Arm.Key.notS, Impl.RsaKeyGen.Arm.Key.setHi,
    Impl.RsaKeyGen.Arm.Key.setWd, Impl.RsaKeyGen.Arm.Key.zeroOut, Impl.RsaKeyGen.tabEntry,
    Impl.Bignum.Arm.TwoPower.step, Impl.Bignum.Arm.compareWords, Impl.Bignum.Arm.copyWords,
    Impl.Bignum.Arm.loadBE, Impl.Bignum.Arm.maskBytes, Impl.Bignum.Arm.selectRow, Impl.Bignum.Arm.subRow,
    Impl.Rsa.Arm.Keys.Inv.batch, Impl.Rsa.Arm.Keys.Inv.finish, Impl.Rsa.Arm.Keys.Inv.init,
    Impl.Rsa.Arm.Keys.eqNormalize, Impl.Rsa.Arm.shiftRight, Impl.Bignum.Arm.TrialDivision16.redcAt,
    Impl.Bignum.Arm.compareWordStep, Impl.Bignum.Arm.copyWordBody, Impl.Bignum.Arm.loadBEreverseArgs,
    Impl.Bignum.Arm.maskByteStep, Impl.Bignum.Arm.reverseBytes, Impl.Bignum.Arm.selectBody,
    Impl.Bignum.Arm.selectMask, Impl.Bignum.Arm.subBody, Impl.Bignum.Arm.zeroStep, Impl.Rsa.Arm.Keys.Inv.bA1,
    Impl.Rsa.Arm.Keys.Inv.bD, Impl.Rsa.Arm.Keys.Inv.bE, Impl.Rsa.Arm.Keys.Inv.bF, Impl.Rsa.Arm.Keys.Inv.bG,
    Impl.Rsa.Arm.Keys.Inv.bP, Impl.Rsa.Arm.Keys.Inv.bT1, Impl.Rsa.Arm.Keys.Inv.bT2, Impl.Rsa.Arm.Keys.Inv.bZ,
    Impl.Rsa.Arm.Keys.Inv.copy1, Impl.Rsa.Arm.Keys.Inv.csub1, Impl.Rsa.Arm.Keys.Inv.divsteps,
    Impl.Rsa.Arm.Keys.Inv.fSign, Impl.Rsa.Arm.Keys.Inv.negInv, Impl.Rsa.Arm.Keys.Inv.sel1,
    Impl.Rsa.Arm.Keys.Inv.start, Impl.Rsa.Arm.Keys.Inv.sub1, Impl.Rsa.Arm.Keys.Inv.topZero,
    Impl.Rsa.Arm.Keys.Inv.update, Impl.Rsa.Arm.Keys.Inv.zero1, Impl.Rsa.Arm.Keys.Inv.zeroW,
    Impl.Rsa.Arm.Keys.setOne, Impl.Rsa.Arm.shiftRightStep, Impl.Bignum.Arm.copyWord,
    Impl.Bignum.Arm.reverseByteStep, Impl.Bignum.Arm.selectStep, Impl.Bignum.Arm.subAdvance,
    Impl.Bignum.Arm.subStep, Impl.Rsa.Arm.Keys.Inv.cnt1, Impl.Bignum.Arm.rowAdvance, Impl.Bignum.Arm.selectWord,
    Impl.Bignum.Arm.subBorrow, Impl.Bignum.Arm.MontFn.body, Impl.Bignum.Arm.doubleLoop,
    Impl.Bignum.Arm.initInverse, Impl.Bignum.Arm.r2Init, Impl.Bignum.Arm.r2Squares, Impl.Bignum.Arm.setBases,
    Impl.Rsa.Arm.Keys.Inv.bA2, Impl.Rsa.Arm.Keys.Inv.cQ, Impl.Rsa.Arm.Keys.Inv.cR, Impl.Rsa.Arm.Keys.Inv.cU,
    Impl.Rsa.Arm.Keys.Inv.cV, Impl.Rsa.Arm.Keys.Inv.lin, Impl.Rsa.Arm.Keys.Inv.redc, Impl.Rsa.Arm.Keys.Inv.shr1,
    Impl.Bignum.Arm.doubleLoopBody, Impl.Bignum.Arm.montBody, Impl.Bignum.Arm.r2Constants,
    Impl.Bignum.Arm.squareOp, Impl.Rsa.Arm.Keys.Inv.cneg, Impl.Rsa.Arm.Keys.Inv.mac1,
    Impl.Rsa.Arm.Keys.Inv.macRow, Impl.Rsa.Arm.Keys.Inv.shr30, Impl.Bignum.Arm.doubleLoopMultiply,
    Impl.Bignum.Arm.montCore, Impl.Bignum.Arm.montInit, Impl.Bignum.Arm.smallConst, Impl.Bignum.Arm.squareBody,
    Impl.Bignum.Arm.doubleFnRestore, Impl.Bignum.Arm.montFinish, Impl.Bignum.Arm.montRounds,
    Impl.Bignum.Arm.setSmallFn, Impl.Bignum.Arm.sqBody, Impl.Bignum.Arm.crossRows, Impl.Bignum.Arm.csub,
    Impl.Bignum.Arm.doubleFnBody, Impl.Bignum.Arm.montRound, Impl.Bignum.Arm.setSmallFnBody,
    Impl.Bignum.Arm.sqDiag, Impl.Bignum.Arm.sqDouble, Impl.Bignum.Arm.sqFinish, Impl.Bignum.Arm.sqInit,
    Impl.Bignum.Arm.sqReduce, Impl.Bignum.Arm.crossRound, Impl.Bignum.Arm.diagLoop, Impl.Bignum.Arm.doubleBody,
    Impl.Bignum.Arm.fusedReductionStage, Impl.Bignum.Arm.productStage, Impl.Bignum.Arm.redRounds,
    Impl.Bignum.Arm.reduceChoice, Impl.Bignum.Arm.setSmall, Impl.Bignum.Arm.shiftLeft, Impl.Bignum.Arm.sqAnchor,
    Impl.Bignum.Arm.FusedReduction.code, Impl.Bignum.Arm.diagStep, Impl.Bignum.Arm.doubleCore,
    Impl.Bignum.Arm.redRound, Impl.Bignum.Arm.row, Impl.Bignum.Arm.rowFull, Impl.Bignum.Arm.DownRow.code,
    Impl.Bignum.Arm.FusedReduction.first, Impl.Bignum.Arm.FusedReduction.top, Impl.Bignum.Arm.doubleProduct,
    Impl.Bignum.Arm.rowBody, Impl.Bignum.Arm.rowCarry, Impl.Bignum.Arm.rowLoop2, Impl.Bignum.Arm.DownRow.loop,
    Impl.Bignum.Arm.rowBody2, Impl.Bignum.Arm.rowStep, Impl.Bignum.Arm.DownRow.body, Impl.Bignum.Arm.rowStepAt,
    Impl.Bignum.Arm.DownRow.step, FrameStack.armStack, List.cons_append, List.nil_append, Nat.max_zero,
    Nat.zero_max, Nat.max_self, List.length_cons, List.length_nil]
  omega

theorem search_verified_of (c : Cand) :
    Verified target (Impl.RsaKeyGen.Arm.Search.code c.call)
      (Spec.RsaKeyGen.primeSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) : Cand where
  name := "vg_rsa_keygen_candidate" ++ v.suffix
  code := Impl.RsaKeyGen.Arm.Candidate.code v.name v.code
  verified := Proof.RsaKeyGen.Arm.Cand.cand_verified v
  stack := cand_stack v

/-- The search calling it. -/
abbrev searchCode [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) : Prog isa :=
  Impl.RsaKeyGen.Arm.Search.code (Cand.ofRound v).call

theorem search_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    Verified target (searchCode v) (Spec.RsaKeyGen.primeSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.RsaKeyGen.Arm.Search
