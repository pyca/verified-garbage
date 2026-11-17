module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Bignum.Arm.CrtPrecomputed
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStages
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.CrtGiven
import VerifiedGarbage.Proof.Bignum.Arm.CrtGivenCT
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.CrtPrecomputedContract
meta import VerifiedGarbage.TCB.Arm.Target

/-! ### `Bignum.Arm.CrtContract`, which only this module used -/

section

/-! ### `Bignum.Arm.CrtContractInput`, which only this module used -/

section

/-! # Native private-CRT arguments satisfy the shared API's buffer contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def crtCallGeometry (s : State) : CrtGeometry where
  base := stackArg s 12
  output := s.gpr .r0
  modulus := s.gpr .r2
  input := stackArg s 0
  p := stackArg s 2
  q := stackArg s 4
  dp := stackArg s 6
  dq := stackArg s 8
  qi := stackArg s 10
  size := 8 * (stackArg s 13).toNat
  length := (s.gpr .r3).toNat
  pLength := (stackArg s 3).toNat
  qLength := (stackArg s 5).toNat

def crtCallBytes (s : State) (i : Fin 7) : List Byte :=
  Spec.Rsa.bytesAt s.mem (State.addr ((crtCallGeometry s).source i)) ((crtCallGeometry s).sourceLength i)

theorem crt_contract_pre (s : State) (h : (Proof.Rsa.privateCrtContract abi 56).pre s) :
    CrtFnInput (crtCallGeometry s) (crtCallBytes s) s := by
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, _, _, _, _, outWs, _,
    nWs, inputWs, pWs, qWs, dpWs, dqWs, qiWs, wsArgs,
    stackOut, stackN, stackInput, stackP, stackQ, stackDp, stackDq, stackQi, stackWs, stackArgs,
    outFit, nFit, inputFit, pFit, qFit, dpFit, dqFit, qiFit, wsFit,
    valid, outLen, inputLen, pPositive, pShort, qPositive, qShort, dpLen, qiLen, dqLen, space⟩ := h
  rw [outLen] at wr outWs stackOut outFit
  rw [inputLen, dpLen, qiLen, dqLen] at rd
  rw [inputLen] at inputWs stackInput inputFit
  rw [dpLen] at dpWs stackDp dpFit
  rw [qiLen] at qiWs stackQi qiFit
  rw [dqLen] at dqWs stackDq dqFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  have argRead (i : Nat) (hi : i < 14) :
      s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * i)) 32 = stackArg s i := by
    unfold stackArg stackArgAddr VG.Proof.Mont.off
    rw [addr_add (by omega_arith : s.sp.toNat + 4 * i < 2 ^ 32)]
  refine {
    workspace := ⟨?_, ?_⟩, lengthValid := valid,
    storageFits := Nat.le_trans (crt_layout_fits valid) (Nat.mul_le_mul_left 8 space),
    pPositive := pPositive, pShort := pShort, qPositive := qPositive, qShort := qShort,
    r2 := (fun _ ha => by cases ha),
    source := ?_, sourceSeparate := ?_, outputFits := outFit, write := ?_, outputSeparate := ?_,
    output := rfl, modulus := rfl, count := ?_, stackFit := stackFit, argFit := argFit,
    argRead := ?_, pointer := ?_, length := ?_, workspaceArg := argRead 12 (by decide),
    stackWorkspace := ?_, argsWorkspace := ?_, stackSource := ?_, stackOutput := ?_, stackArgs := ?_ }
  · simpa only [crtCallGeometry, Nat.mul_comm] using wsFit
  · rw [wr]; simp [crtCallGeometry, State.addr, Nat.mul_comm]
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨nFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨inputFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 0)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨pFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 2)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 4)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dpFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 6)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dqFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 8)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qiFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 10)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using nWs
    · change Region.Disjoint ⟨State.addr (stackArg s 0), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using inputWs
    · change Region.Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using pWs
    · change Region.Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qWs
    · change Region.Disjoint ⟨State.addr (stackArg s 6), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dpWs
    · change Region.Disjoint ⟨State.addr (stackArg s 8), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dqWs
    · change Region.Disjoint ⟨State.addr (stackArg s 10), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qiWs
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [crtCallGeometry, State.addr, Nat.mul_comm] using outWs.symm
  · simp [crtCallGeometry]
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [crtCallGeometry, CrtGeometry.source]
    · exact argRead 0 (by decide)
    · exact argRead 2 (by decide)
    · exact argRead 4 (by decide)
    · exact argRead 6 (by decide)
    · exact argRead 8 (by decide)
    · exact argRead 10 (by decide)

  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 1)) 32 = BitVec.ofNat 32 (s.gpr .r3).toNat
      rw [argRead 1 (by decide)]
      rw [← inputLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 3)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 3 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 5)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 5 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 7)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 7 (by decide)]
      rw [← dpLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 9)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 9 (by decide)]
      rw [← dqLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 11)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 11 (by decide)]
      rw [← qiLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [frame]; simpa only [crtCallGeometry, State.addr, Nat.mul_comm] using stackWs
  · simpa only [crtCallGeometry, State.addr, Nat.mul_comm] using wsArgs.symm
  · intro i
    rw [frame]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact stackN
    · exact stackInput
    · exact stackP
    · exact stackQ
    · exact stackDp
    · exact stackDq
    · exact stackQi
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs

end VG.Proof.Bignum.Arm

/-! # `vg_rsa_private_crt_precomputed`'s arguments as the CRT's input

`vg_rsa_private_crt`'s (`crt_contract_pre`), and the factors' `R²` at its
argument 14. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def crtCallGeometryP (s : State) : CrtGeometry := { crtCallGeometry s with r2 := some (stackArg s 14) }

theorem crt_contract_preP (s : State) (h : (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s) :
    CrtFnInput (crtCallGeometryP s) (crtCallBytes s) s := by
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, _, _, _, _, outWs, outR2, outArgs,
    nWs, inputWs, pWs, qWs, dpWs, dqWs, qiWs, wsR2, wsArgs,
    stackOut, stackN, stackInput, stackP, stackQ, stackDp, stackDq, stackQi, stackWs, stackR2, stackArgs,
    outFit, nFit, inputFit, pFit, qFit, dpFit, dqFit, qiFit, wsFit, r2Fit,
    valid, outLen, inputLen, pPositive, pShort, qPositive, qShort, dpLen, qiLen, dqLen, space,
    r2Len, r2Words, _⟩ := h
  rw [outLen] at wr outWs stackOut outFit outR2 outArgs
  rw [inputLen, dpLen, qiLen, dqLen] at rd
  rw [inputLen] at inputWs stackInput inputFit
  rw [dpLen] at dpWs stackDp dpFit
  rw [qiLen] at qiWs stackQi qiFit
  rw [dqLen] at dqWs stackDq dqFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  have argRead (i : Nat) (hi : i < 16) :
      s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * i)) 32 = stackArg s i := by
    unfold stackArg stackArgAddr VG.Proof.Mont.off
    rw [addr_add (by omega_arith : s.sp.toNat + 4 * i < 2 ^ 32)]
  refine {
    workspace := ⟨?_, ?_⟩, lengthValid := valid,
    storageFits := Nat.le_trans (crt_layout_fits valid) (Nat.mul_le_mul_left 8 space),
    pPositive := pPositive, pShort := pShort, qPositive := qPositive, qShort := qShort,
    r2 := ?_,
    source := ?_, sourceSeparate := ?_, outputFits := outFit, write := ?_, outputSeparate := ?_,
    output := rfl, modulus := rfl, count := ?_, stackFit := stackFit, argFit := by omega_using [argFit],
    argRead := ?_, pointer := ?_, length := ?_, workspaceArg := argRead 12 (by decide),
    stackWorkspace := ?_, argsWorkspace := ?_, stackSource := ?_, stackOutput := ?_, stackArgs := ?_ }
  · simpa only [crtCallGeometryP, crtCallGeometry, Nat.mul_comm] using wsFit
  · rw [wr]; simp [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm]
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨nFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨inputFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 0)) (s.gpr .r3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨pFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 2)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 4)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dpFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 6)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨dqFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 8)) (stackArg s 5).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · refine ⟨qiFit, ?_, rfl⟩
      change InRegions (s.rd ++ s.wr) (State.addr (stackArg s 10)) (stackArg s 3).toNat
      exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using nWs
    · change Region.Disjoint ⟨State.addr (stackArg s 0), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using inputWs
    · change Region.Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using pWs
    · change Region.Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qWs
    · change Region.Disjoint ⟨State.addr (stackArg s 6), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dpWs
    · change Region.Disjoint ⟨State.addr (stackArg s 8), (stackArg s 5).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using dqWs
    · change Region.Disjoint ⟨State.addr (stackArg s 10), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 12), 8 * (stackArg s 13).toNat⟩
      simpa only [State.addr, Nat.mul_comm] using qiWs
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using outWs.symm
  · simp [crtCallGeometryP, crtCallGeometry]
  · exact ⟨⟨State.addr s.sp, 64⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]),
      by simp [Region.Contains]⟩
  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [crtCallGeometryP, crtCallGeometry, CrtGeometry.source]
    · exact argRead 0 (by decide)
    · exact argRead 2 (by decide)
    · exact argRead 4 (by decide)
    · exact argRead 6 (by decide)
    · exact argRead 8 (by decide)
    · exact argRead 10 (by decide)

  · intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 1)) 32 = BitVec.ofNat 32 (s.gpr .r3).toNat
      rw [argRead 1 (by decide)]
      rw [← inputLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 3)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 3 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 5)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 5 (by decide)]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 7)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 7 (by decide)]
      rw [← dpLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 9)) 32 = BitVec.ofNat 32 (stackArg s 5).toNat
      rw [argRead 9 (by decide)]
      rw [← dqLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) (4 * 11)) 32 = BitVec.ofNat 32 (stackArg s 3).toNat
      rw [argRead 11 (by decide)]
      rw [← qiLen]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [frame]; simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using stackWs
  · exact (by simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using wsArgs.symm : Region.Disjoint _ _).sub_left
      (Region.sub_prefix (by decide))
  · intro i
    rw [frame]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact stackN
    · exact stackInput
    · exact stackP
    · exact stackQ
    · exact stackDp
    · exact stackDq
    · exact stackQi
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs.sub_right (Region.sub_prefix (by decide))
  · intro a ha
    cases ha
    have words : 8 * (crtCallGeometryP s).r2Words = (stackArg s 15).toNat * 8 := by
      rw [r2Len]; simp [crtCallGeometryP, crtCallGeometry, CrtGeometry.r2Words, Nat.mul_comm]
    have slotSub : Region.Sub ⟨VG.Proof.Mont.off (State.addr s.sp) 56, 4⟩ ⟨State.addr s.sp, 64⟩ :=
      Offset.sub_base _ (by decide)
    have args : InRegions (s.rd ++ s.wr) (State.addr s.sp) 64 :=
      ⟨⟨State.addr s.sp, 64⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    refine ⟨by omega_using [argFit], VG.CallLay.inRegions_sub args (by decide : 56 + 4 ≤ 64) (by decide),
      argRead 14 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (by simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using wsArgs.symm : Region.Disjoint _ _).sub_left slotSub
    · exact (by simpa only [crtCallGeometryP, crtCallGeometry, State.addr] using outArgs.symm : Region.Disjoint _ _).sub_left slotSub
    · rw [frame]; exact stackArgs.sub_right slotSub
    · rw [words]; simpa only [State.addr] using r2Fit
    · rw [words]; exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
    · rw [words]; simpa only [crtCallGeometryP, crtCallGeometry, State.addr, Nat.mul_comm] using wsR2.symm
    · rw [words, frame]; simpa only [State.addr] using stackR2
    · rw [words]; simpa only [crtCallGeometryP, crtCallGeometry, State.addr] using outR2.symm
    · rw [show (crtCallGeometryP s).r2Words = (stackArg s 15).toNat by omega_using [words]]
      exact r2Words

theorem crt_contract_pqP (s : State) (h : (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s) :
    Spec.Rsa.os2ip (crtCallBytes s 2) * Spec.Rsa.os2ip (crtCallBytes s 3) = Spec.Rsa.os2ip (crtCallBytes s 0) := by
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end VG.Proof.Bignum.Arm

end
end

end

/-! # Private CRT RSA satisfies its shared contract under AAPCS -/

public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

/-- `vg_rsa_private_crt`'s key check and factor preparation. -/
def baselineStages : CrtStages where
  check := CrtFn.validate
  prime := narrowPrime
  ok _ _ := True
  checkOk s _ h ready := crt_validateStage_ok s h ready
  checkCt _ _ := crt_validateStage_ct
  primeOk := fun {g} {_} j s hj _ h => by
    obtain ⟨_, le, _, _, _, _, _⟩ := h.1.narrow_fits j hj
    have words : g.words ≤ 128 := (crt_width_valid h.1.buffers.lengthValid).2.1
    exact crt_narrowPrime_ok s h.2 (by omega_using [le, words])
  primeCt := fun {g} {_} {_} j hj _ _ => by
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨_, le, _, _, _, _, _⟩ := h.1.1.narrow_fits j hj
    have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
    exact crt_narrowPrime_ct (by omega_using [le, words]) s t tr1 tr2 u w ⟨h.1.2, h.2.1.2, h.2.2⟩ e1 e2

end VG.Proof.Bignum.Arm
end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtFnCT.lean`, which only this module imported.
section

/-! # The callable private RSA operation leaks only public geometry and modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crtFn_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0)
    (st : CrtStages) (hst1 : st.ok g bs1) (hst2 : st.ok g bs2) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtFnInput g bs1 s ∧ CrtFnInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.codeOf st.check st.prime kernel.code) (fun _ _ => True) := by
  unfold CrtFn.codeOf
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := crt_entry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, _, _, _⟩ := crt_entry_ready s0 hs
      obtain ⟨_, t1, run2, ready2, _, _, _⟩ := crt_entry_ready t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have body := relCT_keep_sp
        (crt_body_scoped_ct (kernel := kernel) (g := g) modulus st hst1 hst2)
        (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := body.seq restore _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtSaved.lean`, which only this module imported.
section

/-! # The secret acceptance slot does not overlap saved AAPCS registers -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem crt_callee_saved {s t : State} {g : CrtGeometry} {regs : Reg → BitVec 32}
    (saved : Spill.Saved s.mem (State.addr s.sp) regs pcCalleeSaved)
    (frame : Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem)
    (workspace : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.base, g.size⟩)
    (output : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.output, g.length⟩) :
    Spill.Saved t.mem (State.addr s.sp) regs pcCalleeSaved := by
  intro p hp
  have fit : p.2 + 4 ≤ 56 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have gap : p.2 + 4 ≤ 48 ∨ 52 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have low : 16 ≤ p.2 := by
    simp only [pcCalleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have sub : (⟨off (State.addr s.sp) p.2, 4⟩ : Region).Sub ⟨State.addr s.sp, 56⟩ :=
    Offset.sub_base _ fit
  have keep := frame.readW (a := off (State.addr s.sp) p.2) (w := 32) (r := ⟨off (State.addr s.sp) p.2, 4⟩) (by simp [Region.Contains])
    (by
      intro r hr
      simp only [crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | rfl
      · exact workspace.sub_left sub
      · exact Offset.disjoint_base _ (by omega_using [low]) (by omega_using [fit])
      · exact Offset.disjoint _ (Or.inr (by omega_using [low])) (by omega_using [fit]) (by decide)
      · exact Offset.disjoint _ gap (by omega_using [fit]) (by decide)
      · exact output.sub_left sub) (by decide : 32 / 8 < 2 ^ 64)
  exact keep.trans (saved p hp)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtFn.lean`, which only this module imported.
section

/-! # Callable ARMv7 private RSA preserves AAPCS and implements the shared result -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem crtFn_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s)
    (st : CrtStages) (hst : st.ok g bs) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.codeOf st.check st.prime kernel.code) s fun t => abiPreserved s t ∧
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) := by
  unfold CrtFn.codeOf
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (crt_entry_ready s h) ?_
  rintro u ⟨ready, _, savedU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono ((crt_body_scoped_ok (kernel := kernel)) u ready st hst) ?_
  rintro v ⟨result, frameV, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply crt_callee_saved savedU frameV
    · rw [restU.sp]; exact h.stackWorkspace
    · rw [restU.sp]; exact h.stackOutput
  have fit : v.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega_using []
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by decide)
    · exact restored (.r5, 20) (by decide)
    · exact restored (.r6, 24) (by decide)
    · exact restored (.r7, 28) (by decide)
    · exact restored (.r8, 32) (by decide)
    · exact restored (.r9, 36) (by decide)
    · exact restored (.r10, 40) (by decide)
    · exact restored (.r11, 44) (by decide)
    · exact restored (.lr, 52) (by decide)
  · rw [popped_sp, restT.sp, spV]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret]
    exact result

end VG.Proof.Bignum.Arm
end

end

/-! ## `vg_rsa_private_crt_precomputed`'s key check and factor preparation

For a key whose factors' `R² mod p` and `R² mod q` are given (`g.r2`) and
whose factors' product is the modulus, which those values imply. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- The keys `givenStages` is for. -/
def GivenOk (g : CrtGeometry) (bs : Fin 7 → List Byte) : Prop :=
  g.r2.isSome ∧ Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0)

theorem given_check_ok {g : CrtGeometry} {bs : Fin 7 → List Byte} (s : State) (hok : GivenOk g bs)
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.validateGiven s (CrtCheckPost g bs s) :=
  crt_validateGivenStage_ok s hok.2 h ready

theorem given_check_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.validateGiven (fun _ _ => True) :=
  crt_validateGivenStage_ct

theorem given_prime_ok {g : CrtGeometry} {bs : Fin 7 → List Byte} (j : Fin 6) (s : State) (hj : j = 1 ∨ j = 2)
    (hok : GivenOk g bs) (h : CrtPrimeIn g bs j s) :
    WP isa (narrowPrimeGiven (56 + 8 * j.val)) s (NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ) g.words) (bs j.succ) s) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hok.1
  exact crt_narrowPrimeGiven_ok j s hj ha h

theorem given_prime_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6) (hj : j = 1 ∨ j = 2)
    (hok : GivenOk g bs1) :
    RelCT isa (fun s t => CrtPrimeIn g bs1 j s ∧ CrtPrimeIn g bs2 j t ∧ s.sp = t.sp)
      (narrowPrimeGiven (56 + 8 * j.val)) (fun _ _ => True) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hok.1
  exact crt_narrowPrimeGiven_ct hj ha

def givenStages : CrtStages where
  check := CrtFn.validateGiven
  prime := narrowPrimeGiven
  ok := GivenOk
  checkOk s hok h ready := given_check_ok s hok h ready
  checkCt _ _ := given_check_ct
  primeOk j s hj hok h := given_prime_ok j s hj hok h
  primeCt j hj hok _ := given_prime_ct j hj hok

end VG.Proof.Bignum.Arm
end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_contract_correct (s : State) (h : (Proof.Rsa.privateCrtContract abi 56).pre s) (kernel : WindowKernel := baselineWindowKernel) :
    ∃ tr t, Exec isa (CrtFn.codeWith kernel.code) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCrtContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := (crtFn_ok (kernel := kernel)) s (crt_contract_pre s h) baselineStages trivial
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem crt_contract_ct (kernel : WindowKernel := baselineWindowKernel) : ConstantTime isa (Proof.Rsa.privateCrtContract abi 56).pre
    (Proof.Rsa.privateCrtContract abi 56).pub (CrtFn.codeWith kernel.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := crt_contract_pre s hs
  have it := crt_contract_pre t ht
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, _, a2, a3, a4, a5, a6, _, a8, _, a10, _, a12, a13⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geometry : crtCallGeometry s = crtCallGeometry t := by
    simp only [crtCallGeometry, p0, p2, p3, a0, a2, a3, a4, a5, a6, a8, a10, a12, a13]
  rw [← geometry] at it
  have modulus : crtCallBytes s 0 = crtCallBytes t 0 := byteEq
  exact ((crtFn_ct (kernel := kernel)) modulus baselineStages trivial trivial s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

/-! ## `vg_rsa_private_crt_precomputed` -/

theorem crt_contract_correctP (s : State) (h : (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s)
    (kernel : WindowKernel := baselineWindowKernel) :
    ∃ tr t, Exec isa (CrtFn.codeGiven kernel.code) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCrtPrecomputedContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := (crtFn_ok (kernel := kernel)) s (crt_contract_preP s h) givenStages
    (show GivenOk _ _ from ⟨rfl, crt_contract_pqP s h⟩)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem crt_contract_ctP (kernel : WindowKernel := baselineWindowKernel) :
    ConstantTime isa (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre
      (Proof.Rsa.privateCrtPrecomputedContract abi 56).pub (CrtFn.codeGiven kernel.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := crt_contract_preP s hs
  have it := crt_contract_preP t ht
  have oks : GivenOk (crtCallGeometryP s) (crtCallBytes s) := ⟨rfl, crt_contract_pqP s hs⟩
  have okt : GivenOk (crtCallGeometryP t) (crtCallBytes t) := ⟨rfl, crt_contract_pqP t ht⟩
  sig_pub [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, a0, _, a2, a3, a4, a5, a6, _, a8, _, a10, _, a12, a13, a14, _⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have geometry : crtCallGeometryP s = crtCallGeometryP t := by
    simp only [crtCallGeometryP, crtCallGeometry, p0, p2, p3, a0, a2, a3, a4, a5, a6, a8, a10, a12, a13, a14]
  rw [← geometry] at it okt
  have modulus : crtCallBytes s 0 = crtCallBytes t 0 := byteEq
  exact ((crtFn_ct (kernel := kernel)) modulus givenStages oks okt s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm

end

end


/-! # ARMv7 private CRT RSA is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Separate buffers for a 64-byte modulus and 32-byte factors, with native stack arguments. -/
def crtSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else
    if a = 0x8004 then 0x40 else
    if a = 0x8009 then 0x31 else
    if a = 0x800c then 0x20 else
    if a = 0x8011 then 0x32 else
    if a = 0x8014 then 0x20 else
    if a = 0x8019 then 0x33 else
    if a = 0x801c then 0x20 else
    if a = 0x8021 then 0x34 else
    if a = 0x8024 then 0x20 else
    if a = 0x8029 then 0x35 else
    if a = 0x802c then 0x20 else
    if a = 0x8031 then 0x40 else
    if a = 0x8034 then 0x20 else
    if a = 0x8035 then 0x4 else
    0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩, ⟨0x3200, 32⟩,
    ⟨0x3300, 32⟩, ⟨0x3400, 32⟩, ⟨0x3500, 32⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem crt_contract_sat : ∃ s, (Proof.Rsa.privateCrtContract abi 56).pre s := by
  sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using crtSatState

theorem crt_verified (kernel : WindowKernel := baselineWindowKernel) : Verified target (CrtFn.codeWith kernel.code) (Proof.Rsa.privateCrtContract abi 56) :=
  ⟨(crt_contract_correct (kernel := kernel)), (crt_contract_ct (kernel := kernel)), crt_contract_sat⟩

theorem os2ip_replicate_zero' (n : Nat) : Spec.Rsa.os2ip (List.replicate n 0) = 0 := by
  unfold Spec.Rsa.os2ip
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl

/-- `crtSatState`, with factors of one octet, zero (whose product is the zero
modulus, and whose `R² mod p`, `2^256` of 2 words, is zeros), and their `R²`
at `0x3600`. -/
def crtSatStateP : State :=
  { crtSatState with
    mem := fun a => if a = 0x8039 then 0x36 else if a = 0x803c then 4 else
      if a = 0x800c ∨ a = 0x8014 ∨ a = 0x801c ∨ a = 0x8024 ∨ a = 0x802c then 1 else crtSatState.mem a
    rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩,
      ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩, ⟨0x3600, 32⟩, ⟨0x8000, 64⟩] }

theorem crt_contract_satP : ∃ s, (Proof.Rsa.privateCrtPrecomputedContract abi 56).pre s := by
  refine ⟨crtSatStateP, ?_⟩
  sig_pre [Proof.Rsa.privateCrtPrecomputedContract, Proof.Rsa.privateCrtPrecomputedSig,
      Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  rotate_right 3
  · decide
  · rw [show Spec.Rsa.wordsAt _ _ _ = List.replicate 4 0 by decide,
      show Spec.Rsa.bytesAt _ _ _ = [0] by decide, show Spec.Rsa.bytesAt _ _ _ = [0] by decide]
    decide
  · rw [show Spec.Rsa.bytesAt _ _ _ = [0] by decide, show Spec.Rsa.bytesAt _ _ _ = [0] by decide,
      show Spec.Rsa.bytesAt _ _ _ = List.replicate 64 0 by decide, os2ip_replicate_zero']
    rfl
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, crtSatStateP, crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
         at h₁ h₂
       bv_omega)

theorem crt_verifiedP (kernel : WindowKernel := baselineWindowKernel) :
    Verified target (CrtFn.codeGiven kernel.code) (Proof.Rsa.privateCrtPrecomputedContract abi 56) :=
  ⟨(crt_contract_correctP (kernel := kernel)), (crt_contract_ctP (kernel := kernel)), crt_contract_satP⟩

end VG.Proof.Bignum.Arm
