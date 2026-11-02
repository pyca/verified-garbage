module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.Contract

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
