module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePre
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! The public signature supplies all permissions, incoming words and 184 bytes of stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem candidateInput {s : State} {p : CandidateParams}
    (pre : (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre s) (args : CandidateAbi p s) :
    CandidateFnInput p s := by
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, _, _, _, _, _, _, stackOut, stackUsed, stackTape, stackScratch, stackArgs,
    _, _, _, _, _, _, _, _, _⟩ := pre
  have widthNat : (s.gpr .r1).toNat = p.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.length_bounds; omega)]
  have tapeNat : (stackArg s 2).toNat = p.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount]
  have capacityNat : (stackArg s 4).toNat = p.capacity := by
    rw [args.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.capacity_fits]
  rw [args.out, args.used, args.base, widthNat, capacityNat, Nat.mul_comm p.capacity 8] at wr
  rw [args.tape, tapeNat] at rd
  rw [args.out, widthNat] at stackOut
  rw [args.used] at stackUsed
  rw [args.tape, tapeNat] at stackTape
  rw [args.base, capacityNat, Nat.mul_comm p.capacity 8] at stackScratch
  have reserved : s.sp.setWidth 64 - 184#64 = State.addr (s.sp - 184#32) := (FrameStack.addr_sub' stackFit).symm
  rw [reserved] at stackOut stackUsed stackTape stackScratch stackArgs
  have fit128 : 128 ≤ s.sp.toNat := by omega
  have sub128 := FrameStack.belowA_sub (sp := s.sp) (a := 128) (b := 184) (by decide) stackFit
  have localsSub : (⟨State.addr (entered s).sp, 72⟩ : Region).Sub (FrameStack.belowA s.sp 184) :=
    fun x hx => sub128 x (locals_sub_reserved s fit128 x hx)
  have savedSub : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Sub (FrameStack.belowA s.sp 184) :=
    fun x hx => sub128 x (saved_sub_reserved s fit128 x hx)
  have belowSub : (FrameStack.belowA (entered s).sp 56).Sub (FrameStack.belowA s.sp 184) := by
    rw [entered_sp]
    exact FrameStack.belowA_inner (by decide) stackFit
  have workspace : Workspace s p.base (8 * p.capacity) := ⟨p.scratchFits, by rw [wr]; simp [State.addr]⟩
  have tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length :=
    ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have start : CandidateStart p (entered s) := by
    refine ⟨⟨?_, List.mem_cons_self⟩, entered_workspace workspace, ?_, ?_, entered_read tapeRead, ?_, ?_,
      stackOut.sub_left localsSub, stackUsed.sub_left localsSub, stackScratch.sub_left localsSub, stackTape.sub_left localsSub,
      stackOut.sub_left belowSub, stackUsed.sub_left belowSub, stackScratch.sub_left belowSub, stackTape.sub_left belowSub⟩
    · rw [entered_nat s fit128]; have := s.sp.isLt; omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [wr]; simp [State.addr])), Region.contains_self _ _⟩
    · refine (rsa_bytes_frame (entered_frame s fit128) (by have := p.tapeCount; omega) ?_).trans args.bytes
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact stackTape.symm.sub_right savedSub
    · rw [entered_nat s fit128]; omega
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) := VG.Arm.addr_add (by omega)
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]
    exact Offset.sub_base _ (by omega)
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s fit128 (by omega)
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega) (by omega)⟩
      ((stackArgs.sub_left sub128).sub_right (argSub i hi)) rfl
  have nativeIncoming : CandidateIncoming p (entered s) := by
    refine ⟨?_⟩
    intro i hi
    have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [candidateIncomingValue]
    · rw [← args.generator]; exact incoming 0 (by decide)
    · rw [← args.tape]; exact incoming 1 (by decide)
    · rw [← args.tapeLength]; exact incoming 2 (by decide)
    · rw [← args.base]; exact incoming 3 (by decide)
    · rw [← args.capacity]; exact incoming 4 (by decide)
  refine ⟨stackFit, start, nativeIncoming, args.out, args.width, args.used, args.bits, ?_⟩
  intro r hr
  simp only [candidateEnteredRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact stackOut.sub_left savedSub
  · exact stackUsed.sub_left savedSub
  · exact stackScratch.sub_left savedSub
  · exact saved_separate_locals s fit128
  · have shift : (pcPushed s).sp = (entered s).sp + 72#32 := (BitVec.sub_add_cancel _ _).symm
    have room : (entered s).sp.toNat + 72 < 2 ^ 32 := by rw [entered_nat s fit128]; have := s.sp.isLt; omega
    rw [shift, VG.Arm.addr_add room, FrameStack.belowA, FrameStack.addr_sub' start.stackBelow]
    exact (Offset.disjoint_below_above _ (m := 56) (a := 72) (l := 56) (by decide)).symm

end VG.Proof.Ffdh.Arm.ParameterCandidate
