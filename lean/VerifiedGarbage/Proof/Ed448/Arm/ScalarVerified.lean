import VerifiedGarbage.Proof.Ed448.Arm.ScalarMain
import VerifiedGarbage.Proof.Ed448.Arm.ScalarMulAddMain
import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 scalar arithmetic on ARMv7: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses. A concrete witness proves the
signature contract is satisfiable.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm

def scalarReduceSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct (ReducePre.of hs)

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `r2`): the output's address, at `OUT`. -/
def scalarReduceTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [57, 8192], bases := [(.r2, 1)] }

theorem scalarReduceTaint_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.Arm.Taint.Wf scalarReduceTaint s := by
  have hp := ReducePre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarReduceTaint], ?_, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f2
  · intro p hm
    simp only [scalarReduceTaint, List.mem_singleton] at hm
    subst hm
    simp [VG.Arm.Taint.region, hp.wr]

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) scalarReduceTaint ?_ (by taint_decide)
  intro s t hs ht ⟨_, h0, h1, h2⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarReduceTaint_wf hs,
    scalarReduceTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [scalarReduceTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  · rw [(ReducePre.of hs).wr, (ReducePre.of ht).wr, h0, h2]

theorem scalarReduce_verified : Verified Arm.target scalarReduce
    (Spec.Ed448.scalarReduceContract Arm.abi) :=
  Verified.of_correct scalarReduce_ok scalarReduce_ct (by
    sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
      Spec.Ed448.scratchWords, scalarReduceLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [scalarReduceSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scalarReduceSat)

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct (MulAddPre.of hs)

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, whose address is the stack argument): the
arguments' addresses, from `OUT`. -/
def scalarMulAddTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [57, 8192],
    argLen := 4, argBases := [(0, 1)] }

theorem scalarMulAddTaint_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.Arm.Taint.Wf scalarMulAddTaint s := by
  have hp := MulAddPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarMulAddTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.fsp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.fs
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.out_args.symm
    · exact hp.ws_args.symm
  · intro p hm
    simp only [scalarMulAddTaint, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem scalarMulAdd_argByte (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) scalarMulAddTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarMulAddTaint_wf hs,
    scalarMulAddTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [scalarMulAddTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rw [(MulAddPre.of hs).wr, (MulAddPre.of ht).wr, h0, ha]
  · rw [scalarMulAdd_argByte, scalarMulAdd_argByte, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

def scalarMulAddSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else 0
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 57⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_verified : Verified Arm.target scalarMulAdd
    (Spec.Ed448.scalarMulAddContract Arm.abi) :=
  Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (by
    sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
      Spec.Ed448.scratchWords, scalarMulAddLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [scalarMulAddSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scalarMulAddSat)

end VG.Proof.Ed448.Arm
