module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundCall
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Convert the sampled witness using RSA's Montgomery encoder, then call
the same selected compact-window primality kernel that RSA uses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt Operand)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem roundArgs_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (ready : ArithmeticReady base capacity w s) (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 capacity) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r1 36]) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r1 = BitVec.ofNat 32 capacity ∧ t.mem = s.mem) ∧ Rest [.r0, .r1] s t := by
  have read36 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 36#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  refine withRest [.r0, .r1] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.ldrSp .r0 0, .ldrSp .r1 36] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  ffrun [BitVec.add_zero, ready.stackRead, ready.saved, read36, saved]

theorem roundKernel_ok (v : RoundImpl) {s : State} {base : BitVec 32} {capacity w n witness : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem)
    (stack : Workspace s s.sp 72)
    (stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 capacity)
    (stackBelow : 56 ≤ s.sp.toNat)
    (belowSep : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (input : numAt s.mem (State.addr base) w 1 = witness) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel v.name v.code) s fun t =>
      RoundData base capacity w n t.mem ∧
      (t.gpr .r0).toNat = (if Spec.MillerRabin.round n witness then 1 else 0) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have operand (j : Nat) (member : j = 1 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (montEncode_ok s ready (operand 5 (by simp)) (operand 1 (by simp)) (by decide)
    data.modulus data.odd data.r2) ?_)
  rintro u ⟨readyU, modulusU, encodedU, keepsU, frameU, restU⟩
  rw [input] at encodedU
  have dataU := data.after_operand (by decide) (by decide) (by decide) keepsU
  have stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  have savedU : u.mem.readW (State.addr (u.sp + 36#32)) 32 = BitVec.ofNat 32 capacity := by
    have separate : (⟨State.addr (s.sp + 36#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
      rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
      exact stackSep.sub_left (Offset.sub_base _ (by decide : 36 + 4 ≤ 72))
    rw [restU.sp, frameU.readW (r := ⟨State.addr (s.sp + 36#32), 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)]
    exact saved
  refine WP.seq (WP.mono (roundArgs_ok readyU stackU savedU) ?_)
  rintro a ⟨⟨ptrA, lengthA, memA⟩, restA⟩
  have workspaceA := readyU.workspace.congr restA.wr
  have dataA : RoundData base capacity w n a.mem := memA ▸ dataU
  have restUA : Rest roundClobbers u a := restA.mono (by simp [roundClobbers])
  have encodedA : numAt a.mem (State.addr base) w 5 = witness % numAt a.mem (State.addr base) w 0 *
      2 ^ (64 * w) % numAt a.mem (State.addr base) w 0 := by
    rw [dataA.modulus, memA, encodedU, Nat.mod_mul_mod]
  have preparedA := dataA.prepared (by
    rw [memA, encodedU]
    exact Nat.mod_lt _ (by have := data.large; omega))
  refine WP.seq (WP.mono (sharedRoundCall_ok v workspaceA ptrA lengthA
    (by have := ready.workspace.nowrap; omega) dataA.data.width dataA.layout preparedA
    (by rw [restA.sp, restU.sp]; exact stackBelow)
    (by rw [restA.sp, restU.sp]; exact belowSep) encodedA) ?_)
  rintro t ⟨flagT, keepsT, frameT, restT⟩
  rw [dataA.modulus] at flagT
  have dataT := dataA.after_round keepsT
  rw [memA, restA.sp, restU.sp] at frameT
  exact WP.block_nil ⟨dataT, flagT, (frameU.mono (by simp)).trans frameT, restU.trans (restUA.trans restT)⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
