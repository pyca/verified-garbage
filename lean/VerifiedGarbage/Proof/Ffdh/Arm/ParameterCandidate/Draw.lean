module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
import VerifiedGarbage.Impl.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.BelowP
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperand
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.TwoPower
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag

/-! ### `Ffdh.Arm.ParameterCandidate.OnPass`, which this module and modules that import it used -/

section

/-! Count successful witnesses, stopping exactly at the phase's policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem passHead_ok {s : State} {passed checks : Nat} (stack : Workspace s s.sp 72)
    (more : passed < checks) (bound : checks ≤ 128)
    (savedPassed : s.mem.readW (State.addr (s.sp + 56#32)) 32 = BitVec.ofNat 32 passed)
    (savedChecks : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 checks) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 (passed + 1) ∧ t.z = decide (passed + 1 = checks) ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2] s t := by
  have reads (d : Nat) (fit : d + 4 ≤ 72) : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [fit, this])]
    exact stack.read fit
  have increment : BitVec.ofNat 32 passed + 1 = BitVec.ofNat 32 (passed + 1) := by
    change BitVec.ofNat 32 passed + BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_add_ofNat _ _
  have zero : (BitVec.ofNat 32 (passed + 1) - BitVec.ofNat 32 checks == 0) = decide (passed + 1 = checks) :=
    (sub_beq_zero _ _).trans (ofNat_beq_eq (by omega_using [more, bound]) (by omega_using [bound]))
  refine withRest_all [.r1, .r2] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead
  ffrun [BitVec.add_zero, reads 56 (by decide), reads 52 (by decide), savedPassed, savedChecks, increment, zero]

private theorem passChoice_ok {s : State} {passed checks : Nat} (zero : s.z = decide (passed + 1 = checks)) :
    WP isa (.ite .eq (.block [.mov .r3 (.imm 1)]) (.block [.mov .r3 (.imm 4)])) s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (if passed + 1 = checks then 1 else 4) ∧ t.mem = s.mem ∧ Rest [.r3] s t := by
  by_cases done : passed + 1 = checks
  · refine WP.ite true (by change some s.z = some true; simp only [zero, done, decide_true]) ?_ (by intro h; cases h)
    intro _
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    refine ⟨?_, u.mem, u.rest (by simp)⟩
    simp only [done, ite_true]
    exact u.gpr
  · refine WP.ite false (by change some s.z = some false; simp only [zero, done, decide_false]) (by intro h; cases h) ?_
    intro _
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    refine ⟨?_, u.mem, u.rest (by simp)⟩
    simp only [done, ite_false]
    exact u.gpr

private theorem passFinish_ok {s : State} (stack : Workspace s s.sp 72) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (s.gpr .r1) ∧ t.z = (s.gpr .r3 == 4)) ∧ Rest [.r12] s t := by
  have write : InRegions s.wr (State.addr (s.sp + 56#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.write (by decide)
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, write]
  exact sub_beq_zero _ _

theorem onPass_ok {s : State} {passed checks : Nat} (stack : Workspace s s.sp 72)
    (more : passed < checks) (bound : checks ≤ 128)
    (savedPassed : s.mem.readW (State.addr (s.sp + 56#32)) 32 = BitVec.ofNat 32 passed)
    (savedChecks : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 checks) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.onPass s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (BitVec.ofNat 32 (passed + 1)) ∧
        t.gpr .r3 = BitVec.ofNat 32 (if passed + 1 = checks then 1 else 4) ∧
        t.z = decide (passed + 1 ≠ checks)) ∧ Rest [.r1, .r2, .r3, .r12] s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.onPass, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (passHead_ok stack more bound savedPassed savedChecks) ?_)
  rintro u ⟨⟨valueU, zeroU, memU⟩, restU⟩
  refine WP.seq (WP.mono (passChoice_ok zeroU) ?_)
  rintro v ⟨valueV, memV, restV⟩
  have restUV : Rest [.r1, .r2, .r3] s v := (restU.mono (by simp)).trans (restV.mono (by simp))
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  refine WP.seq (WP.mono (passFinish_ok stackV) ?_)
  rintro t ⟨⟨memT, zeroT⟩, restT⟩
  refine WP.block_nil ⟨⟨?_, (restT.gpr .r3 (by simp)).trans valueV, ?_⟩,
    (restUV.mono (by simp)).trans (restT.mono (by simp))⟩
  · rw [memT, restV.gpr .r1 (by simp), valueU, memV, memU, restUV.sp]
  · rw [zeroT, valueV]
    by_cases done : passed + 1 = checks <;> simp [done]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.RoundKernel`, which this module and modules that import it used -/

section

/-! Convert the sampled witness using RSA's Montgomery encoder, then call
the same selected compact-window primality kernel that RSA uses. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/RoundCall.lean`, which only this module imported.
section

/-! Call the existing RSA/shared compact Miller–Rabin implementation with
its exact selected name and body, and its existing 56-byte stack bound. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt wOf)
open VG.Proof.MillerRabin.Arm (RoundImpl LayoutLite PreparedLite KeepsLite roundPre roundPost)

theorem sharedRoundCall_ok (v : RoundImpl) {s : State} {base : BitVec 32} {capacity w witness : Nat}
    (workspace : Workspace s base (8 * capacity))
    (ptr : s.gpr .r0 = base) (length : s.gpr .r1 = BitVec.ofNat 32 capacity)
    (capacityBound : capacity < 2 ^ 32)
    (width : wOf s.mem (State.addr base) = w)
    (layout : LayoutLite s.mem (State.addr base) capacity) (prepared : PreparedLite s.mem (State.addr base))
    (stack : 56 ≤ s.sp.toNat)
    (separate : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (encoded : numAt s.mem (State.addr base) w 5 =
      witness % numAt s.mem (State.addr base) w 0 * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0) :
    WP isa (.call v.name v.code) s fun t =>
      (t.gpr .r0).toNat = (if Proof.MillerRabin.Round.round (numAt s.mem (State.addr base) w 0) witness then 1 else 0) ∧
      KeepsLite (State.addr base) capacity w s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have r0entry : (s.callEntry.withRegions [] [⟨State.addr base, 8 * capacity⟩]).gpr .r0 = base := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), ptr]
  have r1entry : (s.callEntry.withRegions [] [⟨State.addr base, 8 * capacity⟩]).gpr .r1 =
      BitVec.ofNat 32 capacity := by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), length]
  have capValue : (BitVec.ofNat 32 capacity).toNat = capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt capacityBound]
  have pre : roundPre (s.callEntry.withRegions [] [⟨State.addr base, 8 * capacity⟩]) := by
    unfold roundPre
    rw [r0entry, r1entry, capValue]
    exact ⟨rfl, rfl, workspace.nowrap, stack, separate, layout, prepared⟩
  have covers : Covers [⟨State.addr base, 8 * capacity⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_, workspace.writable, 0, by simp, by simp⟩
  refine FrameStack.WP.callF v.verified.1 pre covers.right covers (by have := v.stack; omega)
    fun t rd wr sp frame _ post => ?_
  change roundPost _ _ at post
  unfold roundPost at post
  rw [r0entry, r1entry, capValue] at post
  simp only [State.withRegions_mem, State.callEntry_mem, width] at post
  refine ⟨post.1 witness encoded, post.2, ?_, ?_⟩
  · refine frame.sub ?_
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, FrameStack.belowA_sub v.stack stack⟩
  · refine ⟨?_, rd, wr, sp⟩
    intro r hr
    cases r <;> simp [roundClobbers] at hr

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem roundArgs_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (ready : ArithmeticReady base capacity w s) (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 capacity) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r1 36]) s fun t =>
      (t.gpr .r0 = base ∧ t.gpr .r1 = BitVec.ofNat 32 capacity ∧ t.mem = s.mem) ∧ Rest [.r0, .r1] s t := by
  have read36 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 36#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.read (by decide)
  refine withRest_all [.r0, .r1] ?_ (by rfl) (by rfl)
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
      (t.gpr .r0).toNat = (if Proof.MillerRabin.Round.round n witness then 1 else 0) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have operand (j : Nat) (member : j = 1 ∨ j = 5) : Operand j := by
    rcases member with rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (montEncode_ok s ready (operand 5 (by simp)) (operand 1 (by simp)) (by decide)
    data.modulus data.odd data.r2) ?_)
  rintro u ⟨readyU, modulusU, encodedU, keepsU, frameU, restU⟩
  rw [input] at encodedU
  have dataU := data.after_operand (by decide) (by decide) (by decide) keepsU
  have stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  have savedU : u.mem.readW (State.addr (u.sp + 36#32)) 32 = BitVec.ofNat 32 capacity := by
    have separate : (⟨State.addr (s.sp + 36#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
      rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
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
    exact Nat.mod_lt _ (by have := data.large; omega_using [this]))
  refine WP.seq (WP.mono (sharedRoundCall_ok v workspaceA ptrA lengthA
    (by have := ready.workspace.nowrap; omega_using [this]) dataA.data.width dataA.layout preparedA
    (by rw [restA.sp, restU.sp]; exact stackBelow)
    (by rw [restA.sp, restU.sp]; exact belowSep) encodedA) ?_)
  rintro t ⟨flagT, keepsT, frameT, restT⟩
  rw [dataA.modulus] at flagT
  have dataT := dataA.after_round keepsT
  rw [memA, restA.sp, restU.sp] at frameT
  exact WP.block_nil ⟨dataT, flagT, (frameU.mono (by simp)).trans frameT, restU.trans (restUA.trans restT)⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.DrawRange`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.DrawSample`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessMaskBits`, which this module and modules that import it used -/

section

/-! Reuse RSA's fixed-step masked shifts for a full native-word witness
mask, including n=32, without shifting a native register by its width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem witnessMaskBits_ok {s : State} {bits : Nat} (bound : bits ≤ 32)
    (count : s.gpr .r6 = BitVec.ofNat 32 bits) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (2 ^ bits - 1) ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r7] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits, WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun u move => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Bignum.Arm.TwoPower.code_ok u) ?_
  rintro v ⟨value, memV, restV⟩
  rw [move.gpr, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound] : bits < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [bound] : bits < 64)] at value
  have low : v.gpr .r2 = BitVec.ofNat 32 (2 ^ bits) := by
    apply BitVec.eq_of_toNat_eq
    have reduced := congrArg (fun n => n % 2 ^ 32) value
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (v.gpr .r2).isLt] at reduced
    exact reduced
  refine wp_dp (op2_imm (by decide)) fun t subtract => WP.block_nil ?_
  refine ⟨?_, subtract.mem.trans (memV.trans move.mem),
    (move.rest (by simp)).trans ((restV.mono (by simp)).trans (subtract.rest (by simp)))⟩
  rw [subtract.gpr, dpVal, low]
  change BitVec.ofNat 32 (2 ^ bits) - BitVec.ofNat 32 1 = _
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (Nat.two_pow_pos bits)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessMaskHead`, which this module and modules that import it used -/

section

/-! Locate the occupied native witness word and its exact bit count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem witness_geometry {bits w : Nat} (positive : 0 < bits) (bound : bits ≤ 64 * w) :
    (bits - 1) / 32 < 2 * w ∧ (bits - 1) % 32 + 1 ≤ 32 ∧
      32 * ((bits - 1) / 32) + ((bits - 1) % 32 + 1) = bits ∧
      8 * ((bits + 7) / 8) ≤ 32 * ((bits - 1) / 32 + 1) := by omega_using [positive, bound]

private theorem nativeIndex {bits : Nat} (bound : bits ≤ 8192) :
    BitVec.ofNat 32 (bits - 1) >>> 5 = BitVec.ofNat 32 ((bits - 1) / 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound] : bits - 1 < 2 ^ 32),
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound] : (bits - 1) / 32 < 2 ^ 32)]

private theorem nativeCount {bits : Nat} (bound : bits ≤ 8192) :
    (BitVec.ofNat 32 (bits - 1) &&& 31) + 1 = BitVec.ofNat 32 ((bits - 1) % 32 + 1) := by
  have mask : BitVec.ofNat 32 (bits - 1) &&& 31 = BitVec.ofNat 32 ((bits - 1) % 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [bound] : bits - 1 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [] : (bits - 1) % 32 < 2 ^ 32)]
    change (bits - 1) &&& (2 ^ 5 - 1) = _
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  rw [mask]
  change BitVec.ofNat 32 ((bits - 1) % 32) + BitVec.ofNat 32 1 = _
  exact BitVec.ofNat_add_ofNat _ _

theorem witnessMaskHead_ok {s : State} {bits : Nat} (stack : Workspace s s.sp 72)
    (positive : 0 < bits) (bound : bits ≤ 8192)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 32 ((bits - 1) / 32) ∧
        t.gpr .r6 = BitVec.ofNat 32 ((bits - 1) % 32 + 1) ∧ t.mem = s.mem) ∧ Rest [.r5, .r6] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 44#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.read (by decide)
  have sub : BitVec.ofNat 32 bits - 1 = BitVec.ofNat 32 (bits - 1) := by
    change BitVec.ofNat 32 bits - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  refine withRest_all [.r5, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskHead
  ffrun [BitVec.add_zero, read, saved, sub, nativeIndex bound, nativeCount bound]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessTape`, which this module and modules that import it used -/

section

/-! A phase draws exactly the next prefix of its public entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

private theorem sourceAddress {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    State.addr (p.tape + BitVec.ofNat 32 offset) = off (State.addr p.tape) offset :=
  VG.Arm.addr_add (by have := h.tapeFits; have := h.bitsPositive; omega_arith)

theorem WitnessState.source_fits {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    (p.tape + BitVec.ofNat 32 offset).toNat + (p.bits + 7) / 8 ≤ 2 ^ 32 := by
  have start : p.tape.toNat + offset < 2 ^ 32 := by have := h.tapeFits; have := h.bitsPositive; omega_arith
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [start] : offset < 2 ^ 32), Nat.mod_eq_of_lt start]
  have := h.tapeFits
  omega_using [enough, this]

theorem WitnessState.source_read {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    InRegions (s.rd ++ s.wr) (State.addr (p.tape + BitVec.ofNat 32 offset)) ((p.bits + 7) / 8) := by
  rw [sourceAddress h enough]
  exact VG.CallLay.inRegions_sub h.tapeRead enough (by have := h.tapeCount; omega_using [this])

theorem WitnessState.source_separate {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    (⟨State.addr (p.tape + BitVec.ofNat 32 offset), (p.bits + 7) / 8⟩ : Region).Disjoint
      ⟨State.addr p.base, 8 * p.capacity⟩ := by
  rw [sourceAddress h enough]
  exact h.tapeScratch.sub_left (Offset.sub_base _ enough)

theorem WitnessState.source_bytes {s : State} {p : WitnessParams} {used passed offset : Nat}
    (h : WitnessState p used passed s) (enough : offset + (p.bits + 7) / 8 ≤ p.bytes.length) :
    Spec.Rsa.bytesAt s.mem (State.addr (p.tape + BitVec.ofNat 32 offset)) ((p.bits + 7) / 8) =
      (p.bytes.drop offset).take ((p.bits + 7) / 8) := by
  rw [sourceAddress h enough, ← VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.tape) enough, h.tapeBytes]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessMemory`, which this module and modules that import it used -/

section

/-! Reconstruct arithmetic arguments from saved phase state and retain that
state across calls to the shared primality machinery. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/RoundStack.lean`, which only this module imported.
section

/-! The shared Miller–Rabin call writes below the caller's saved arguments. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SavedFrame.after_round {s t : State} {base : BitVec 32} {capacity : Nat}
    {values : Nat → BitVec 32} {slots : List Nat} {rs : List Reg}
    (h : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (stackBelow : 56 ≤ s.sp.toNat)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have fit := bounds d hd
  rcases hr with rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ fit)
  · change (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
    rw [VG.Arm.addr_add (by have := h.space.nowrap; omega), FrameStack.addr_sub' stackBelow]
    exact Offset.disjoint_below _ (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem WitnessState.ready {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (ptr : s.gpr .r0 = p.base) :
    ArithmeticReady p.base p.capacity p.words s := by
  refine h.data.data.ready h.workspace ptr ?_
    (h.stackScratch.sub_left (Region.sub_prefix (by decide : 4 ≤ 72))) ?_
  · simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)
  · have saved := h.saved.saved 0 (by simp [witnessSlots])
    simpa only [BitVec.add_zero, witnessValues] using saved

theorem WitnessState.after_round {s t : State} {p : WitnessParams} {used passed : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (data : RoundData p.base p.capacity p.words p.modulus t.mem)
    (changed : Frame [⟨State.addr p.base, 8 * p.capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs s t) : WitnessState p used passed t :=
  h.after_frame data (h.saved.after_round (fun _ hd => witnessSlots_bound hd) h.stackBelow h.stackScratch changed rest)
    h.usedBound h.passedBound (changed.mono (by simp [witnessRegions])) rest

theorem WitnessState.after_workspace {s t : State} {p : WitnessParams} {used passed : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (data : RoundData p.base p.capacity p.words p.modulus t.mem)
    (changed : Frame [⟨State.addr p.base, 8 * p.capacity⟩] s.mem t.mem) (rest : Rest rs s t) :
    WitnessState p used passed t := h.after_round data (changed.mono (by simp)) rest

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.DrawHead`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessLocals`, which this module and modules that import it used -/

section

/-! The witness controller changes only its consumed-byte and passed-round counts. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/LocalStore.lean`, which only this module imported.
section

/-! Update one saved native policy word while retaining the other arguments. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SavedFrame.after_store {s t : State} {values : Nat → BitVec 32} {slots : List Nat}
    {offset : Nat} {value : BitVec 32} {rs : List Reg} (h : SavedFrame values slots s)
    (fit : offset + 4 ≤ 72) (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (separate : ∀ d ∈ slots, d ≠ offset → d + 4 ≤ offset ∨ offset + 4 ≤ d)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 offset)) value)
    (rest : Rest rs s t) :
    SavedFrame (fun d => if d = offset then value else values d) slots t := by
  refine ⟨?_, ?_⟩
  · rw [rest.sp]
    exact h.space.congr rest.wr
  · intro d hd
    rw [rest.sp, memory]
    by_cases same : d = offset
    · subst d
      rw [Mem.readW_writeW_self32, ite_eq_left rfl]
    · have disjoint : (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
          ⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩ := by
        rw [VG.Arm.addr_add (by have := h.space.nowrap; have := bounds d hd; omega),
          VG.Arm.addr_add (by have := h.space.nowrap; omega)]
        exact Offset.disjoint _ (separate d hd same) (by have := bounds d hd; omega) (by omega)
      rw [Mem.readW_writeW_sep (disjoint.sep (Region.contains_self _ 4) (Region.contains_self _ 4)) (by decide),
        ite_eq_right same]
      exact h.saved d hd

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/RoundMemory.lean`, which only this module imported.
section

/-! Local controller stores leave all shared primality constants unchanged. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem RoundData.after_workspaceEq {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m) (equal : WorkspaceEq (VG.Arm.State.addr base) (8 * capacity) m m') :
    RoundData base capacity w n m' := by
  have headerFits : 128 ≤ 8 * capacity := Nat.le_trans (by
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega : 128 ≤ arrAt w 28) h.fits
  refine h.after_reads (fun _ fit => equal.word (bits := 64) (by omega)) ?_ ?_
  · intro q member
    have bound : q < 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    have arrayFits := Nat.le_trans (array_end_le (w := w) bound) h.fits
    unfold numAt
    rw [equal.read (arrAt w q) (8 * w) (by omega)]
  · have arrayFits := Nat.le_trans (array_end_le (w := w) (j := 27) (k := 28) (by decide)) h.fits
    exact equal.word (bits := 64) (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

private theorem values_used (p : WitnessParams) (used passed next : Nat) :
    (fun d => if d = 40 then BitVec.ofNat 32 next else witnessValues p used passed d) =
      witnessValues p next passed := by
  funext d
  by_cases same : d = 40
  · subst d; simp [witnessValues]
  · rw [ite_eq_right same]
    unfold witnessValues
    split <;> simp_all

private theorem values_passed (p : WitnessParams) (used passed next : Nat) :
    (fun d => if d = 56 then BitVec.ofNat 32 next else witnessValues p used passed d) =
      witnessValues p used next := by
  funext d
  by_cases same : d = 56
  · subst d; simp [witnessValues]
  · rw [ite_eq_right same]
    unfold witnessValues
    split <;> simp_all

private theorem storeLocal {s t : State} {p : WitnessParams} {used passed nextUsed nextPassed offset : Nat}
    {value : BitVec 32} {rs : List Reg} (h : WitnessState p used passed s)
    (slot : offset = 40 ∨ offset = 56)
    (values : (fun d => if d = offset then value else witnessValues p used passed d) =
      witnessValues p nextUsed nextPassed)
    (usedBound : nextUsed ≤ p.bytes.length) (passedBound : nextPassed ≤ p.checks)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 offset)) value)
    (rest : Rest rs s t) : WitnessState p nextUsed nextPassed t := by
  have fit : offset + 4 ≤ 72 := by rcases slot with rfl | rfl <;> decide
  have saved := h.saved.after_store fit (fun _ hd => witnessSlots_bound hd) (by
    intro d hd different
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases slot with rfl | rfl <;> omega_using [hd, different]) memory rest
  rw [values] at saved
  have data : RoundData p.base p.capacity p.words p.modulus t.mem := by
    rw [memory]
    exact h.data.after_workspaceEq (stackWrite_workspaceEq h.workspace h.saved.space h.stackScratch fit value)
  have changed : Frame [⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩] s.mem t.mem := by
    rw [memory]
    exact (Frame.refl _ _).writeW (by simp) value (Region.contains_self _ _)
  exact h.after_frame data saved usedBound passedBound (changed.mono (by
    rcases slot with rfl | rfl <;> simp [witnessRegions])) rest

theorem WitnessState.store_used {s t : State} {p : WitnessParams} {used passed next : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (bound : next ≤ p.bytes.length)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + 40#32)) (BitVec.ofNat 32 next))
    (rest : Rest rs s t) : WitnessState p next passed t :=
  storeLocal h (.inl rfl) (values_used p used passed next) bound h.passedBound memory rest

theorem WitnessState.store_passed {s t : State} {p : WitnessParams} {used passed next : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (bound : next ≤ p.checks)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (BitVec.ofNat 32 next))
    (rest : Rest rs s t) : WitnessState p used next t :=
  storeLocal h (.inr rfl) (values_passed p used passed next) h.usedBound bound memory rest

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Load one witness prefix and consume its exact byte count in native code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem drawArgs_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.drawArgs) s fun t =>
      (t.gpr .r0 = p.base ∧ t.gpr .r4 = p.tape + BitVec.ofNat 32 used ∧
        t.gpr .r6 = BitVec.ofNat 32 ((p.bits + 7) / 8) ∧
        t.gpr .r1 = BitVec.ofNat 32 (used + (p.bits + 7) / 8) ∧ t.mem = s.mem) ∧
        Rest [.r0, .r1, .r4, .r6] s t := by
  have base : s.mem.readW (State.addr s.sp) 32 = p.base := by
    simpa only [BitVec.add_zero, witnessValues] using h.saved.saved 0 (by simp [witnessSlots])
  have tape : s.mem.readW (State.addr (s.sp + 16#32)) 32 = p.tape := by
    simpa only [witnessValues] using h.saved.saved 16 (by simp [witnessSlots])
  have usedWord : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used := by
    simpa only [witnessValues] using h.saved.saved 40 (by simp [witnessSlots])
  have width : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 ((p.bits + 7) / 8) := by
    simpa only [witnessValues] using h.saved.saved 48 (by simp [witnessSlots])
  refine withRest_all [.r0, .r1, .r4, .r6] ?_ (by rfl) (by rfl)
  have read0 : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.drawArgs
  ffrun [BitVec.add_zero, read0, h.saved.read (d := 16) (by decide), h.saved.read (d := 40) (by decide),
    h.saved.read (d := 48) (by decide), base, tape, usedWord, width, BitVec.ofNat_add_ofNat]

theorem drawHead_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) passed t ∧
      t.gpr .r0 = p.base ∧ t.gpr .r4 = p.tape + BitVec.ofNat 32 used ∧
      t.gpr .r6 = BitVec.ofNat 32 ((p.bits + 7) / 8) ∧
      Frame [⟨State.addr (s.sp + 40#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead
  refine WP.seq (WP.mono (drawArgs_ok h) ?_)
  rintro u ⟨⟨base, tape, width, usedWord, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  refine WP.mono (saveR1_ok ctx.saved.space (d := 40) (by decide)) ?_
  rintro t ⟨memoryT, restT⟩
  rw [usedWord] at memoryT
  have finalState := ctx.store_used enough memoryT restT
  refine ⟨finalState, (restT.gpr .r0 (by simp)).trans base, (restT.gpr .r4 (by simp)).trans tape,
    (restT.gpr .r6 (by simp)).trans width, ?_, (rest.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩
  rw [memoryT, memory, rest.sp]
  exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessMask`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessMaskStore`, which only this module used -/

section

/-! Apply a native mask to one occupied witness word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (arrAt)

theorem witnessMaskStore_ok {s : State} {base : BitVec 32} {capacity w j : Nat}
    (ready : ArithmeticReady base capacity w s) (bound : j < 2 * w)
    (index : s.gpr .r5 = BitVec.ofNat 32 j) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore) s fun t =>
      (t.mem = s.mem.writeW (off (State.addr base) (arrAt w 1 + 4 * j))
        (s.mem.readW (off (State.addr base) (arrAt w 1 + 4 * j)) 32 &&& s.gpr .r7) ∧
        t.gpr .r0 = base) ∧ Rest [.r0, .r3, .r4] s t := by
  have fits : arrAt w 8 ≤ 8 * capacity := ready.width ▸ ready.layout.2.2.1
  have arrayFit := array_end_le (w := w) (j := 1) (k := 8) (by decide)
  have size : 128 ≤ 8 * capacity := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have header := nativeHeader_of_layout s.mem base ready.workspace.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at header
  have pointer := header.array 1 (by decide)
  have addr72 : State.addr (base + 72#32) = off (State.addr base) 72 :=
    VG.Arm.addr_add (by have := ready.workspace.nowrap; omega_using [size, this])
  have shifted : BitVec.ofNat 32 j <<< 2 = BitVec.ofNat 32 (4 * j) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 j * BitVec.ofNat 32 4 = _
    rw [BitVec.ofNat_mul_ofNat, Nat.mul_comm]
  have address : State.addr (base + BitVec.ofNat 32 (arrAt w 1) + BitVec.ofNat 32 (4 * j)) =
      off (State.addr base) (arrAt w 1 + 4 * j) := by
    rw [Offset.add_add]
    exact VG.Arm.addr_add (by have := ready.workspace.nowrap; omega_using [bound, fits, arrayFit, this])
  have readHeader := ready.workspace.read (off := 72) (by omega_using [size])
  have read := ready.workspace.read (off := arrAt w 1 + 4 * j) (by omega_using [bound, fits, arrayFit])
  have write := ready.workspace.write (off := arrAt w 1 + 4 * j) (by omega_using [bound, fits, arrayFit])
  refine withRest_all [.r0, .r3, .r4] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskStore
  ffrun [BitVec.add_zero, ready.stackRead, ready.saved, addr72, readHeader, pointer,
    index, shifted, address, read, write]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Exact native witness truncation, using RSA's fixed-step word-mask
construction and the existing packed Montgomery operand. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/ParameterCandidate/WordCut32.lean`, which only this module imported.
section

/-! Cutting one occupied native word masks the complete packed integer,
including a partially occupied top word below the allocated width. -/

section
namespace VG.Proof.Ffdh.ParameterCandidate
open VG VG.Proof.Mont
open VG.Proof.Weierstrass (testBit_val32)

theorem testBit_mask32 {k : Nat} (bound : k ≤ 32) (i : Nat) :
    (BitVec.ofNat 32 (2 ^ k - 1)).toNat.testBit i = decide (i < k) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) bound
    have := Nat.two_pow_pos k
    omega), Nat.testBit_two_pow_sub_one]

theorem val32_cut {m m' : Mem} {base : Addr} {d w j k : Nat}
    (bits : k ≤ 32)
    (small : val32 m base d w < 2 ^ (32 * (j + 1)))
    (top : m'.readW (off base (d + 4 * j)) 32 =
      m.readW (off base (d + 4 * j)) 32 &&& BitVec.ofNat 32 (2 ^ k - 1))
    (other : ∀ i, i < w → i ≠ j →
      m'.readW (off base (d + 4 * i)) 32 = m.readW (off base (d + 4 * i)) 32) :
    val32 m' base d w = val32 m base d w % 2 ^ (32 * j + k) := by
  have topNat := congrArg BitVec.toNat top
  rw [BitVec.toNat_and] at topNat
  change w32 m' base (d + 4 * j) = w32 m base (d + 4 * j) &&& _ at topNat
  have otherNat (i : Nat) (bound : i < w) (different : i ≠ j) :
      w32 m' base (d + 4 * i) = w32 m base (d + 4 * i) :=
    congrArg BitVec.toNat (other i bound different)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases within : i < 32 * w
  · have index : i / 32 < w := by omega
    have bit : i % 32 < 32 := Nat.mod_lt _ (by decide)
    have split : i = 32 * (i / 32) + i % 32 := by omega
    have readNew := testBit_val32 m' base d w (i / 32) (i % 32) index bit
    have readOld := testBit_val32 m base d w (i / 32) (i % 32) index bit
    rw [← split] at readNew readOld
    rw [readNew]
    by_cases atTop : i / 32 = j
    · rw [atTop, topNat, Nat.testBit_and, testBit_mask32 bits]
      rw [readOld, atTop]
      have same : decide (i % 32 < k) = decide (i < 32 * j + k) := decide_eq_decide.mpr (by omega)
      rw [same, Bool.and_comm]
    · rw [otherNat (i / 32) index atTop, ← readOld]
      by_cases below : i / 32 < j
      · have keep : i < 32 * j + k := by omega
        simp only [keep, decide_true, Bool.true_and]
      · have high : 32 * (j + 1) ≤ i := by omega
        have zero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le small
          (Nat.pow_le_pow_right (by decide : 0 < 2) high))
        rw [zero]
        simp only [Bool.and_false]
  · have scale := Nat.pow_le_pow_right (by decide : 0 < 2) (show 32 * w ≤ i by omega)
    have oldZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m base d w) scale)
    have newZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m' base d w) scale)
    rw [oldZero, newZero]
    simp only [Bool.and_false]

end VG.Proof.Ffdh.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)

theorem witnessMask_ok {s : State} {base : BitVec 32} {capacity w bits : Nat}
    (ready : ArithmeticReady base capacity w s) (stack : Workspace s s.sp 72)
    (positive : 0 < bits) (bound : bits ≤ 8192) (fitsBits : bits ≤ 64 * w)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits)
    (small : numAt s.mem (State.addr base) w 1 < 2 ^ (32 * ((bits - 1) / 32 + 1))) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask s fun t =>
      ArithmeticReady base capacity w t ∧
      numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 % 2 ^ bits ∧
      Keeps (State.addr base) capacity w 1 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let j := (bits - 1) / 32
  let k := (bits - 1) % 32 + 1
  have geometry := witness_geometry positive fitsBits
  have jBound : j < 2 * w := geometry.1
  have kBound : k ≤ 32 := geometry.2.1
  have bitWidth : 32 * j + k = bits := geometry.2.2.1
  have fit : arrAt w 1 + 8 * (w + 2) ≤ 8 * capacity :=
    Nat.le_trans (array_end_le (w := w) (j := 1) (k := 8) (by decide)) (ready.width ▸ ready.layout.2.2.1)
  have nowrap := ready.workspace.nowrap
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMask, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (witnessMaskHead_ok stack positive bound saved) ?_)
  rintro u ⟨⟨indexU, countU, memU⟩, restU⟩
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  refine WP.seq (WP.mono (witnessMaskBits_ok kBound countU) ?_)
  rintro v ⟨maskV, memV, restV⟩
  have readyV := readyU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans readyU.ptr)
  have indexV : v.gpr .r5 = BitVec.ofNat 32 j := (restV.gpr .r5 (by simp)).trans indexU
  refine WP.seq (WP.mono (witnessMaskStore_ok readyV jBound indexV) ?_)
  rintro t ⟨⟨memT, ptrT⟩, restT⟩
  rw [maskV, memV, memU] at memT
  have outside := writeW32_outside s.mem (State.addr base)
    (s.mem.readW (off (State.addr base) (arrAt w 1 + 4 * j)) 32 &&& BitVec.ofNat 32 (2 ^ k - 1))
    (d := arrAt w 1 + 4 * j) (by omega_using [bound, fit, nowrap])
  rw [← memT] at outside
  have wide := outside.mono (o' := arrAt w 1) (n' := 8 * w) (by omega_using []) (by omega_using [geometry])
  have keeps := outside_array_keeps wide (len := capacity) (by omega_using [nowrap])
  have frame := outside_workspace wide (size := 8 * capacity) (by omega_using [fit])
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    ((restV.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers])))
  have value : numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 % 2 ^ bits := by
    rw [numAt_native, numAt_native, ← bitWidth]
    apply VG.Proof.Ffdh.ParameterCandidate.val32_cut kBound
    · rwa [← numAt_native]
    · rw [memT, Mem.readW_writeW_self32]
    · intro i bound different
      rw [memT, Mem.readW_writeW_sep (w := 32) (w' := 32)
        (Offset.sep _ (d := arrAt w 1 + 4 * i) (n := 4) (e := arrAt w 1 + 4 * j) (k := 4)
          (by omega_using [different]) (by omega_using [fit, nowrap, bound]) (by omega_arith)) (by decide)]
  exact WP.block_nil ⟨(ready.after_array (by decide) keeps frame rest ptrT).1, value, keeps, frame, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Draw, consume, import and mask one public witness prefix. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/SampleWitness.lean`, which only this module imported.
section

/-! Import a witness at its phase's byte width, then cut it to the exact
bit width, while preserving the shared-round constants. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt Keeps)

theorem sampleWitness_ok {s : State} {base src : BitVec 32} {capacity w n bits : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem)
    (stack : Workspace s s.sp 72)
    (stackSep : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (positive : 0 < bits) (bound : bits ≤ 8192) (fitsBits : bits ≤ 64 * w)
    (saved : s.mem.readW (State.addr (s.sp + 44#32)) 32 = BitVec.ofNat 32 bits)
    (sourceFit : src.toNat + (bits + 7) / 8 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) ((bits + 7) / 8))
    (sep : (⟨State.addr src, (bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 ((bits + 7) / 8)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sampleWitness s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem ∧
      numAt t.mem (State.addr base) w 1 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) ((bits + 7) / 8)) % 2 ^ bits ∧
      Keeps (State.addr base) capacity w 1 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.sampleWitness, WP.seq_iff]
  refine WP.mono (importOperand_ok s ready (o := 1) (by decide) (by decide)
    (by omega) (by omega) sourceFit read sep source count) ?_
  rintro u ⟨readyU, valueU, keepsU, frameU, restU⟩
  have stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  have savedU : u.mem.readW (State.addr (u.sp + 44#32)) 32 = BitVec.ofNat 32 bits := by
    have separate : (⟨State.addr (s.sp + 44#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
      rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
      exact stackSep.sub_left (Offset.sub_base _ (by decide : 44 + 4 ≤ 72))
    rw [restU.sp, frameU.readW (r := ⟨State.addr (s.sp + 44#32), 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)]
    exact saved
  have rawBound := VG.Proof.Bignum.os2ip_lt
    (Spec.Rsa.bytesAt s.mem (State.addr src) ((bits + 7) / 8))
  rw [VG.Proof.Bignum.bytesAt_length, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at rawBound
  have small : numAt u.mem (State.addr base) w 1 < 2 ^ (32 * ((bits - 1) / 32 + 1)) := by
    rw [valueU]
    exact Nat.lt_of_lt_of_le rawBound (Nat.pow_le_pow_right (by decide : 0 < 2)
      (witness_geometry positive fitsBits).2.2.2)
  refine WP.mono (witnessMask_ok readyU stackU positive bound fitsBits savedU small) ?_
  rintro t ⟨readyT, valueT, keepsT, frameT, restT⟩
  rw [valueU] at valueT
  have keeps : Keeps (State.addr base) capacity w 1 s.mem t.mem := fun i hi outside =>
    (keepsT i hi outside).trans (keepsU i hi outside)
  exact ⟨readyT, data.after_operand (by decide) (by decide) (by decide) keeps,
    valueT, keeps, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt)

def witnessValue (p : WitnessParams) (used : Nat) : Nat :=
  Spec.Rsa.os2ip ((p.bytes.drop used).take ((p.bits + 7) / 8)) % 2 ^ p.bits

theorem drawSample_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) passed t ∧ ArithmeticReady p.base p.capacity p.words t ∧
      numAt t.mem (State.addr p.base) p.words 1 = witnessValue p used ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample, WP.seq_iff]
  refine WP.mono (drawHead_ok h enough) ?_
  rintro u ⟨ctx, base, source, count, changed, rest⟩
  have bits : u.mem.readW (State.addr (u.sp + 44#32)) 32 = BitVec.ofNat 32 p.bits := by
    simpa only [witnessValues] using ctx.saved.saved 44 (by simp [witnessSlots])
  refine WP.mono (sampleWitness_ok (ctx.ready base) ctx.data ctx.saved.space ctx.stackScratch
    ctx.bitsPositive ctx.bitsBound ctx.bitsFit bits (ctx.source_fits enough) (ctx.source_read enough)
    (ctx.source_separate enough) source count) ?_
  rintro t ⟨readyT, dataT, value, _, changedT, restT⟩
  rw [ctx.source_bytes enough] at value
  exact ⟨ctx.after_workspace dataT changedT restT, readyT, value,
    (changed.mono (by simp [witnessRegions])).trans (changedT.mono (by simp [witnessRegions])), rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Rejection-sample the imported witness against the shared FFDH range check. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/InRange.lean`, which only this module imported.
section

/-! Reuse FFDH's existing witness range-check proof, strengthening it with
preservation of the shared primality round's extended-array constants. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

private theorem greaterOne_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (VG.Impl.Ffdh.Arm.greaterOne 1) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem := by
  rw [VG.Impl.Ffdh.Arm.greaterOne, WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 ready (o := 7) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, _, _, keepsU, _, _⟩
  have dataU := data.after_operand (by decide) (by decide) (by decide) keepsU
  refine WP.mono (compare_ok u readyU (a := 7) (b := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨readyT, _, keepsT, _, _⟩
  exact ⟨readyT, dataU.after_operand (by decide) (by decide) (by decide) keepsT⟩

private theorem saveFlag_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (.block VG.Impl.Ffdh.Arm.saveFlag) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem := by
  have size : 256 ≤ 8 * capacity :=
    Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (w + 2)))) data.fits
  unfold VG.Impl.Ffdh.Arm.saveFlag
  refine wp_str (a := off (State.addr base) 136) (by decide)
    (by rw [ready.ptr]; exact VG.Arm.addr_add (by have := ready.workspace.nowrap; omega))
    (ready.workspace.write (by omega)) fun t store => WP.block_nil ?_
  have rest : Rest [] s t := store.rest []
  have result := ready.after_header (d := 136) (by decide) (by decide) store.mem rest
    ((rest.gpr .r0 (by simp)).trans ready.ptr)
  refine ⟨result.1, ?_⟩
  rw [store.mem]
  exact data.after_aux_word (by decide) (by decide) _

private theorem belowP_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (VG.Impl.Ffdh.Arm.belowP 1) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem := by
  rw [VG.Impl.Ffdh.Arm.belowP, WP.seq_iff]
  refine WP.mono (VG.Proof.Ffdh.Arm.copy_ok s ready (o := 7) (a := 1) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, _, keepsU, _, _⟩
  have dataU := data.after_operand (by decide) (by decide) (by decide) keepsU
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Ffdh.Arm.setLowBit_ok u readyU) ?_
  rintro v ⟨readyV, _, keepsV, _, _⟩
  have dataV := dataU.after_operand (by decide) (by decide) (by decide) keepsV
  refine WP.mono (compare_ok v readyV (a := 7) (b := 0) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨readyT, _, keepsT, _, _⟩
  exact ⟨readyT, dataV.after_operand (by decide) (by decide) (by decide) keepsT⟩

private theorem inRange_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s fun t => RoundData base capacity w n t.mem := by
  rw [VG.Impl.Ffdh.Arm.inRange, WP.seq_iff]
  refine WP.mono (greaterOne_data ready data) ?_
  rintro u ⟨readyU, dataU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_data readyU dataU) ?_
  rintro v ⟨readyV, dataV⟩
  rw [WP.seq_iff]
  refine WP.mono (belowP_data readyV dataV) ?_
  rintro a ⟨readyA, dataA⟩
  refine WP.mono (VG.Proof.Ffdh.Arm.andFlag_ok a readyA) ?_
  rintro t ⟨⟨_, mem⟩, _⟩
  exact mem ▸ dataA

theorem inRangeWitness_ok {s : State} {base : BitVec 32} {capacity w n witness : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem)
    (input : numAt s.mem (State.addr base) w 1 = witness) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem ∧
      t.gpr .r11 = (if 1 < witness ∧ witness < n - 1 then 1 else 0) ∧
      numAt t.mem (State.addr base) w 1 = witness ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have operand : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono ((VG.Proof.Ffdh.Arm.inRange_ok s ready operand (by decide)
    (by rw [data.modulus]; exact data.odd)).and (inRange_data ready data)) ?_
  rintro t ⟨⟨readyT, flag, arrays, frame, rest⟩, dataT⟩
  rw [input, data.modulus] at flag
  exact ⟨readyT, dataT, flag, (arrays 1 operand (by decide)).trans input, frame, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt)

theorem drawRange_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) passed t ∧ ArithmeticReady p.base p.capacity p.words t ∧
      t.gpr .r11 = (if 1 < witnessValue p used ∧ witnessValue p used < p.modulus - 1 then 1 else 0) ∧
      numAt t.mem (State.addr p.base) p.words 1 = witnessValue p used ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange, WP.seq_iff]
  refine WP.mono (drawSample_ok h enough) ?_
  rintro u ⟨ctx, ready, value, changed, rest⟩
  refine WP.mono (inRangeWitness_ok ready ctx.data value) ?_
  rintro t ⟨readyT, dataT, flag, valueT, changedT, restT⟩
  exact ⟨ctx.after_workspace dataT changedT restT, readyT, flag, valueT,
    changed.trans (changedT.mono (by simp [witnessRegions])), rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.Round`, which only this module used -/

section

/-! The selected shared Miller–Rabin round updates native status and success count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.MillerRabin.Arm (RoundImpl)

def roundPassed (p : WitnessParams) (passed witness : Nat) : Nat :=
  if Spec.Ffdh.mrRound p.modulus witness then passed + 1 else passed

def roundStatus (p : WitnessParams) (passed witness : Nat) : Nat :=
  if Spec.Ffdh.mrRound p.modulus witness then (if passed + 1 = p.checks then 1 else 4) else 2

theorem round_ok (v : RoundImpl) {s : State} {p : WitnessParams} {used passed witness : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks)
    (ready : ArithmeticReady p.base p.capacity p.words s)
    (input : numAt s.mem (State.addr p.base) p.words 1 = witness) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.round v.name v.code) s fun t =>
      WitnessState p used (roundPassed p passed witness) t ∧
      t.gpr .r3 = BitVec.ofNat 32 (roundStatus p passed witness) ∧
      t.z = decide (roundStatus p passed witness = 4) ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have capacity : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.capacity := by
    simpa only [witnessValues] using h.saved.saved 36 (by simp [witnessSlots])
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.round VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (roundKernel_ok v ready h.data h.saved.space h.stackScratch capacity
    h.stackBelow h.belowScratch input) ?_)
  rintro u ⟨dataU, valueU, frameU, restU⟩
  have shared : Proof.MillerRabin.Round.round p.modulus witness = Spec.Ffdh.mrRound p.modulus witness := by
    simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq witness h.data.large h.data.odd
  rw [shared] at valueU
  have ctxU := h.after_round dataU frameU restU
  refine WP.seq (WP.mono (cmpResult_ok valueU) ?_)
  rintro a ⟨⟨zeroA, memA⟩, restA⟩
  have ctxA := ctxU.after_memory memA restA
  have through : Rest roundClobbers s a := restU.trans (restA.mono (by simp [roundClobbers]))
  have frameA : Frame (witnessRegions p s.sp) s.mem a.mem := by
    rw [memA]
    exact frameU.mono (by simp [witnessRegions])
  by_cases pass : Spec.Ffdh.mrRound p.modulus witness = true
  · refine WP.seq (WP.ite false (by change some a.z = some false; rw [zeroA, pass]; rfl)
      (by intro h; cases h) ?_)
    intro _
    have passedWord : a.mem.readW (State.addr (a.sp + 56#32)) 32 = BitVec.ofNat 32 passed := by
      simpa only [witnessValues] using ctxA.saved.saved 56 (by simp [witnessSlots])
    have checksWord : a.mem.readW (State.addr (a.sp + 52#32)) 32 = BitVec.ofNat 32 p.checks := by
      simpa only [witnessValues] using ctxA.saved.saved 52 (by simp [witnessSlots])
    refine WP.mono (onPass_ok ctxA.saved.space more h.checksBound passedWord checksWord) ?_
    rintro t ⟨⟨memT, statusT, zeroT⟩, restT⟩
    have stateT := ctxA.store_passed (by omega_using [more] : passed + 1 ≤ p.checks) memT restT
    have frameT : Frame [⟨State.addr (s.sp + 56#32), 4⟩] a.mem t.mem := by
      rw [memT, through.sp]
      exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    refine WP.block_nil ⟨?_, ?_, ?_, frameA.trans (frameT.mono (by simp [witnessRegions])),
      through.trans (restT.mono (by simp [roundClobbers]))⟩
    · simpa only [roundPassed, pass, ite_true] using stateT
    · simpa only [roundStatus, pass, ite_true] using statusT
    · rw [zeroT]
      apply decide_eq_decide.mpr
      by_cases done : passed + 1 = p.checks <;> simp [roundStatus, pass, done]
  · have fail : Spec.Ffdh.mrRound p.modulus witness = false := Bool.eq_false_iff.mpr pass
    refine WP.seq (WP.ite true (by change some a.z = some true; rw [zeroA, fail]; rfl)
      ?_ (by intro h; cases h))
    intro _
    refine WP.mono (setStatus_ok a 2 (by decide)) ?_
    rintro t ⟨⟨statusT, zeroT, memT⟩, restT⟩
    have stateT := ctxA.after_memory memT restT
    have frameT : Frame (witnessRegions p s.sp) s.mem t.mem := by rw [memT]; exact frameA
    refine WP.block_nil ?_
    simpa only [roundPassed, roundStatus, fail, Bool.false_eq_true, ite_false] using
      (show WitnessState p used passed t ∧ t.gpr .r3 = BitVec.ofNat 32 2 ∧ t.z = decide (2 = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT, through.trans (restT.mono (by simp [roundClobbers]))⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! One complete native witness draw: consume, reject or test, and update status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def drawPassed (p : WitnessParams) (passed used : Nat) : Nat :=
  if 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1 then
    roundPassed p passed (witnessValue p used) else passed

def drawStatus (p : WitnessParams) (passed used : Nat) : Nat :=
  if 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1 then
    roundStatus p passed (witnessValue p used) else 4

theorem draw_ok (v : RoundImpl) {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks)
    (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.draw v.name v.code) s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) (drawPassed p passed used) t ∧
      t.gpr .r3 = BitVec.ofNat 32 (drawStatus p passed used) ∧
      t.z = decide (drawStatus p passed used = 4) ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.draw VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (drawRange_ok h enough) ?_)
  rintro u ⟨ctxU, readyU, range, input, frameU, restU⟩
  have word : (u.gpr .r11).toNat =
      if decide (2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1) then 1 else 0 := by
    rw [range]
    by_cases valid : 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1
    · have valid' : 1 < witnessValue p used ∧ witnessValue p used < p.modulus - 1 := by omega_using [valid]
      simp only [ite_eq_left valid', decide_eq_true valid, ite_true]
      rfl
    · have invalid : ¬ (1 < witnessValue p used ∧ witnessValue p used < p.modulus - 1) := by omega_using [valid]
      simp only [ite_eq_right invalid, decide_eq_false valid, Bool.false_eq_true, ite_false]
      rfl
  refine WP.seq (WP.mono (cmpWord_ok .r11 word) ?_)
  rintro a ⟨⟨zeroA, memA⟩, restA⟩
  have ctxA := ctxU.after_memory memA restA
  have through : Rest roundClobbers s a := restU.trans (restA.mono (by simp [roundClobbers]))
  have frameA : Frame (witnessRegions p s.sp) s.mem a.mem := by rw [memA]; exact frameU
  by_cases valid : 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1
  · refine WP.seq (WP.ite false (by change some a.z = some false; rw [zeroA, decide_eq_true valid]; rfl)
      (by intro h; cases h) ?_)
    intro _
    have readyA := ctxA.ready ((restA.gpr .r0 (by simp)).trans readyU.ptr)
    refine WP.mono (round_ok v (witness := witnessValue p used) ctxA more readyA (by rw [memA]; exact input)) ?_
    rintro t ⟨stateT, statusT, zeroT, frameT, restT⟩
    rw [through.sp] at frameT
    refine WP.block_nil ?_
    simpa only [drawPassed, drawStatus, ite_eq_left valid] using
      (show WitnessState p (used + (p.bits + 7) / 8) (roundPassed p passed (witnessValue p used)) t ∧
        t.gpr .r3 = BitVec.ofNat 32 (roundStatus p passed (witnessValue p used)) ∧
        t.z = decide (roundStatus p passed (witnessValue p used) = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameA.trans frameT, through.trans restT⟩)
  · refine WP.seq (WP.ite true (by change some a.z = some true; rw [zeroA, decide_eq_false valid]; rfl)
      ?_ (by intro h; cases h))
    intro _
    refine WP.mono (setStatus_ok a 4 (by decide)) ?_
    rintro t ⟨⟨statusT, zeroT, memT⟩, restT⟩
    have stateT := ctxA.after_memory memT restT
    have frameT : Frame (witnessRegions p s.sp) s.mem t.mem := by rw [memT]; exact frameA
    refine WP.block_nil ?_
    simpa only [drawPassed, drawStatus, ite_eq_right valid] using
      (show WitnessState p (used + (p.bits + 7) / 8) passed t ∧ t.gpr .r3 = BitVec.ofNat 32 4 ∧
        t.z = decide (4 = 4) ∧ Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT, through.trans (restT.mono (by simp [roundClobbers]))⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
