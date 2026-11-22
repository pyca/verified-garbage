module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Bignum.OddDivision
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentStep
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Bignum.Arm.TwoPower
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits

/-! ### `Ffdh.Arm.ParameterCandidate.Room`, which this module and modules that import it used -/

section

/-! Native entropy guards compare unsigned byte counts without wrapping
the subtraction of bytes already consumed. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem geFlag_ok (s : State) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.geFlag) s fun t =>
      (t.z = decide ((s.gpr .r1).toNat < (s.gpr .r2).toNat) ∧ t.mem = s.mem) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.geFlag
  by_cases ge : (s.gpr .r2).toNat ≤ (s.gpr .r1).toNat
  · have lt : ¬ (s.gpr .r1).toNat < (s.gpr .r2).toNat := by omega_using [ge]
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]
  · have lt : (s.gpr .r1).toNat < (s.gpr .r2).toNat := by omega_using [ge]
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]

private theorem initialHead_ok {s : State} {length width : Nat} (stack : Workspace s s.sp 72)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block [.ldrSp .r1 20, .ldrSp .r2 12]) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 length ∧ t.gpr .r2 = BitVec.ofNat 32 width ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2] s t := by
  have reads (d : Nat) (fit : d + 4 ≤ 72) : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [fit, this])]
    exact stack.read fit
  refine withRest_all [.r1, .r2] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, reads 20 (by decide), reads 12 (by decide), savedLength, savedWidth]

theorem initialRoom_ok {s : State} {length width : Nat} (stack : Workspace s s.sp 72)
    (lengthBound : length < 2 ^ 32) (widthBound : width < 2 ^ 32)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) s fun t =>
      (t.z = decide (length < width) ∧ t.mem = s.mem) ∧ Rest [.r1, .r2, .r3] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom, WP.block_append_iff]
  refine WP.mono (initialHead_ok stack savedLength savedWidth) ?_
  rintro u ⟨⟨lenU, widthU, memU⟩, restU⟩
  refine WP.mono (geFlag_ok u) ?_
  rintro t ⟨⟨zeroT, memT⟩, restT⟩
  rw [lenU, widthU, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound,
    Nat.mod_eq_of_lt widthBound] at zeroT
  exact ⟨⟨zeroT, memT.trans memU⟩, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

private theorem witnessHead_ok {s : State} {length used width : Nat} (stack : Workspace s s.sp 72)
    (lengthBound : length < 2 ^ 32) (enough : used ≤ length)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedUsed : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used)
    (savedWidth : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block [.ldrSp .r1 20, .ldrSp .r2 40, .dp .sub .r1 .r1 (.reg .r2), .ldrSp .r2 48]) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 (length - used) ∧ t.gpr .r2 = BitVec.ofNat 32 width ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2] s t := by
  have reads (d : Nat) (fit : d + 4 ≤ 72) : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [fit, this])]
    exact stack.read fit
  have subtract : BitVec.ofNat 32 length - BitVec.ofNat 32 used = BitVec.ofNat 32 (length - used) := by
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [lengthBound, enough]) enough
  refine withRest_all [.r1, .r2] ?_ (by rfl) (by rfl)
  ffrun [BitVec.add_zero, reads 20 (by decide), reads 40 (by decide), reads 48 (by decide),
    savedLength, savedUsed, savedWidth, subtract]

theorem witnessRoom_ok {s : State} {length used width : Nat} (stack : Workspace s s.sp 72)
    (lengthBound : length < 2 ^ 32) (widthBound : width < 2 ^ 32) (enough : used ≤ length)
    (savedLength : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 length)
    (savedUsed : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used)
    (savedWidth : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 width) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom) s fun t =>
      (t.z = decide (length - used < width) ∧ t.mem = s.mem) ∧ Rest [.r1, .r2, .r3] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessRoom, WP.block_append_iff]
  refine WP.mono (witnessHead_ok stack lengthBound enough savedLength savedUsed savedWidth) ?_
  rintro u ⟨⟨lenU, widthU, memU⟩, restU⟩
  refine WP.mono (geFlag_ok u) ?_
  rintro t ⟨⟨zeroT, memT⟩, restT⟩
  rw [lenU, widthU, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [lengthBound] : length - used < 2 ^ 32),
    Nat.mod_eq_of_lt widthBound] at zeroT
  exact ⟨⟨zeroT, memT.trans memU⟩, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.PreparedWitness`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.ExponentSigma`, which this module and modules that import it used -/

section

/-! Select the shared compact Miller–Rabin kernel's shift in 1..=4. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero wp_mov op2_imm)

def countShift (count : Nat) : Nat := if count % 4 = 0 then 4 else count % 4

theorem countShift_bounds (count : Nat) : 0 < countShift count ∧ countShift count ≤ 4 := by
  unfold countShift
  split <;> omega_arith

private theorem maskCount (count : Nat) : BitVec.ofNat 32 count &&& 3 = BitVec.ofNat 32 (count % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  change (count % 2 ^ 32 &&& (2 ^ 2 - 1)) = (count % 4) % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd count (by decide : 4 ∣ 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [] : count % 4 < 2 ^ 32)]

theorem sigmaHead_ok {s : State} {count : Nat} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 (count % 4) ∧ t.z = decide (count % 4 = 0) ∧ t.mem = s.mem) ∧
      Rest [.r1] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.read (by decide)
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead
  ffrun [BitVec.add_zero, read, saved, maskCount count]
  change (_ - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact ofNat_beq_zero (by omega_using [] : count % 4 < 2 ^ 32)

private theorem sigmaChoice_ok {s : State} {count : Nat}
    (value : s.gpr .r1 = BitVec.ofNat 32 (count % 4)) (zero : s.z = decide (count % 4 = 0)) :
    WP isa (.ite .eq (.block [.mov .r1 (.imm 4)]) (.block [])) s fun t =>
      t.gpr .r1 = BitVec.ofNat 32 (countShift count) ∧ t.mem = s.mem ∧ Rest [.r1] s t := by
  by_cases divisible : count % 4 = 0
  · refine WP.ite true (by change some s.z = some true; simp only [zero, divisible, decide_true]) ?_
      (by intro h; cases h)
    intro _
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    refine ⟨?_, u.mem, u.rest (by simp)⟩
    simp only [countShift, divisible, ite_true]
    exact u.gpr
  · refine WP.ite false (by change some s.z = some false; simp only [zero, divisible, decide_false])
      (by intro h; cases h) ?_
    intro _
    exact WP.block_nil ⟨by simpa only [countShift, divisible, ite_false] using value, rfl, Rest.refl _ _⟩

theorem exponentSigma_ok {s : State} {count : Nat} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma s fun t =>
      t.mem = s.mem.writeW (State.addr (s.sp + 64#32)) (BitVec.ofNat 32 (countShift count)) ∧
      Rest [.r1, .r12] s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (sigmaHead_ok stack saved) ?_)
  rintro u ⟨⟨valueU, zeroU, memU⟩, restU⟩
  refine WP.seq (WP.mono (sigmaChoice_ok valueU zeroU) ?_)
  rintro v ⟨valueV, memV, restV⟩
  have restUV := restU.trans restV
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  refine WP.seq (WP.mono (saveR1_ok stackV (d := 64) (by decide)) ?_)
  rintro t ⟨memT, restT⟩
  exact WP.block_nil ⟨by rw [memT, valueV, memV, memU, restUV.sp],
    (restUV.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.Decompose`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CountInit`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CountStep`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.CountTail`, which only this module used -/

section

/-! Increment the native halving count and test the new exponent's low bit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Keys (num arr S)

theorem halfCountTail_ok {s : State} {base : BitVec 32} {capacity w count : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 60#32)) (BitVec.ofNat 32 (count + 1)) ∧
        t.z = decide (num s.mem (base + 96#32) (2 * w + 2) 29 % 2 = 0)) ∧
      Rest [.r0, .r1, .r12] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.read (by decide)
  have write : InRegions s.wr (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact stack.write (by decide)
  let B := base + 96#32
  let d := arr (2 * w + 2) 29
  have nativeAddr : State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
    ready.addr (by have := ready.arr_fit (j := 29) (by decide); simp only [S] at this; omega_using [this])
  have realRead : InRegions (s.rd ++ s.wr) (State.addr (B + BitVec.ofNat 32 d)) 4 := by
    rw [nativeAddr]
    rw [VG.Arm.addr_add (ready.baseShiftFits workspace)]
    unfold off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
    exact workspace.read (by have := ready.arrayFit (j := 29) (by decide); omega_using [this])
  have stackSep : (⟨State.addr (s.sp + 60#32), 4⟩ : Region).Disjoint
      ⟨State.addr (B + BitVec.ofNat 32 d), 4⟩ := by
    have a : State.addr (B + BitVec.ofNat 32 d) = off (State.addr base) (Proof.Rsa.Mont.arrAt w 29) := by
      rw [nativeAddr, VG.Arm.addr_add (ready.baseShiftFits workspace)]
      unfold off
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
    rw [a, VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72)) |>.sub_right
      (Offset.sub_base _ (by have := ready.arrayFit (j := 29) (by decide); omega_using [this]))
  have lowUnchanged : (s.mem.writeW (State.addr (s.sp + 60#32)) (BitVec.ofNat 32 (count + 1))).readW
      (State.addr (B + BitVec.ofNat 32 d)) 32 = s.mem.readW (State.addr (B + BitVec.ofNat 32 d)) 32 :=
    Mem.readW_writeW_sep stackSep.symm (by decide)
  have ptrValue : BitVec.ofNat 32 29 * BitVec.ofNat 32 (S (2 * w + 2)) + B + 160 = B + BitVec.ofNat 32 d :=
    VG.Proof.Rsa.Arm.Keys.ptr_val B 29 (S (2 * w + 2))
  change BitVec.ofNat 32 29 * BitVec.ofNat 32 (S (2 * w + 2)) + B +
    BitVec.ofNat 32 VG.Impl.Rsa.Arm.Keys.hdr = B + BitVec.ofNat 32 d at ptrValue
  have r7 : s.gpr .r7 = BitVec.ofNat 32 (S (2 * w + 2)) := ready.r7
  have r8 : s.gpr .r8 = B := ready.r8
  have plus : BitVec.ofNat 32 count + 1 = BitVec.ofNat 32 (count + 1) := by
    change BitVec.ofNat 32 count + BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_add_ofNat count 1
  have parity : (s.mem.readW (State.addr (B + BitVec.ofNat 32 d)) 32 &&& 1 == 0) =
      decide (num s.mem B (2 * w + 2) 29 % 2 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, VG.Proof.Rsa.Arm.Keys.bv_and_one, nativeAddr,
      ← VG.Proof.Rsa.Arm.Keys.num_mod2 s.mem B (by omega_using [] : 0 < 2 * w + 2)]
    rfl
  refine withRest_all [.r0, .r1, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail VG.Impl.Ffdh.Arm.ParameterCandidate.save
    VG.Impl.Rsa.Arm.Keys.ptr
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, saved, plus, r7, r8,
    ptrValue, realRead, lowUnchanged]
  change (_ - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  exact parity

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! One native exponent-halving iteration, with the exact count and parity. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)

private theorem zeroCarry (s : State) :
    WP isa (.block [.mov .r11 (.imm 0)]) s fun t =>
      t.gpr .r11 = 0#32 ∧ t.mem = s.mem ∧ Rest [.r11] s t := by
  refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
  exact ⟨u.gpr, u.mem, u.rest (by simp)⟩

theorem halfCountStep_ok {s : State} {base : BitVec 32} {capacity w count : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 29 = num s.mem (base + 96#32) (2 * w + 2) 29 / 2 ∧
      t.mem.readW (State.addr (t.sp + 60#32)) 32 = BitVec.ofNat 32 (count + 1) ∧
      t.z = decide (num s.mem (base + 96#32) (2 * w + 2) 29 / 2 % 2 = 0) ∧
      (∀ j, j < 30 → j ≠ 29 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩] s.mem t.mem ∧
      Rest opRegs s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (zeroCarry s) ?_)
  rintro u ⟨carryU, memU, restU⟩
  have readyU := ready.rest restU (by decide) (by decide) (by decide)
  have workspaceU := workspace.congr restU.wr
  refine WP.seq (WP.mono (keyHalf_ok workspaceU readyU (j := 29) (by decide) (by rw [carryU]; decide)) ?_)
  rintro v ⟨readyV, keepV, valueV, restV⟩
  rw [carryU, memU, show (0#32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at valueV
  have frameV := key_keep_workspace workspaceU readyU (by simp) keepV
  have dataV := (MontData.after_key_keep (by rw [memU]; exact data) workspaceU readyU
    (by simp) (by simp) keepV).1
  have restUV : Rest opRegs s v := (restU.mono (by simp [opRegs])).trans restV
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  have countSep : (⟨State.addr (s.sp + 60#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
  have countV : v.mem.readW (State.addr (v.sp + 60#32)) 32 = BitVec.ofNat 32 count := by
    rw [restUV.sp, frameV.readW (r := ⟨State.addr (s.sp + 60#32), 4⟩)
      (Region.contains_self _ _) (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact countSep) (by decide), memU]
    exact saved
  refine WP.seq (WP.mono (halfCountTail_ok (workspace.congr restUV.wr) readyV stackV countV
    (by rw [restUV.sp]; exact separate)) ?_)
  rintro t ⟨⟨memT, zeroT⟩, restT⟩
  have tailFrame : Frame [⟨State.addr (v.sp + 60#32), 4⟩] v.mem t.mem := by
    rw [memT]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have equal : WorkspaceEq (State.addr base) (8 * capacity) v.mem t.mem :=
    WorkspaceEq.of_frame (by have := workspace.nowrap; omega_using [this]) tailFrame (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [restUV.sp]
      exact countSep.symm)
  have numberT := (key_number_of_workspaceEq (workspace.congr restUV.wr) readyV equal (j := 29) (by decide)).trans valueV
  have rest := restUV.trans (restT.mono (by simp [opRegs]))
  have frameV' : Frame [⟨State.addr base, 8 * capacity⟩] s.mem v.mem := by rw [← memU]; exact frameV
  refine WP.block_nil ⟨readyV.rest restT (by decide) (by decide) (by decide), dataV.after_workspaceEq equal,
    numberT, ?_, ?_, ?_, ?_, (frameV'.mono (by simp)).trans (tailFrame.mono (by simp only [restUV.sp]; simp)), rest⟩
  · rw [restT.sp, memT, Mem.readW_writeW_self32]
  · rw [valueV] at zeroT
    exact zeroT
  · intro j bound different
    rw [key_number_of_workspaceEq (workspace.congr restUV.wr) readyV equal bound,
      keepV.num (j := j) (by simpa using different.symm) (by simp) (readyU.fit64 bound), memU]
  · intro d bound
    have fits := readyV.arrayFit (j := 0) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fits
    rw [equal.word (bits := 64) (by omega_using [bound, fits]), key_keep_header workspaceU readyU (by simp) bound keepV, memU]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CountLoop`, which only this module used -/

section

/-! The native loop stops at the odd part and records the complete number
of factors of two; the termination measure is the number being halved. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)
open VG.Spec.Rsa (splitTwos)

structure CountInv (s0 : State) (base : BitVec 32) (capacity w original count m : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * capacity)
  ready : KeyReady base capacity w s
  data : MontData base capacity w s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  number : num s.mem (base + 96#32) (2 * w + 2) 29 = m
  positive : 0 < m
  even : m % 2 = 0
  factors : count + (splitTwos m).1 = (splitTwos original).1
  oddPart : (splitTwos m).2 = (splitTwos original).2
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count
  arrays : ∀ j, j < 30 → j ≠ 29 → num s.mem (base + 96#32) (2 * w + 2) j =
    num s0.mem (base + 96#32) (2 * w + 2) j
  header : ∀ d, d + 8 ≤ 256 → s.mem.readW (off (State.addr base) d) 64 =
    s0.mem.readW (off (State.addr base) d) 64
  frame : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s0.sp + 60#32), 4⟩] s0.mem s.mem
  rest : Rest opRegs s0 s

theorem halfCountLoop_ok {s : State} {base : BitVec 32} {capacity w original : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 29 = original)
    (positive : 0 < original) (even : original % 2 = 0)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = 0#32) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep .eq) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 29 = (splitTwos original).2 ∧
      t.mem.readW (State.addr (t.sp + 60#32)) 32 = BitVec.ofNat 32 (splitTwos original).1 ∧
      (∀ j, j < 30 → j ≠ 29 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩] s.mem t.mem ∧ Rest opRegs s t := by
  let inv := fun m t => ∃ count, CountInv s base capacity w original count m t
  refine WP.loop (M := isa) inv ?_ original s ?_
  · intro m u h
    obtain ⟨count, h⟩ := h
    refine WP.mono (halfCountStep_ok h.workspace h.ready h.data h.stack h.saved h.separate) ?_
    rintro t ⟨readyT, dataT, valueT, savedT, zeroT, arraysT, headerT, frameT, restT⟩
    rw [h.number] at valueT zeroT
    have smaller : m / 2 < m := Nat.div_lt_self h.positive (by decide)
    have positiveT : 0 < m / 2 := by have := h.even; have := h.positive; omega_arith
    have split := VG.Proof.Rsa.splitTwos_even (by have := h.positive; omega_using [smaller]) h.even
    have factors : count + 1 + (splitTwos (m / 2)).1 = (splitTwos original).1 := by
      have := h.factors
      rw [split] at this
      dsimp only at this
      omega_using [this]
    have oddPart : (splitTwos (m / 2)).2 = (splitTwos original).2 := by
      have := h.oddPart
      rw [split] at this
      exact this
    have rest := h.rest.trans restT
    rw [h.rest.sp] at frameT
    have frame := h.frame.trans frameT
    have arrays (j : Nat) (bound : j < 30) (different : j ≠ 29) :=
      (arraysT j bound different).trans (h.arrays j bound different)
    have header (d : Nat) (bound : d + 8 ≤ 256) := (headerT d bound).trans (h.header d bound)
    by_cases evenT : m / 2 % 2 = 0
    · right
      refine ⟨?_, m / 2, smaller, count + 1, ?_⟩
      · change some t.z = some true
        simp only [zeroT, evenT, decide_true]
      · refine ⟨h.workspace.congr restT.wr, readyT, dataT, ?_, ?_, valueT, positiveT,
          evenT, factors, oddPart, savedT, arrays, header, frame, rest⟩
        · rw [restT.sp]; exact h.stack.congr restT.wr
        · rw [restT.sp]; exact h.separate
    · left
      have oddT : m / 2 % 2 = 1 := by omega_using [evenT]
      rw [VG.Proof.Rsa.splitTwos_odd oddT] at factors oddPart
      have countDone : count + 1 = (splitTwos original).1 := by simpa using factors
      refine ⟨?_, readyT, dataT, valueT.trans oddPart, ?_, arrays, header, frame, rest⟩
      · change some t.z = some false
        simp only [zeroT, evenT, decide_false]
      · rw [savedT, countDone]
  · exact ⟨0, workspace, ready, data, stack, separate, number, positive, even,
      by simp, rfl, saved, by intros; rfl, by intros; rfl, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end


/-! Initialize the native decomposition with N−1 and a zero halving count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)

theorem expCountInit_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 0 = n) (large : 1 < n) (odd : n % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit s
      (CountInv s base capacity w (n - 1) 0 (n - 1)) := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (keyCopy_ok workspace ready (o := 29) (a := 0) (by decide) (by decide) (by decide)) ?_)
  rintro u ⟨readyU, keepU, numberU, restU⟩
  rw [number] at numberU
  have workspaceU := workspace.congr restU.wr
  refine WP.seq (WP.mono (keyClrLow_ok workspaceU readyU (j := 29) (by decide)) ?_)
  rintro v ⟨readyV, keepV, numberV, restV⟩
  rw [numberU] at numberV
  have valueV : num v.mem (base + 96#32) (2 * w + 2) 29 = n - 1 := by omega_using [odd, numberV]
  have restUV := restU.trans restV
  have workspaceV := workspace.congr restUV.wr
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  have keep := keepU.trans keepV
  have frameV := key_keep_workspace workspace ready (by simp) keep
  have dataV := (data.after_key_keep workspace ready (by simp) (by simp) keep).1
  refine WP.seq (WP.mono (saveWord_ok stackV (d := 60) (by decide) 0#32 (by decide)) ?_)
  rintro t ⟨memT, restT⟩
  have equal : WorkspaceEq (State.addr base) (8 * capacity) v.mem t.mem := by
    rw [memT]
    exact stackWrite_workspaceEq workspaceV stackV (by rw [restUV.sp]; exact separate) (by decide) _
  have frameT : Frame [⟨State.addr (s.sp + 60#32), 4⟩] v.mem t.mem := by
    rw [memT, restUV.sp]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have rest : Rest opRegs s t := restUV.trans (restT.mono (by simp [opRegs]))
  refine WP.block_nil ⟨workspace.congr rest.wr, readyV.rest restT (by decide) (by decide) (by decide),
    dataV.after_workspaceEq equal, ?_, ?_, ?_, by omega_using [large], by omega_using [odd], by simp, rfl, ?_, ?_, ?_,
    (frameV.mono (by simp)).trans (frameT.mono (by simp)), rest⟩
  · rw [rest.sp]; exact stack.congr rest.wr
  · rw [rest.sp]; exact separate
  · exact (key_number_of_workspaceEq workspaceV readyV equal (j := 29) (by decide)).trans valueV
  · rw [restT.sp, memT, Mem.readW_writeW_self32]
  · intro j bound different
    rw [key_number_of_workspaceEq workspaceV readyV equal bound,
      keep.num (j := j) (by simpa using different.symm) (by simp) (ready.fit64 bound)]
  · intro d bound
    have fits := readyV.arrayFit (j := 0) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fits
    rw [equal.word (bits := 64) (by omega_using [bound, fits]), key_keep_header workspace ready (by simp) bound keep]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Compose native initialization and the exact factor-of-two loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)
open VG.Spec.Rsa (splitTwos)

theorem expDecompose_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 0 = n) (large : 1 < n) (odd : n % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 29 = (splitTwos (n - 1)).2 ∧
      t.mem.readW (State.addr (t.sp + 60#32)) 32 = BitVec.ofNat 32 (splitTwos (n - 1)).1 ∧
      (∀ j, j < 30 → j ≠ 29 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩] s.mem t.mem ∧ Rest opRegs s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose, WP.seq_iff]
  refine WP.mono (expCountInit_ok workspace ready data stack separate number large odd) ?_
  intro u h
  refine WP.mono (halfCountLoop_ok h.workspace h.ready h.data h.stack h.separate h.number h.positive h.even h.saved) ?_
  rintro t ⟨readyT, dataT, valueT, countT, arraysT, headerT, frameT, restT⟩
  rw [h.rest.sp] at frameT
  exact ⟨readyT, dataT, valueT, countT,
    fun j bound different => (arraysT j bound different).trans (h.arrays j bound different),
    fun d bound => (headerT d bound).trans (h.header d bound), h.frame.trans frameT, h.rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.ExponentSetup`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.PowerStore`, which only this module used -/

section

/-! Store both halves of the shared power-of-two metadata in the exponent
array's padding, preserving all bytes of its actual exponent. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.Rsa.Arm.Keys (arr S)

theorem exponentPowerStore_words {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) (arrAt w 27 + 8 * w)) (s.gpr .r2)).writeW
        (off (State.addr base) (arrAt w 27 + 8 * w + 4)) (s.gpr .r3) ∧ Rest [.r0] s t := by
  let B := base + 96#32
  obtain fit := ready.arrayFit (j := 27) (by decide)
  have r7 : s.gpr .r7 = BitVec.ofNat 32 (S (2 * w + 2)) := ready.r7
  have r8 : s.gpr .r8 = B := ready.r8
  have r9 : s.gpr .r9 = BitVec.ofNat 32 (2 * w + 2) := ready.r9
  obtain ptrValue : BitVec.ofNat 32 27 * BitVec.ofNat 32 (S (2 * w + 2)) + B +
      BitVec.ofNat 32 VG.Impl.Rsa.Arm.Keys.hdr = B + BitVec.ofNat 32 (arr (2 * w + 2) 27) :=
    VG.Proof.Rsa.Arm.Keys.ptr_val B 27 (S (2 * w + 2))
  obtain shifted : BitVec.ofNat 32 (2 * w + 2) <<< 2 = BitVec.ofNat 32 (4 * (2 * w + 2)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (2 * w + 2) * BitVec.ofNat 32 4 = _
    rw [BitVec.ofNat_mul_ofNat]
    congr 1
    omega_arith
  obtain pointer : B + BitVec.ofNat 32 (arr (2 * w + 2) 27) + BitVec.ofNat 32 (4 * (2 * w + 2)) - 8 =
      base + BitVec.ofNat 32 (arrAt w 27 + 8 * w) := by
    change base + 96#32 + BitVec.ofNat 32 (arr (2 * w + 2) 27) +
      BitVec.ofNat 32 (4 * (2 * w + 2)) - BitVec.ofNat 32 8 = _
    rw [VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_arith), BitVec.add_assoc,
      ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    rw [← Nat.add_assoc, keyView_array]
    congr 1
    omega_arith
  obtain addr0 : State.addr (base + BitVec.ofNat 32 (arrAt w 27 + 8 * w)) =
      off (State.addr base) (arrAt w 27 + 8 * w) := VG.Arm.addr_add (by have := workspace.nowrap; omega_arith)
  obtain addr4 : State.addr (base + BitVec.ofNat 32 (arrAt w 27 + 8 * w) + 4#32) =
      off (State.addr base) (arrAt w 27 + 8 * w + 4) := by
    rw [Offset.add_add]
    exact VG.Arm.addr_add (by have := workspace.nowrap; omega_arith)
  obtain write0 := workspace.write (off := arrAt w 27 + 8 * w) (by omega_arith)
  obtain write4 := workspace.write (off := arrAt w 27 + 8 * w + 4) (by omega_arith)
  refine withRest_all [.r0] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore VG.Impl.Rsa.Arm.Keys.ptr
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, r7, r8, r9, ptrValue, shifted, pointer,
    addr0, addr4, write0, write4]

theorem exponentPowerStore_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      t.mem.readW (off (State.addr base) (arrAt w 27 + 8 * w)) 64 = (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) ∧
      numAt t.mem (State.addr base) w 27 = numAt s.mem (State.addr base) w 27 ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [27] [] s.mem t.mem ∧ Rest [.r0] s t := by
  refine WP.mono (exponentPowerStore_words workspace ready) ?_
  rintro t ⟨mem, rest⟩
  obtain fit := ready.arrayFit (j := 27) (by decide)
  have nowrap := workspace.nowrap
  obtain written : t.mem = s.mem.writeW (off (State.addr base) (arrAt w 27 + 8 * w))
      (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) := by
    rw [VG.Proof.Rc2.Word32.write64_pair, Offset.add_add]
    exact mem
  obtain frame : Frame [⟨off (State.addr base) (arrAt w 27 + 8 * w), 8⟩] s.mem t.mem := by
    rw [written]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  obtain number : numAt t.mem (State.addr base) w 27 = numAt s.mem (State.addr base) w 27 := by
    unfold numAt
    apply congrArg BitVec.toNat
    exact frame.read (r := ⟨off (State.addr base) (arrAt w 27), 8 * w⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r
          exact Offset.disjoint _ (.inl (Nat.le_refl _)) (by omega_arith) (by omega_arith)) (by omega_arith)
  obtain shiftFits := ready.baseShiftFits workspace
  obtain offNative : off (State.addr base) (arrAt w 27 + 8 * w) =
      off (State.addr (base + 96#32)) (arr (2 * w + 2) 27 + 8 * w) := by
    rw [VG.Arm.addr_add shiftFits]
    unfold off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_assoc, keyView_array]
  obtain keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [27] [] s.mem t.mem := by
    rw [written, offNative]
    exact VG.Proof.Rsa.Arm.Keys.Keep.of_arr (d := 8 * w)
      (writeW_outside _ _ _ (by have := ready.fit64 (j := 27) (by decide); simp only [S] at this; omega_arith))
      (by simp only [S]; omega_arith) (by simp)
  exact ⟨ready.rest rest (by decide) (by decide) (by decide),
    (data.after_key_keep workspace ready (by simp) (by simp) keep).1,
    by rw [written, Mem.readW_writeW_self64], number, keep, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Complete native setup of the exponent and metadata consumed by the
shared four-bit-window Miller–Rabin kernel. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/ExponentLoop.lean`, which only this module imported.
section

/-! The bounded native loop divides by precisely 2^sigma. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)

structure ExponentInv (s0 : State) (base : BitVec 32) (capacity w input sigma i left : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * capacity)
  ready : KeyReady base capacity w s
  data : MontData base capacity w s.mem
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  number : num s.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ i
  saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 left
  remaining : i + left = sigma
  positive : 0 < left
  bound : left ≤ 4
  arrays : ∀ j, j < 30 → j ≠ 27 → num s.mem (base + 96#32) (2 * w + 2) j =
    num s0.mem (base + 96#32) (2 * w + 2) j
  header : ∀ d, d + 8 ≤ 256 → s.mem.readW (off (State.addr base) d) 64 =
    s0.mem.readW (off (State.addr base) d) 64
  frame : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s0.sp + 64#32), 4⟩] s0.mem s.mem
  rest : Rest opRegs s0 s

theorem exponentHalfLoop_ok {s : State} {base : BitVec 32} {capacity w input sigma : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 27 = input)
    (positive : 0 < sigma) (bound : sigma ≤ 4)
    (saved : s.mem.readW (State.addr (s.sp + 64#32)) 32 = BitVec.ofNat 32 sigma) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf .ne) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ sigma ∧
      t.mem.readW (State.addr (t.sp + 64#32)) 32 = 0#32 ∧
      (∀ j, j < 30 → j ≠ 27 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest opRegs s t := by
  let inv := fun left t => ∃ i, ExponentInv s base capacity w input sigma i left t
  refine WP.loop (M := isa) inv ?_ sigma s ?_
  · intro left u h
    obtain ⟨i, h⟩ := h
    refine WP.mono (exponentHalfStep_ok h.workspace h.ready h.data h.stack h.positive h.bound h.saved h.separate) ?_
    rintro t ⟨readyT, dataT, valueT, savedT, zeroT, arraysT, headerT, frameT, restT⟩
    obtain value : num t.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ (i + 1) := by
      rw [valueT, h.number, Nat.div_div_eq_div_mul, Nat.pow_succ]
    obtain rest := h.rest.trans restT
    rw [h.rest.sp] at frameT
    obtain frame := h.frame.trans frameT
    have arrays (j : Nat) (bound : j < 30) (different : j ≠ 27) :=
      (arraysT j bound different).trans (h.arrays j bound different)
    have header (d : Nat) (bound : d + 8 ≤ 256) := (headerT d bound).trans (h.header d bound)
    by_cases last : left = 1
    · left
      obtain done : i + 1 = sigma := by have := h.remaining; omega
      refine ⟨?_, readyT, dataT, ?_, ?_, arrays, header, frame, rest⟩
      · change some (!t.z) = some false
        simp only [zeroT, last, decide_true, Bool.not_true]
      · rwa [done] at value
      · simpa only [last, Nat.sub_self] using savedT
    · right
      refine ⟨?_, left - 1, by have := h.positive; omega, i + 1, ?_⟩
      · change some (!t.z) = some true
        simp only [zeroT, last, decide_false, Bool.not_false]
      · refine ⟨h.workspace.congr restT.wr, readyT, dataT, ?_, ?_, value, savedT,
          by have := h.remaining; have := h.positive; omega,
          by have := h.positive; omega, by have := h.bound; omega, arrays, header, frame, rest⟩
        · rw [restT.sp]; exact h.stack.congr restT.wr
        · rw [restT.sp]; exact h.separate
  · exact ⟨0, workspace, ready, data, stack, separate, by simpa using number,
      saved, by simp, positive, bound, by intros; rfl, by intros; rfl, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PowerWord.lean`, which only this module imported.
section

/-! Load the complete native decomposition count and call RSA's shared
fixed-step construction of the u64 metadata word. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem exponentPowerWord_ok {s : State} {count : Nat} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count) :
    WP isa (.block (([.ldrSp .r1 60] : List Instr) ++ VG.Impl.Bignum.Arm.TwoPower.code)) s fun t =>
      (t.gpr .r3 ++ t.gpr .r2 : BitVec 64) = BitVec.twoPow 64 (count % 64) ∧
      t.mem = s.mem ∧ Rest [.r1, .r2, .r3, .r4] s t := by
  obtain read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  change WP isa (.block (.ldrSp .r1 60 :: VG.Impl.Bignum.Arm.TwoPower.code)) s _
  refine wp_loadStack (by decide) rfl read fun u load => ?_
  refine WP.mono (VG.Proof.Bignum.Arm.TwoPower.code_word_ok u) ?_
  rintro t ⟨word, mem, rest⟩
  rw [load.gpr, saved, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd count (by decide : 64 ∣ 2 ^ 32)] at word
  exact ⟨word, mem.trans load.mem, (load.rest (by simp)).trans rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.Rsa.Arm.Keys (num opRegs)

private theorem local60_preserved {s t : State} {base : BitVec 32} {capacity : Nat} {rs : List Reg}
    (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (frame : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem)
    (rest : Rest rs s t) :
    t.mem.readW (State.addr (t.sp + 60#32)) 32 = s.mem.readW (State.addr (s.sp + 60#32)) 32 := by
  rw [rest.sp]
  refine frame.readW (r := ⟨State.addr (s.sp + 60#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
  · rw [VG.Arm.addr_add (by have := stack.nowrap; omega_using [this]), VG.Arm.addr_add (by have := stack.nowrap; omega_using [this])]
    exact Offset.disjoint _ (.inl (by decide : 60 + 4 ≤ 64)) (by decide) (by decide)

theorem expSetup_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 0 = n)
    (large : 1 < n) (odd : n % 2 = 1) (small : n < 2 ^ (64 * w)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expSetup s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      numAt t.mem (State.addr base) w 27 = Proof.MillerRabin.Round.exponent n ∧
      t.mem.readW (off (State.addr base) (arrAt w 27 + 8 * w)) 64 =
        BitVec.twoPow 64 ((Spec.Rsa.splitTwos (n - 1)).1 % 64) ∧
      (∀ j, j < 30 → j ≠ 27 → j ≠ 29 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest opRegs s t := by
  let count := (Spec.Rsa.splitTwos (n - 1)).1
  let sigma := countShift count
  obtain sigmaPositive : 0 < sigma := (countShift_bounds count).1
  obtain sigmaBound : sigma ≤ 4 := (countShift_bounds count).2
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.expSetup, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (expDecompose_ok workspace ready data stack separate number large odd) ?_)
  rintro u ⟨readyU, dataU, _, countU, arraysU, headerU, frameU, restU⟩
  obtain workspaceU := workspace.congr restU.wr
  obtain stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  obtain separateU : (⟨State.addr u.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
    rw [restU.sp]; exact separate
  refine WP.seq (WP.mono (exponentSigma_ok stackU countU) ?_)
  rintro v ⟨memV, restV⟩
  obtain equalV : WorkspaceEq (State.addr base) (8 * capacity) u.mem v.mem := by
    rw [memV]
    exact stackWrite_workspaceEq workspaceU stackU separateU (by decide) _
  obtain readyV := readyU.rest restV (by decide) (by decide) (by decide)
  obtain dataV := dataU.after_workspaceEq equalV
  obtain workspaceV := workspaceU.congr restV.wr
  obtain frameV : Frame [⟨State.addr (u.sp + 64#32), 4⟩] u.mem v.mem := by
    rw [memV]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  obtain numberV : num v.mem (base + 96#32) (2 * w + 2) 0 = n :=
    (key_number_of_workspaceEq workspaceU readyU equalV (j := 0) (by decide)).trans
      ((arraysU 0 (by decide) (by decide)).trans number)
  refine WP.seq (WP.mono (keyCopy_ok workspaceV readyV (o := 27) (a := 0) (by decide) (by decide) (by decide)) ?_)
  rintro a ⟨readyA, keepA, valueA, restA⟩
  rw [numberV] at valueA
  obtain workspaceA := workspaceV.congr restA.wr
  obtain dataA := (dataV.after_key_keep workspaceV readyV (by simp) (by simp) keepA).1
  obtain frameA := key_keep_workspace workspaceV readyV (by simp) keepA
  obtain restUA : Rest opRegs u a := (restV.mono (by simp [opRegs])).trans restA
  obtain stackA : Workspace a a.sp 72 := by rw [restUA.sp]; exact stackU.congr restUA.wr
  obtain savedA : a.mem.readW (State.addr (a.sp + 64#32)) 32 = BitVec.ofNat 32 sigma := by
    obtain countSep : (⟨State.addr (v.sp + 64#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
      rw [restV.sp, VG.Arm.addr_add (by have := stackU.nowrap; omega_using [this])]
      exact separateU.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))
    rw [restA.sp, frameA.readW (r := ⟨State.addr (v.sp + 64#32), 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact countSep) (by decide),
      restV.sp, memV, Mem.readW_writeW_self32]
  refine WP.seq (WP.mono (exponentHalfLoop_ok workspaceA readyA dataA stackA
    (by rw [restUA.sp]; exact separateU) valueA sigmaPositive sigmaBound savedA) ?_)
  rintro b ⟨readyB, dataB, valueB, _, arraysB, headerB, frameB, restB⟩
  obtain restUB := restUA.trans restB
  obtain frameWork : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (u.sp + 64#32), 4⟩] u.mem b.mem := by
    rw [restUA.sp] at frameB
    exact ((frameV.mono (by simp)).trans (frameA.mono (by simp))).trans frameB
  obtain countB : b.mem.readW (State.addr (b.sp + 60#32)) 32 = BitVec.ofNat 32 count :=
    (local60_preserved stackU separateU frameWork restUB).trans countU
  obtain stackB : Workspace b b.sp 72 := by rw [restUB.sp]; exact stackU.congr restUB.wr
  refine WP.seq (WP.mono (exponentPowerWord_ok stackB countB) ?_)
  rintro c ⟨powerC, memC, restC⟩
  obtain workspaceB := workspaceU.congr restUB.wr
  obtain workspaceC := workspaceB.congr restC.wr
  obtain readyC := readyB.rest restC (by decide) (by decide) (by decide)
  obtain dataC : MontData base capacity w c.mem := memC ▸ dataB
  refine WP.seq (WP.mono (exponentPowerStore_ok workspaceC readyC dataC) ?_)
  rintro t ⟨readyT, dataT, powerT, exponentT, keepT, restT⟩
  obtain quotientSmall : n / 2 ^ sigma < 2 ^ (64 * w) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) small
  obtain lowB : numAt b.mem (State.addr base) w 27 = n / 2 ^ sigma := by
    rw [keyView_number_low b.mem base w 27 (readyB.baseShiftFits workspaceB) (by rw [valueB]; exact quotientSmall), valueB]
  rw [memC, lowB] at exponentT
  obtain exponent : n / 2 ^ sigma = Proof.MillerRabin.Round.exponent n := by
    change _ = (n - 1) / 2 ^ sigma
    exact (VG.Proof.Bignum.odd_div odd (by omega_using [sigmaPositive] : 1 ≤ sigma)).symm
  obtain rest : Rest opRegs s t := restU.trans (restUB.trans
    ((restC.mono (by simp [opRegs])).trans (restT.mono (by simp [opRegs]))))
  obtain frameT := key_keep_workspace workspaceC readyC (by simp) keepT
  rw [memC] at frameT
  obtain frameTotal : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem := by
    rw [restU.sp] at frameWork
    exact ((frameU.mono (by simp)).trans (frameWork.mono (by simp))).trans (frameT.mono (by simp))
  refine WP.block_nil ⟨readyT, dataT, exponentT.trans exponent, powerT.trans powerC, ?_, ?_, frameTotal, rest⟩
  · intro j bound not27 not29
    rw [keepT.num (j := j) (by simpa using not27.symm) (by simp) (readyC.fit64 bound), memC,
      arraysB j bound not27, keepA.num (j := j) (by simpa using not27.symm) (by simp) (readyV.fit64 bound),
      key_number_of_workspaceEq workspaceU readyU equalV bound, arraysU j bound not29]
  · intro d bound
    obtain fit := readyU.arrayFit (j := 0) (by decide)
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
    rw [key_keep_header workspaceC readyC (by simp) bound keepT, memC, headerB d bound,
      key_keep_header workspaceV readyV (by simp) bound keepA, equalV.word (bits := 64) (by omega_using [bound, fit]), headerU d bound]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Native Montgomery and exponent preparation establish the complete witness state. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhasePrepared.lean`, which only this module imported.
section

/-! End-to-end native preparation of a q or p phase for the existing shared
Miller–Rabin kernel. Only the phase's scratch and two local counters change. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)

private theorem oddThree {n : Nat} (large : 1 < n) (odd : n % 2 = 1) : 3 ≤ n := by omega

private theorem phaseWords {k : Nat} (lower : 64 ≤ k) (upper : k ≤ 1024) :
    4 ≤ Spec.Rsa.modulusWords k ∧ Spec.Rsa.modulusWords k ≤ 128 := by
  simp only [Spec.Rsa.modulusWords]
  omega

theorem phasePrepared_ok (b : MontBackend) {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (stack : Workspace s s.sp 72) (stackBelow : 56 ≤ s.sp.toNat)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := Spec.Rsa.modulusWords k
  let n := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared, WP.seq_iff]
  refine WP.mono (montPrep_ok b h space) ?_
  rintro u ⟨readyU, dataU, fullU, oneU, minusU, modulusU, r2U, strideU, frameU, restU⟩
  have frameU' : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩, FrameStack.belowA s.sp 56] s.mem u.mem := frameU.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨FrameStack.belowA s.sp 56, by simp, FrameStack.belowA_sub (by decide) stackBelow⟩
  obtain workspaceU := h.workspace.congr restU.wr
  obtain stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  obtain separateU : (⟨State.addr u.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
    rw [restU.sp]; exact separate
  obtain smallN : n < 2 ^ (64 * w) := by
    dsimp only [n, w]
    rw [← modulusU]
    exact numAt_lt _ _ _ _
  refine WP.mono (expSetup_ok workspaceU readyU dataU stackU separateU fullU h.large h.odd smallN) ?_
  rintro t ⟨readyT, dataT, exponentT, powerT, arraysT, _, frameT, restT⟩
  obtain workspaceT := workspaceU.congr restT.wr
  have numbers (j : Nat) (bound : j < 30) (not27 : j ≠ 27) (not29 : j ≠ 29) :
      numAt t.mem (State.addr base) w j = numAt u.mem (State.addr base) w j := by
    rw [← keyView_number_mod t.mem base w j (readyT.baseShiftFits workspaceT),
      ← keyView_number_mod u.mem base w j (readyU.baseShiftFits workspaceU), arraysT j bound not27 not29]
  obtain dims := phaseWords h.minLength h.maxLength
  obtain fits : arrAt w 28 ≤ 8 * capacity := readyU.arraysFit (j := 27) (by decide)
  obtain data : RoundData base capacity w n t.mem :=
    ⟨dataT, dims.1, dims.2, fits, oddThree h.large h.odd, h.odd,
      (numbers 0 (by decide) (by decide) (by decide)).trans modulusU,
      (numbers 4 (by decide) (by decide) (by decide)).trans r2U,
      (numbers 9 (by decide) (by decide) (by decide)).trans oneU,
      (numbers 10 (by decide) (by decide) (by decide)).trans minusU, exponentT, powerT⟩
  rw [restU.sp] at frameT
  exact ⟨data, frameU'.trans (frameT.mono (by simp)),
    restU.trans (restT.mono (by simp [roundClobbers, VG.Proof.Rsa.Arm.Keys.opRegs]))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhaseSaved.lean`, which only this module imported.
section

/-! Montgomery and exponent preparation preserve the witness-loop policy slots. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem locals_disjoint {s : State} {d offset : Nat} (stack : Workspace s s.sp 72)
    (before : d + 4 ≤ offset) (fit : offset + 4 ≤ 72) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩ := by
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega), VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact Offset.disjoint _ (.inl before) (by omega) (by omega)

theorem SavedFrame.after_preparation {s t : State} {base : BitVec 32} {capacity : Nat}
    {values : Nat → BitVec 32} {slots : List Nat} {rs : List Reg}
    (h : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (stackBelow : 56 ≤ s.sp.toNat)
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩, FrameStack.belowA s.sp 56] s.mem t.mem) (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  obtain fit := bounds d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ (by omega))
  · exact locals_disjoint h.space fit (by decide : 60 + 4 ≤ 72)
  · exact locals_disjoint h.space (by omega) (by decide : 64 + 4 ≤ 72)
  · change (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
    rw [VG.Arm.addr_add (by have := h.space.nowrap; omega), FrameStack.addr_sub' stackBelow]
    exact Offset.disjoint_below _ (by omega)

theorem phasePrepared_saved_ok (b : MontBackend) {s : State} {base src : BitVec 32} {capacity k : Nat}
    {values : Nat → BitVec 32} {slots : List Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (saved : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (stackBelow : 56 ≤ s.sp.toNat) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      SavedFrame values slots t ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (phasePrepared_ok b h space saved.space stackBelow separate) ?_
  rintro t ⟨data, changed, rest⟩
  exact ⟨data, saved.after_preparation bounds separate stackBelow changed rest, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem preparedWitness_ok (b : MontBackend) {s : State} {p : WitnessParams} {src : BitVec 32} {k used : Nat}
    (h : PhaseInput p src k used s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) s fun t =>
      WitnessState p used 0 t ∧
      Frame [⟨State.addr p.base, 8 * p.capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain bounds : ∀ d ∈ witnessSlots, d + 4 ≤ 60 := by
    intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega_using [hd]
  refine WP.mono (phasePrepared_saved_ok b h.preparation h.space h.saved bounds h.stackScratch h.stackBelow) ?_
  rintro t ⟨data, saved, changed, rest⟩
  rw [h.modulus, ← h.words] at data
  refine ⟨⟨data, h.preparation.workspace.congr rest.wr, saved, ?_, ?_, ?_, h.bitsExact, h.bitsPositive,
    h.bitsBound, h.bitsFit, h.checksPositive, h.checksBound, h.usedBound, Nat.zero_le _,
    h.tapeCount, h.tapeFits, ?_, h.tapeScratch, ?_, ?_, ?_⟩, changed, rest⟩
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · rw [rest.sp]; exact h.tapeStack
  · rw [rest.sp]; exact h.tapeBelow
  · refine (rsa_bytes_frame changed (by have := h.tapeCount; omega_using [this]) ?_).trans h.tapeBytes
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tapeScratch
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))
    · exact h.tapeBelow

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! A witness iteration either consumes a nonempty prefix or reports exhausted entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def witnessNextUsed (p : WitnessParams) (used : Nat) : Nat :=
  if used + (p.bits + 7) / 8 ≤ p.bytes.length then used + (p.bits + 7) / 8 else used

def witnessNextPassed (p : WitnessParams) (used passed : Nat) : Nat :=
  if used + (p.bits + 7) / 8 ≤ p.bytes.length then drawPassed p passed used else passed

def witnessNextStatus (p : WitnessParams) (used passed : Nat) : Nat :=
  if used + (p.bits + 7) / 8 ≤ p.bytes.length then drawStatus p passed used else 0

theorem witnessStep_ok (b : VG.Proof.Bignum.Arm.MontBackend) (v : RoundImpl) {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul) v.name v.code) s fun t =>
      WitnessState p (witnessNextUsed p used) (witnessNextPassed p used passed) t ∧
      t.gpr .r3 = BitVec.ofNat 32 (witnessNextStatus p used passed) ∧
      t.z = decide (witnessNextStatus p used passed = 4) ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have lengthWord : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 p.bytes.length := by
    simpa only [witnessValues] using h.saved.saved 20 (by simp [witnessSlots])
  have usedWord : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used := by
    simpa only [witnessValues] using h.saved.saved 40 (by simp [witnessSlots])
  have widthWord : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 ((p.bits + 7) / 8) := by
    simpa only [witnessValues] using h.saved.saved 48 (by simp [witnessSlots])
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (witnessRoom_ok h.saved.space h.tapeCount
    (by have := h.bitsBound; omega_using [this]) h.usedBound lengthWord usedWord widthWord) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases enough : used + (p.bits + 7) / 8 ≤ p.bytes.length
  · have available : ¬ p.bytes.length - used < (p.bits + 7) / 8 := by omega_using [enough]
    refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false available])
      (by intro h; cases h) ?_)
    intro _
    refine WP.mono (draw_ok b v ctx more enough) ?_
    rintro t ⟨stateT, statusT, zeroT, frameT, restT⟩
    rw [rest.sp, memory] at frameT
    refine WP.block_nil ?_
    simpa only [witnessNextUsed, witnessNextPassed, witnessNextStatus, ite_eq_left enough] using
      (show WitnessState p (used + (p.bits + 7) / 8) (drawPassed p passed used) t ∧
        t.gpr .r3 = BitVec.ofNat 32 (drawStatus p passed used) ∧ t.z = decide (drawStatus p passed used = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT, (rest.mono (by simp [roundClobbers])).trans restT⟩)
  · have short : p.bytes.length - used < (p.bits + 7) / 8 := by have := h.usedBound; omega_using [enough, this]
    refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true short])
      ?_ (by intro h; cases h))
    intro _
    refine WP.mono (setStatus_ok u 0 (by decide)) ?_
    rintro t ⟨⟨statusT, zeroT, memT⟩, restT⟩
    have stateT := ctx.after_memory memT restT
    have frameT : Frame (witnessRegions p s.sp) s.mem t.mem := by rw [memT, memory]; exact Frame.refl _ _
    refine WP.block_nil ?_
    simpa only [witnessNextUsed, witnessNextPassed, witnessNextStatus, ite_eq_right enough] using
      (show WitnessState p used passed t ∧ t.gpr .r3 = BitVec.ofNat 32 0 ∧ t.z = decide (0 = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT,
          (rest.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
