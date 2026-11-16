module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Decompose
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSigma
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
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
import Batteries.Tactic.Init
import Batteries.Tactic.PermuteGoals
import Batteries.Tactic.SeqFocus
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Bignum.Arm.TwoPower
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.TwoPower
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame

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

theorem phasePrepared_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := Spec.Rsa.modulusWords k
  let n := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared, WP.seq_iff]
  refine WP.mono (montPrep_ok h space) ?_
  rintro u ⟨readyU, dataU, fullU, oneU, minusU, modulusU, r2U, strideU, frameU, restU⟩
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
  exact ⟨data, (frameU.mono (by simp)).trans frameT,
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
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem) (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  obtain fit := bounds d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ (by omega))
  · exact locals_disjoint h.space fit (by decide : 60 + 4 ≤ 72)
  · exact locals_disjoint h.space (by omega) (by decide : 64 + 4 ≤ 72)

theorem phasePrepared_saved_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    {values : Nat → BitVec 32} {slots : List Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (saved : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      SavedFrame values slots t ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (phasePrepared_ok h space saved.space separate) ?_
  rintro t ⟨data, changed, rest⟩
  exact ⟨data, saved.after_preparation bounds separate changed rest, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem preparedWitness_ok {s : State} {p : WitnessParams} {src : BitVec 32} {k used : Nat}
    (h : PhaseInput p src k used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      WitnessState p used 0 t ∧
      Frame [⟨State.addr p.base, 8 * p.capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain bounds : ∀ d ∈ witnessSlots, d + 4 ≤ 60 := by
    intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega_using [hd]
  refine WP.mono (phasePrepared_saved_ok h.preparation h.space h.saved bounds h.stackScratch) ?_
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
    rcases hr with rfl | rfl | rfl
    · exact h.tapeScratch
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))

end VG.Proof.Ffdh.Arm.ParameterCandidate
