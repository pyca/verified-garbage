module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Decompose
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSigma
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PowerStore
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Bignum.OddDivision
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
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
    have value : num t.mem (base + 96#32) (2 * w + 2) 27 = input / 2 ^ (i + 1) := by
      rw [valueT, h.number, Nat.div_div_eq_div_mul, Nat.pow_succ]
    have rest := h.rest.trans restT
    rw [h.rest.sp] at frameT
    have frame := h.frame.trans frameT
    have arrays (j : Nat) (bound : j < 30) (different : j ≠ 27) :=
      (arraysT j bound different).trans (h.arrays j bound different)
    have header (d : Nat) (bound : d + 8 ≤ 256) := (headerT d bound).trans (h.header d bound)
    by_cases last : left = 1
    · left
      have done : i + 1 = sigma := by have := h.remaining; omega
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
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
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
  · rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
  · rw [VG.Arm.addr_add (by have := stack.nowrap; omega), VG.Arm.addr_add (by have := stack.nowrap; omega)]
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
  have sigmaPositive : 0 < sigma := (countShift_bounds count).1
  have sigmaBound : sigma ≤ 4 := (countShift_bounds count).2
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.expSetup, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (expDecompose_ok workspace ready data stack separate number large odd) ?_)
  rintro u ⟨readyU, dataU, _, countU, arraysU, headerU, frameU, restU⟩
  have workspaceU := workspace.congr restU.wr
  have stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  have separateU : (⟨State.addr u.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
    rw [restU.sp]; exact separate
  refine WP.seq (WP.mono (exponentSigma_ok stackU countU) ?_)
  rintro v ⟨memV, restV⟩
  have equalV : WorkspaceEq (State.addr base) (8 * capacity) u.mem v.mem := by
    rw [memV]
    exact stackWrite_workspaceEq workspaceU stackU separateU (by decide) _
  have readyV := readyU.rest restV (by decide) (by decide) (by decide)
  have dataV := dataU.after_workspaceEq equalV
  have workspaceV := workspaceU.congr restV.wr
  have frameV : Frame [⟨State.addr (u.sp + 64#32), 4⟩] u.mem v.mem := by
    rw [memV]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have numberV : num v.mem (base + 96#32) (2 * w + 2) 0 = n :=
    (key_number_of_workspaceEq workspaceU readyU equalV (j := 0) (by decide)).trans
      ((arraysU 0 (by decide) (by decide)).trans number)
  refine WP.seq (WP.mono (keyCopy_ok workspaceV readyV (o := 27) (a := 0) (by decide) (by decide) (by decide)) ?_)
  rintro a ⟨readyA, keepA, valueA, restA⟩
  rw [numberV] at valueA
  have workspaceA := workspaceV.congr restA.wr
  have dataA := (dataV.after_key_keep workspaceV readyV (by simp) (by simp) keepA).1
  have frameA := key_keep_workspace workspaceV readyV (by simp) keepA
  have restUA : Rest opRegs u a := (restV.mono (by simp [opRegs])).trans restA
  have stackA : Workspace a a.sp 72 := by rw [restUA.sp]; exact stackU.congr restUA.wr
  have savedA : a.mem.readW (State.addr (a.sp + 64#32)) 32 = BitVec.ofNat 32 sigma := by
    have countSep : (⟨State.addr (v.sp + 64#32), 4⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
      rw [restV.sp, VG.Arm.addr_add (by have := stackU.nowrap; omega)]
      exact separateU.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))
    rw [restA.sp, frameA.readW (r := ⟨State.addr (v.sp + 64#32), 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact countSep) (by decide),
      restV.sp, memV, Mem.readW_writeW_self32]
  refine WP.seq (WP.mono (exponentHalfLoop_ok workspaceA readyA dataA stackA
    (by rw [restUA.sp]; exact separateU) valueA sigmaPositive sigmaBound savedA) ?_)
  rintro b ⟨readyB, dataB, valueB, _, arraysB, headerB, frameB, restB⟩
  have restUB := restUA.trans restB
  have frameWork : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (u.sp + 64#32), 4⟩] u.mem b.mem := by
    rw [restUA.sp] at frameB
    exact ((frameV.mono (by simp)).trans (frameA.mono (by simp))).trans frameB
  have countB : b.mem.readW (State.addr (b.sp + 60#32)) 32 = BitVec.ofNat 32 count :=
    (local60_preserved stackU separateU frameWork restUB).trans countU
  have stackB : Workspace b b.sp 72 := by rw [restUB.sp]; exact stackU.congr restUB.wr
  refine WP.seq (WP.mono (exponentPowerWord_ok stackB countB) ?_)
  rintro c ⟨powerC, memC, restC⟩
  have workspaceB := workspaceU.congr restUB.wr
  have workspaceC := workspaceB.congr restC.wr
  have readyC := readyB.rest restC (by decide) (by decide) (by decide)
  have dataC : MontData base capacity w c.mem := memC ▸ dataB
  refine WP.seq (WP.mono (exponentPowerStore_ok workspaceC readyC dataC) ?_)
  rintro t ⟨readyT, dataT, powerT, exponentT, keepT, restT⟩
  have quotientSmall : n / 2 ^ sigma < 2 ^ (64 * w) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) small
  have lowB : numAt b.mem (State.addr base) w 27 = n / 2 ^ sigma := by
    rw [keyView_number_low b.mem base w 27 (readyB.baseShiftFits workspaceB) (by rw [valueB]; exact quotientSmall), valueB]
  rw [memC, lowB] at exponentT
  have exponent : n / 2 ^ sigma = Proof.MillerRabin.Round.exponent n := by
    change _ = (n - 1) / 2 ^ sigma
    exact (VG.Proof.Bignum.odd_div odd (by omega : 1 ≤ sigma)).symm
  have rest : Rest opRegs s t := restU.trans (restUB.trans
    ((restC.mono (by simp [opRegs])).trans (restT.mono (by simp [opRegs]))))
  have frameT := key_keep_workspace workspaceC readyC (by simp) keepT
  rw [memC] at frameT
  have frameTotal : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem := by
    rw [restU.sp] at frameWork
    exact ((frameU.mono (by simp)).trans (frameWork.mono (by simp))).trans (frameT.mono (by simp))
  refine WP.block_nil ⟨readyT, dataT, exponentT.trans exponent, powerT.trans powerC, ?_, ?_, frameTotal, rest⟩
  · intro j bound not27 not29
    rw [keepT.num (j := j) (by simpa using not27.symm) (by simp) (readyC.fit64 bound), memC,
      arraysB j bound not27, keepA.num (j := j) (by simpa using not27.symm) (by simp) (readyV.fit64 bound),
      key_number_of_workspaceEq workspaceU readyU equalV bound, arraysU j bound not29]
  · intro d bound
    have fit := readyU.arrayFit (j := 0) (by decide)
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
    rw [key_keep_header workspaceC readyC (by simp) bound keepT, memC, headerB d bound,
      key_keep_header workspaceV readyV (by simp) bound keepA, equalV.word (bits := 64) (by omega), headerU d bound]

end VG.Proof.Ffdh.Arm.ParameterCandidate
