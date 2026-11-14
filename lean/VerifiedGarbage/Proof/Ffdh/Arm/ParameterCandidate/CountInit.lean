module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountStep
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord

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
