module

import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Step
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `TripleDes.AArch64.Bitsliced.Round`, which only this module used -/

section

/-!
# An AdvSIMD round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`x5`, broadcasts it, steps the pointer by 8 in the pass's direction, and
does to the 64 state words what `roundW` does, with the key's low 48 bits.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ step_congr steps_congr)

/-- The key pointer after a round. -/
def nextKey (d : Direction) (p : Addr) : Addr := if d = .encrypt then p + 8 else p - 8

theorem keyLoad_ok (d : Direction) {s : State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧
      s'.v keyReg = ofVDwords (s.mem.readW (s.gpr .x5) 64) (s.mem.readW (s.gpr .x5) 64) ∧
      s'.gpr .x5 = nextKey d (s.gpr .x5) ∧
      (∀ r, r ≠ .x9 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ y, y ≠ keyReg → s'.v y = s.v y) := by
  let K := s.mem.readW (s.gpr .x5) 64
  have hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 8 := by
    simpa using hkey
  let s₁ := s.write .x .x9 K
  have e₁ : exec (.ldr .x .x9 .x5 0) s = some s₁ := by
    rw [exec_ldr_x ⟨by decide, by decide⟩ hk0]; simp [s₁, K]
  let s₂ := s₁.setV keyReg (ofVDwords (s₁.gpr .x9) (s₁.gpr .x9))
  have e₂ : exec (.vop (.dup .d2 keyReg .x9)) s₁ = some s₂ := rfl
  have x9₁ : s₁.gpr .x9 = K := by simp [s₁, State.write]
  have x5₂ : s₂.gpr .x5 = s.gpr .x5 := by simp [s₂, s₁, State.write, State.setV]
  let s₃ := s₂.write .x .x5 (nextKey d (s.gpr .x5))
  have e₃ : exec (if d = .encrypt then .addImm .x .x5 .x5 8 else .subImm .x .x5 .x5 8) s₂ =
      some s₃ := by
    cases d
    · simp only [ite_true, exec_addImm_x (show 8 < 4096 by decide)]
      simp only [s₃, nextKey, ite_true, State.read, BitVec.setWidth_eq, x5₂]; rfl
    · simp only [reduceCtorEq, ite_false, exec_subImm_x (show 8 < 4096 by decide)]
      simp only [s₃, nextKey, State.read, BitVec.setWidth_eq, x5₂, reduceCtorEq, ite_false]; rfl
  refine ⟨s₃, ?_, ?_, by simp [s₃, State.write], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      e₃, runStep_some, runBlock_nil]
  · show s₂.v keyReg = _; rw [v_setV_self, x9₁]
  · simp [s₃, s₂, s₁, State.write, State.setV, h1, h2]
  · show s₂.v y = s.v y; rw [v_setV_of_ne _ _ hy]; rfl

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) {K : BitVec 64} {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hk : KeyRegs K s) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, hk, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega_using [hn])
    have h₁ := room_congr h (by rw [g₁]) wr₁
    obtain ⟨s₂, run₂, w₂, k₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := sboxStep_ok ρ (by omega_using [hn] : n < 8) h₁ k₁
    refine ⟨s₂, ?_, fun x hx => ?_, k₂, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact step_congr ρ _ (by omega_using [hn]) w₁ (w₁ x hx)
    · rw [show stateR s₁ = stateR s by simp only [stateR, g₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) (hz : s.v zeroReg = 0)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW (s.gpr .x5) 64).setWidth 48) (words s) x) ∧
      s'.gpr .x5 = nextKey d (s.gpr .x5) ∧ (∀ r, r ≠ .x9 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.v zeroReg = 0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, x5₁, g₁, m₁, rd₁, wr₁, sp₁, v₁⟩ := keyLoad_ok d hkey
  have h₁ := room_congr h (g₁ _ (by decide) (by decide)) wr₁
  have kr : KeyRegs (s.mem.readW (s.gpr .x5) 64) s₁ := ⟨k₁, by rw [v₁ _ (by decide), hz]⟩
  obtain ⟨s₂, run₂, w₂, k₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := stepsCode_ok ρ (Nat.le_refl 8) h₁ kr
  refine ⟨s₂, ?_, fun x hx => ?_, by rw [g₂, x5₁], fun r h1 h2 => by rw [g₂, g₁ r h1 h2], k₂.zero,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    have e : ∀ y, words s₁ y = words s y := fun y => by
      simp only [words, m₁, g₁ .x4 (by decide) (by decide)]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [show stateR s₁ = stateR s by simp only [stateR, g₁ .x4 (by decide) (by decide)], m₁] at f₂
    exact f₂

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-!
# An AdvSIMD DES pass on the machine

A pass with schedule component `c` in direction `d` points `x5` at its
first round key, runs eight pairs of rounds (counted in `x7`), stepping
the pointer by 8 in its direction, and exchanges the halves. `pass_ok`: it
does to the state words what `passW` does with that component of the
schedule at `x0`, which is readable and apart from the state words.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Impl.TripleDes.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW passW roundW_congr pairs_congr swapW_congr)

/-- The schedule at `x0`: readable, and apart from the state words. -/
structure Sched (s : State) : Prop where
  read : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8
  sep : (⟨s.gpr .x0, 384⟩ : Region).Disjoint (stateR s)

theorem Sched.congr {s s' : State} (h : Sched s) (h0 : s'.gpr .x0 = s.gpr .x0)
    (h4 : s'.gpr .x4 = s.gpr .x4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Sched s' where
  read i hi := by rw [h0, hrd, hwr]; exact h.read i hi
  sep := by simp only [stateR, h0, h4]; exact h.sep

/-- The index in the schedule of round `r`'s key of component `c`, in direction `d`. -/
def keyIdx (c : Nat) (d : Direction) (r : Nat) : Nat :=
  16 * c + if d = .encrypt then r else 15 - r

/-- The address of round `r`'s key. -/
def keyA (S : Addr) (c : Nat) (d : Direction) (r : Nat) : Addr :=
  S + BitVec.ofNat 64 (8 * keyIdx c d r)

theorem keyIdx_lt {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    keyIdx c d r < 48 := by
  unfold keyIdx; split <;> omega_arith

theorem keyA_succ (S : Addr) (c : Nat) (d : Direction) {r : Nat} (hr : r < 15) :
    nextKey d (keyA S c d r) = keyA S c d (r + 1) := by
  cases d
  · simp only [nextKey, keyA, keyIdx, ite_true]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => S + BitVec.ofNat 64 i) (by omega_arith)
  · simp only [nextKey, keyA, keyIdx, reduceCtorEq, ite_false]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_ofNat_sub _ (by omega_arith)]
    exact congrArg (fun i => S + BitVec.ofNat 64 i) (by omega_arith)

theorem Sched.key {s : State} (h : Sched s) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat}
    (hr : r < 16) : InRegions (s.rd ++ s.wr) (keyA (s.gpr .x0) c d r) 8 :=
  h.read _ (keyIdx_lt hc d hr)

theorem Sched.keySep {s : State} (h : Sched s) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat}
    (hr : r < 16) : (⟨keyA (s.gpr .x0) c d r, 8⟩ : Region).Disjoint (stateR s) :=
  h.sep.sub_left (Offset.sub_base _ (by have := keyIdx_lt hc d hr; omega_arith))

theorem keyA_roundKey (m : Mem) (S : Addr) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat}
    (hr : r < 16) :
    (m.readW (keyA S c d r) 64).setWidth 48 = roundKey (componentSchedule (scheduleAt m S) c) d r := by
  simp only [roundKey, keyA, keyIdx]
  rw [componentSchedule_readW m S c _ hc (by split <;> omega_arith)]

/-! ## Counting down `x7` -/

theorem sub1_run (s : State) :
    ∃ s', runBlock isa [.subImm .x .x7 .x7 1] s = some s' ∧ s'.gpr .x7 = s.gpr .x7 - 1 ∧
      (∀ r, r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.v = s.v := by
  refine ⟨s.write .x .x7 (s.read .x .x7 - BitVec.ofNat _ 1), ?_, ?_, fun r h => ?_, rfl, rfl, rfl,
    rfl, rfl⟩
  · rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · simp [State.write, State.read]
  · simp [State.write, h]

theorem cnt_sub (m : Nat) (h : 1 ≤ m) : BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  have e : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  rw [e, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h]

/-! ## A pair of rounds -/

theorem roundPair_eq (d : Direction) :
    roundPair d = round d .ba ++ round d .ab ++ ([.subImm .x .x7 .x7 1] : List Instr) := rfl

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) (hz : s.v zeroReg = 0)
    (h₁ : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8)
    (h₂ : InRegions (s.rd ++ s.wr) (nextKey d (s.gpr .x5)) 8)
    (sep₂ : (⟨nextKey d (s.gpr .x5), 8⟩ : Region).Disjoint (stateR s)) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (nextKey d (s.gpr .x5)) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (s.gpr .x5) 64).setWidth 48) (words s)) x) ∧
      s'.gpr .x5 = nextKey d (nextKey d (s.gpr .x5)) ∧ s'.gpr .x7 = s.gpr .x7 - 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.v zeroReg = 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, k₁, g₁, z₁, rd₁, wr₁, sp₁, f₁⟩ := round_ok d .ba h hz h₁
  have x4₁ := g₁ .x4 (by decide) (by decide)
  have h₁' := room_congr h x4₁ wr₁
  obtain ⟨s₂, run₂, w₂, k₂, g₂, z₂, rd₂, wr₂, sp₂, f₂⟩ :=
    round_ok d .ab h₁' z₁ (by rw [k₁, rd₁, wr₁]; exact h₂)
  obtain ⟨s₃, run₃, c₃, g₃, m₃, rd₃, wr₃, sp₃, v₃⟩ := sub1_run s₂
  have st₁ : stateR s₁ = stateR s := by simp only [stateR, x4₁]
  have kread : s₁.mem.readW (nextKey d (s.gpr .x5)) 64 = s.mem.readW (nextKey d (s.gpr .x5)) 64 :=
    f₁.readW (Region.contains_self _ _) (by simpa using sep₂) (by decide)
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, fun r a b c => ?_, by rw [v₃, z₂], rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [roundPair_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · have e : words s₃ x = words s₂ x := by simp only [words, m₃, g₃ .x4 (by decide)]
    rw [e, w₂ x hx, k₁, kread]
    exact roundW_congr .ab _ w₁ x hx
  · rw [g₃ _ (by decide), k₂, k₁]
  · rw [c₃, g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide)]
  · rw [g₃ r c, g₂ r a b, g₁ r a b]
  · rw [st₁] at f₂
    rw [m₃]
    exact f₁.trans f₂

/-! ## The loop of pairs of rounds -/

/-- The keys of the pass. -/
abbrev passKeys (s₀ : State) (c : Nat) (d : Direction) : Nat → BitVec 48 :=
  roundKey (componentSchedule (scheduleAt s₀.mem (s₀.gpr .x0)) c) d

structure LoopInv (c : Nat) (d : Direction) (s₀ : State) (m : Nat) (s : State) : Prop where
  room : Room s
  zero : s.v zeroReg = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, words s x = pairs (passKeys s₀ c d) (8 - m) (words s₀) x
  key : s.gpr .x5 = keyA (s₀.gpr .x0) c d (2 * (8 - m))
  cnt : s.gpr .x7 = BitVec.ofNat 64 m
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s.gpr r = s₀.gpr r
  frame : Frame [stateR s₀] s₀.mem s.mem

structure LoopPost (c : Nat) (d : Direction) (s₀ s : State) : Prop where
  room : Room s
  zero : s.v zeroReg = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  words : ∀ x < 64, words s x = pairs (passKeys s₀ c d) 8 (words s₀) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s.gpr r = s₀.gpr r
  frame : Frame [stateR s₀] s₀.mem s.mem

theorem pairLoop_ok {c : Nat} (hc : c < 3) (d : Direction) {s₀ : State} (hS : Sched s₀)
    (m₀ : Nat) (s₁ : State) (hs₁ : LoopInv c d s₀ m₀ s₁) :
    WP isa (.loop (.block (roundPair d)) (.nonzero .x .x7)) s₁ (LoopPost c d s₀) := by
  refine WP.loop (M := isa) (LoopInv c d s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let S := s₀.gpr .x0
  have h4 : s.gpr .x4 = s₀.gpr .x4 := hs.gpr _ (by decide) (by decide) (by decide)
  have st : stateR s = stateR s₀ := by simp only [stateR, h4]
  have r₀ : 2 * (8 - m) < 16 := by omega_using [hs.pos]
  have r₁ : 2 * (8 - m) + 1 < 16 := by omega_using [hs.pos]
  have a₁ : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8 := by
    rw [hs.key, hs.rd, hs.wr]; exact hS.key hc d r₀
  have nk : nextKey d (s.gpr .x5) = keyA S c d (2 * (8 - m) + 1) := by
    rw [hs.key]; exact keyA_succ S c d (by omega_arith)
  have a₂ : InRegions (s.rd ++ s.wr) (nextKey d (s.gpr .x5)) 8 := by
    rw [nk, hs.rd, hs.wr]; exact hS.key hc d r₁
  have sep₂ : (⟨nextKey d (s.gpr .x5), 8⟩ : Region).Disjoint (stateR s) := by
    rw [nk, st]; exact hS.keySep hc d r₁
  obtain ⟨s', run', w', key', cnt', g', z', rd', wr', sp', f'⟩ :=
    roundPair_ok d hs.room hs.zero a₁ a₂ sep₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  have frame' : Frame [stateR s₀] s₀.mem s'.mem := by
    rw [st] at f'; exact hs.frame.trans f'
  have rk : ∀ r < 16, (s.mem.readW (keyA S c d r) 64).setWidth 48 = passKeys s₀ c d r := by
    intro r hr
    have e := hs.frame.readW (a := keyA S c d r) (w := 64) (r := ⟨keyA S c d r, 8⟩)
      (Region.contains_self _ _) (by simpa using hS.keySep hc d hr) (by decide)
    rw [e]; exact keyA_roundKey _ _ hc d hr
  have words' : ∀ x < 64, words s' x = pairs (passKeys s₀ c d) (8 - m + 1) (words s₀) x := by
    intro x hx
    rw [w' x hx, nk, hs.key, rk _ r₀, rk _ r₁]
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ hs.words) x hx
  have gpr' : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s₀.gpr r :=
    fun r a b c => (g' r a b c).trans (hs.gpr r a b c)
  have room' := room_congr hs.room (g' _ (by decide) (by decide) (by decide)) wr'
  have cntv : s'.gpr .x7 = BitVec.ofNat 64 (m - 1) := by rw [cnt', hs.cnt]; exact cnt_sub m hs.pos
  have hm8 := hs.le
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', z', rd'.trans hs.rd, wr'.trans hs.wr, sp'.trans hs.sp, words', gpr', frame'⟩⟩
    show some (s'.read .x .x7 != 0) = some false
    simp [State.read, cntv]
  · right
    refine ⟨?_, m - 1, by omega_arith, ⟨room', z', rd'.trans hs.rd, wr'.trans hs.wr, sp'.trans hs.sp,
      by omega_arith, by omega_arith, ?_, ?_, cntv, gpr', frame'⟩⟩
    · show some (s'.read .x .x7 != 0) = some true
      have hne : BitVec.ofNat 64 (m - 1) ≠ 0 := by
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        simp at this
        omega_arith
      simp [State.read, cntv]
      exact hne
    · rw [show 8 - (m - 1) = 8 - m + 1 by omega_arith]; exact words'
    · rw [key', nk, keyA_succ S c d (by omega_arith)]
      congr 1; omega_arith

/-! ## A pass -/

theorem passOff (c : Nat) (hc : c < 3) (d : Direction) :
    (128 * c + if d = .encrypt then 0 else 120) < 4096 ∧
      BitVec.ofNat 64 (128 * c + if d = .encrypt then 0 else 120) =
        BitVec.ofNat 64 (8 * keyIdx c d 0) := by
  constructor
  · split <;> omega_arith
  · simp only [keyIdx]; split <;> (congr 1; omega_arith)

structure PassPost (c : Nat) (d : Direction) (s s' : State) : Prop where
  room : Room s'
  zero : s'.v zeroReg = 0
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  words : ∀ x < 64, words s' x = passW (componentSchedule (scheduleAt s.mem (s.gpr .x0)) c) d
    (words s) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r
  frame : Frame [stateR s] s.mem s'.mem

theorem pass_ok {c : Nat} (hc : c < 3) (d : Direction) {s : State} (h : Room s)
    (hz : s.v zeroReg = 0) (hS : Sched s) : WP isa (pass c d) s (PassPost c d s) := by
  obtain ⟨hoff, heq⟩ := passOff c hc d
  let s₁ := s.write .x .x5 (s.read .x .x0 + BitVec.ofNat _ (128 * c + if d = .encrypt then 0 else 120))
  let s₂ := s₁.write .x .x7 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))
  have run₁ : runBlock isa [.addImm .x .x5 .x0 (128 * c + if d = .encrypt then 0 else 120),
      .movz .x .x7 8 0] s = some s₂ := by
    rw [runBlock_cons, exec_addImm_x hoff, runStep_some, runBlock_cons]
    simp only [exec, Size.bits, show 16 * 0 < 64 by decide, ite_true, runStep_some, runBlock_nil]
    rfl
  have g₂ : ∀ r, r ≠ .x5 → r ≠ .x7 → s₂.gpr r = s.gpr r := by
    intro r a b; simp [s₂, s₁, State.write, a, b]
  have x5₂ : s₂.gpr .x5 = keyA (s.gpr .x0) c d 0 := by
    simp [s₂, s₁, State.write, State.read, keyA, heq]
  have x7₂ : s₂.gpr .x7 = BitVec.ofNat 64 8 := by simp [s₂, State.write]
  have h₂ : Room s₂ := room_congr h (g₂ _ (by decide) (by decide)) rfl
  have S₂ : Sched s₂ := hS.congr (g₂ _ (by decide) (by decide)) (g₂ _ (by decide) (by decide)) rfl rfl
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, run₁, ?_⟩
  apply WP.seq
  have inv : LoopInv c d s₂ 8 s₂ := ⟨h₂, hz, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl,
    by simpa using x5₂.trans (by rw [g₂ _ (by decide) (by decide)]), x7₂,
    fun _ _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (pairLoop_ok hc d S₂ 8 s₂ inv)
  intro s₃ p₃
  obtain ⟨s₄, run₄, w₄, g₄, -, z₄, rd₄, wr₄, sp₄, -, f₄⟩ := swapHalves_ok p₃.room
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s₃.gpr r = s.gpr r :=
    fun r a b c => (p₃.gpr r a b c).trans (g₂ r b c)
  have st₃ : stateR s₃ = stateR s := by simp only [stateR, g₃ .x4 (by decide) (by decide) (by decide)]
  have st₂ : stateR s₂ = stateR s := by simp only [stateR, g₂ .x4 (by decide) (by decide)]
  refine ⟨room_congr p₃.room (by rw [g₄]) wr₄, by rw [z₄, p₃.zero], rd₄.trans p₃.rd,
    wr₄.trans p₃.wr, sp₄.trans p₃.sp, fun x hx => ?_, fun r a b c => by rw [g₄, g₃ r a b c], ?_⟩
  · rw [w₄ x hx]
    have hx0 : s₂.gpr .x0 = s.gpr .x0 := g₂ _ (by decide) (by decide)
    have hk : passKeys s₂ c d = passKeys s c d := by
      rw [passKeys, passKeys, hx0]; rfl
    refine swapW_congr (fun y hy => ?_) x hx
    rw [p₃.words y hy, hk]
    exact pairs_congr _ 8 (fun z _ => by
      simp only [words, g₂ .x4 (by decide) (by decide)]; rfl) y hy
  · rw [st₃] at f₄
    have f₃ := p₃.frame
    rw [st₂] at f₃
    exact f₃.trans f₄

end VG.Proof.TripleDes.AArch64.BitslicedNeon
