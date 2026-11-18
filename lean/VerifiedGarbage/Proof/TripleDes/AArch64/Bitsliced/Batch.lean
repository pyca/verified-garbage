module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Sbox
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.TripleDes.Bitslice.TransposeIdx
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Step

/-! ### `TripleDes.AArch64.Bitsliced.Pass`, which this module and modules that import it used -/

section

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

end

end

/-! ### `TripleDes.AArch64.Bitsliced.Bytes`, which only this module used -/

section

/-!
# Blocks as little-endian words

A block's little-endian word holds bit `i` of the block (big-endian, as
`decodeBlock` reads it) at bit `i ^^^ 56`: the byte order is reversed.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

theorem xor56_lt {p : Nat} (hp : p < 64) : p ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hp (by decide)

theorem xor56_xor56 (a : Nat) : a ^^^ 56 ^^^ 56 = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem getLsbD_rev64' (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (rev64 x).getLsbD p = x.getLsbD (p ^^^ 56) := by
  rw [getLsbD_rev64 _ hp, xor56_eq p hp]

/-- The little-endian word of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (decodeBlock (blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [VG.Proof.TripleDes.AArch64.decodeBlock_readW, getLsbD_rev64' _ (xor56_lt hj), xor56_xor56]

/-- A word whose bits are those of `x` at `j ^^^ 56` is the little-endian word of
the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    blockAt m p = encodeBlock x := by
  have hw : m.readW p 64 = rev64 x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [h j hj, getLsbD_rev64' _ hj]
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m p (n := 8) hi]
  have e : (m.read p 8) = m.readW p 64 := by simp only [Mem.readW]; rfl
  rw [e, hw]
  exact VG.Proof.TripleDes.AArch64.rev64_byte x i hi

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-! ### `TripleDes.AArch64.Bitsliced.Transpose`, which only this module used -/

section

/-!
# The transposition of the AdvSIMD state

The 64 state words are the 16-byte slots at `x4`. The transposition runs
two stages of eight groups each, in loops: a group moves and XORs bits
within the doubleword lanes of eight words, masked with constants, so the
lane domain evaluates one group once, on words of atoms (bit `t` of word
`i` is atom `64 i + t`), for any base (`bodyA_check`, `bodyB_check`). The
first stage's group at word `i` exchanges the high three bits of the word
index and the bit index of the words `i + 8 k` (`stA`); the second's group
at word `8 g` exchanges the low three bits of those of the words `8 g + k`
(`stB`). Together they transpose the 64 doublewords of every lane
(`stB_stA`, `transpose_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Bitslice VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- Doubleword lane `q` of the 16-byte words at `D`. -/
def laneAt (m : Mem) (D : Addr) (q j : Nat) : BitVec 64 := vdword (m.readW (vAddr D j) 128) q

/-! ## The stages, on the lanes -/

/-- The first stage: bit `p` of word `j` is bit `(p mod 8) + 8 (j / 8)` of
word `(j mod 8) + 8 (p / 8)`. -/
def stA (W : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  ofBits 64 fun p => (W (j % 8 + 8 * ((p >>> 3) &&& 7))).getLsbD ((p &&& 7) ||| ((j / 8) <<< 3))

/-- The second stage: bit `p` of word `j` is bit `8 (p / 8) + (j mod 8)` of
word `8 (j / 8) + (p mod 8)`. -/
def stB (W : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  ofBits 64 fun p => (W (8 * (j / 8) + (p &&& 7))).getLsbD ((p &&& 56) ||| (j % 8))

theorem stB_stA_idx : ∀ j < 64, ∀ p < 64,
    (8 * (j / 8) + (p &&& 7)) % 8 + 8 * ((((p &&& 56) ||| (j % 8)) >>> 3) &&& 7) = p ∧
    ((((p &&& 56) ||| (j % 8)) &&& 7) ||| (((8 * (j / 8) + (p &&& 7)) / 8) <<< 3)) = j ∧
    ((p &&& 56) ||| (j % 8)) < 64 :=
  VG.Proof.TripleDes.Bitslice.stB_stA_idx

/-- The two stages transpose. -/
theorem stB_stA (W : Nat → BitVec 64) {j : Nat} (hj : j < 64) : stB (stA W) j = transposeW W j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  obtain ⟨e₁, e₂, e₃⟩ := stB_stA_idx j hj p hp
  simp only [stB, stA, transposeW, getLsbD_ofBits, hp, e₃, decide_true, Bool.true_and, e₁, e₂]

/-! ## One group, by evaluation -/

/-- The slots below `n`, each a word of atoms. -/
def envIn (n : Nat) : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if k < n then some (inWord k) else none }

/-- Bit `p` of slot `j` is atom `g j p`. -/
def postOut (n : Nat) (g : Nat → Nat → Nat) (e : Env (Nat × Nat)) : Bool :=
  (List.range n).all fun j => e.slot j == some (outWord fun p => [g j p])

/-- Code checked to move bit `g j p mod 64` of slot `g j p / 64` to bit `p` of
slot `j`, for the `n` slots at `x4`. -/
theorem group_run {n K : Nat} {is : List Instr} {g : Nat → Nat → Nat} {s : State}
    (hn : 64 * n ≤ 2 ^ K) (hg : ∀ j < n, ∀ p < 64, g j p < 64 * n)
    (hchk : check (lanes 64 K) ⟨.x4, n⟩ is (envIn n) (postOut n g) = true)
    (hok : Ok ⟨.x4, n⟩ s) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ q < 2, ∀ j < n, ∀ p < 64, (laneAt s'.mem (s.gpr .x4) q j).getLsbD p =
        (laneAt s.mem (s.gpr .x4) q (g j p / 64)).getLsbD (g j p % 64)) ∧
      (∀ r, (is.all fun i => !clobbers i r) = true → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨s.gpr .x4, 16 * n⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  have hrel : Rel (fun q => LaneRel K (assign (laneW s q) (2 ^ K))) ⟨.x4, n⟩ (envIn n) s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl q hq => ?_), (fun _ _ h => by cases h)⟩
    have hj' : j < n := hj
    simp only [envIn, hj', ↓reduceIte, Option.some.injEq] at hsl
    subst hsl
    exact inWord_rel (laneW s q) (by omega_arith)
  obtain ⟨s', hs', p⟩ := run (fun _ _ => lanes_sound) hok hrel he
  refine ⟨s', hs', fun q hq j hj b hb => ?_, fun r hr => p.gpr r (by simp [hr]), p.rd, p.wr, p.sp, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot j _ hj (beq_iff_eq.mp hpj) q hq
  have bits := outWord_rel (fun p hp a ha => by
    simp only [List.mem_singleton] at ha; subst ha; have := hg j hj p hp; omega_arith) hs
  have hb' : s'.gpr .x4 = s.gpr .x4 := p.base
  have hsj : laneAt s'.mem (s.gpr .x4) q j =
      vdword (s'.mem.readW (vAddr (s'.gpr (⟨.x4, n⟩ : Cfg).base) j) 128) q := by
    show _ = vdword (s'.mem.readW (vAddr (s'.gpr .x4) j) 128) q
    rw [hb']; rfl
  rw [hsj, bits b hb]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false]
  rfl

/-- A group of the first stage: the words `8 k` from `x4` of the 57 words. -/
def bodyA : List Instr := masks 8 ++ group (fun k => 8 * k) 8

/-- A group of the second stage: the eight words from `x4`. -/
def bodyB : List Instr := masks 1 ++ group (fun k => k) 1

def gA (j p : Nat) : Nat :=
  if j % 8 = 0 then 64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j / 8) <<< 3)) else 64 * j + p

def gB (j p : Nat) : Nat := 64 * (p &&& 7) + ((p &&& 56) ||| j)

theorem bodyA_check : check (lanes 64 12) ⟨.x4, 57⟩ bodyA (envIn 57) (postOut 57 gA) = true := by
  decide +kernel

theorem bodyB_check : check (lanes 64 9) ⟨.x4, 8⟩ bodyB (envIn 8) (postOut 8 gB) = true := by
  decide +kernel

theorem gA_lt : ∀ j < 57, ∀ p < 64, gA j p < 64 * 57 := by
  intro j hj p hp
  unfold gA
  split
  · have h1 : (p >>> 3) &&& 7 ≤ 7 := Nat.and_le_right
    have h2 : ((p &&& 7) ||| ((j / 8) <<< 3)) < 2 ^ 6 :=
      Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) (by rw [Nat.shiftLeft_eq]; omega_arith)
    omega_arith
  · omega_arith

theorem gB_lt : ∀ j < 8, ∀ p < 64, gB j p < 64 * 8 := by decide +kernel

theorem bodyA_nogpr : bodyA.all (fun op => (dsts op).all (· == .x10)) = true := by
  decide +kernel

theorem bodyB_nogpr : bodyB.all (fun op => (dsts op).all (· == .x10)) = true := by
  decide +kernel

theorem keeps_of_nogpr {is : List Instr} (h : is.all (fun op => (dsts op).all (· == .x10)) = true)
    {r : Reg} (hr : r ≠ .x10) : (is.all fun i => !clobbers i r) = true := by
  rw [List.all_eq_true] at h ⊢
  intro op hop
  simpa using clobbers_eq_false_of_all (h op hop) (by simpa using hr)

/-! ## Where a group is, in the state -/

theorem vAddr_add (D : Addr) (a k : Nat) : vAddr (vAddr D a) k = vAddr D (a + k) := by
  simp only [vAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

/-- The slots of a group, within the state's. -/
theorem ok_window {s₀ s : State} {D : Addr} (h₀ : Ok stateCfg s₀) (hD : s₀.gpr .x4 = D) {a n : Nat}
    (ha : a + n ≤ 64) (hb : s.gpr .x4 = vAddr D a) (hw : s.wr = s₀.wr) : Ok ⟨.x4, n⟩ s where
  slotIn k hk := by
    have hk' : k < n := hk
    show InRegions s.wr (vAddr (s.gpr .x4) k) 16
    rw [hb, vAddr_add, hw, ← hD]
    exact h₀.slotIn (a + k) (by show a + k < 64; omega_arith)
  slots := by show 16 * n < 2 ^ 64; omega_arith

/-- A word outside a group's slots is unchanged. -/
theorem lane_out {m m' : Mem} {D : Addr} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨vAddr D a, 16 * n⟩] m m') {j : Nat} (hj : j < 64) (hout : j < a ∨ a + n ≤ j) (q : Nat) :
    laneAt m' D q j = laneAt m D q j := by
  simp only [laneAt]
  rw [hf.readW (r := ⟨vAddr D j, 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]

/-- A word in a group's slots, from the group's view. -/
theorem lane_in (m : Mem) (D : Addr) (a q j : Nat) : laneAt m (vAddr D a) q j = laneAt m D q (a + j) := by
  simp only [laneAt, vAddr_add]

/-! ## The register steps -/

theorem addX_run (s : State) (r : Reg) {k : Nat} (hk : k < 4096) :
    ∃ s', runBlock isa [.addImm .x r r k] s = some s' ∧ s'.gpr r = s.gpr r + BitVec.ofNat 64 k ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨s.write .x r (s.read .x r + BitVec.ofNat _ k), by rw [runBlock_cons, exec_addImm_x hk]; rfl,
    ?_, fun r' h => gpr_write_of_ne _ _ _ h, rfl, rfl, rfl, rfl⟩
  simp [gpr_write_self, State.read]

theorem subX_run (s : State) (r : Reg) {k : Nat} (hk : k < 4096) :
    ∃ s', runBlock isa [.subImm .x r r k] s = some s' ∧ s'.gpr r = s.gpr r - BitVec.ofNat 64 k ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨s.write .x r (s.read .x r - BitVec.ofNat _ k), by rw [runBlock_cons, exec_subImm_x hk]; rfl,
    ?_, fun r' h => gpr_write_of_ne _ _ _ h, rfl, rfl, rfl, rfl⟩
  simp [gpr_write_self, State.read]

theorem movz8_run (s : State) (r : Reg) :
    ∃ s', runBlock isa [.movz .x r 8 0] s = some s' ∧ s'.gpr r = BitVec.ofNat 64 8 ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨s.write .x r (BitVec.ofNat 64 8), by rw [runBlock_cons]; rfl,
    by rw [gpr_write_self]; rfl, fun r' h => gpr_write_of_ne _ _ _ h, rfl, rfl, rfl, rfl⟩

theorem cnt8_sub (n : Nat) (h₁ : 1 ≤ n) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) :=
  BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h₁

theorem cnt8_zero : ∀ n < 8, (BitVec.ofNat 64 n != 0) = !decide (n = 0) := by decide

/-! ## The stages -/

/-- What every step of a stage keeps, from `s₀`, with the state words at `D`. -/
structure Keep (s₀ s : State) : Prop where
  gpr : ∀ r, r ≠ .x10 → r ≠ .x4 → r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [stateR s₀] s₀.mem s.mem

/-- A group's slots are in the state words. -/
theorem frame_state {s₀ : State} {m m' : Mem} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨vAddr (s₀.gpr .x4) a, 16 * n⟩] m m') : Frame [stateR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_arith)⟩

/-- A group's code, then `x4` past it and the count down: what each keeps. -/
theorem group_step {s : State} {body : List Instr} {step : Nat} (hst : step < 4096) {Q : State → Prop}
    {s₁ : State} (run₁ : runBlock isa body s = some s₁) (hk₁ : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r)
    (hsp₁ : s₁.sp = s.sp)
    (hQ : ∀ s₃ : State, s₃.mem = s₁.mem → s₃.rd = s₁.rd → s₃.wr = s₁.wr → s₃.sp = s.sp →
      s₃.gpr .x4 = s.gpr .x4 + BitVec.ofNat 64 step → s₃.gpr .x9 = s.gpr .x9 - BitVec.ofNat 64 1 →
      (∀ r, r ≠ .x10 → r ≠ .x4 → r ≠ .x9 → s₃.gpr r = s.gpr r) → Q s₃) :
    WP isa (.block (body ++ ([.addImm .x .x4 .x4 step, .subImm .x .x9 .x9 1] : List Instr))) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [show ([.addImm .x .x4 .x4 step, .subImm .x .x9 .x9 1] : List Instr) =
    [.addImm .x .x4 .x4 step] ++ [.subImm .x .x9 .x9 1] from rfl, WP.block_append_iff]
  obtain ⟨s₂, run₂, si₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := addX_run s₁ .x4 hst
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, c₃, g₃, m₃, rd₃, wr₃, sp₃⟩ := subX_run s₂ .x9 (k := 1) (by decide)
  refine WP.of_runBlock ⟨s₃, run₃, hQ s₃ (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂)
    (sp₃.trans (sp₂.trans hsp₁)) ?_ ?_ ?_⟩
  · rw [g₃ _ (by decide), si₂, hk₁ _ (by decide)]
  · rw [c₃, g₂ _ (by decide), hk₁ _ (by decide)]
  · intro r a b c; rw [g₃ r c, g₂ r b, hk₁ r a]

theorem vAddr_succ (D : Addr) (i : Nat) (k : Nat) :
    vAddr D i + BitVec.ofNat 64 (16 * k) = vAddr D (i + k) := by
  simp only [vAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

/-- After the groups below `8 - n` of the first stage. -/
structure InvA (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  pos : 1 ≤ n
  le : n ≤ 8
  x4 : s.gpr .x4 = vAddr (s₀.gpr .x4) (8 - n)
  x9 : s.gpr .x9 = BitVec.ofNat 64 n
  lanes : ∀ q < 2, ∀ j < 64, laneAt s.mem (s₀.gpr .x4) q j =
    if j % 8 < 8 - n then stA (laneW s₀ q) j else laneW s₀ q j

/-- The first stage, done. -/
structure DoneA (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  x4 : s.gpr .x4 = vAddr (s₀.gpr .x4) 8
  lanes : ∀ q < 2, ∀ j < 64, laneAt s.mem (s₀.gpr .x4) q j = stA (laneW s₀ q) j

theorem gA_idx : ∀ k < 8, ∀ p < 64, ((p &&& 7) ||| (k <<< 3)) < 64 ∧ ((p >>> 3) &&& 7) < 8 := by
  decide +kernel

theorem gB_idx : ∀ k < 8, ∀ p < 64, ((p &&& 56) ||| k) < 64 ∧ (p &&& 7) < 8 := by
  decide +kernel

theorem eval_nz (s : State) : isa.eval (.nonzero .x .x9) s = some (s.gpr .x9 != 0) := by
  show some (s.read .x .x9 != 0) = _
  simp [State.read]

theorem stageA_step {s₀ : State} (h₀ : Ok stateCfg s₀) {n : Nat} {s : State} (hs : InvA s₀ n s) :
    WP isa (.block (stageBody (fun k => 8 * k) 8 16)) s fun s' =>
      (isa.eval (.nonzero .x .x9) s' = some false ∧ DoneA s₀ s') ∨
      (isa.eval (.nonzero .x .x9) s' = some true ∧ ∃ m < n, InvA s₀ m s') := by
  let D := s₀.gpr .x4
  have hn₁ := hs.pos
  have hn₂ := hs.le
  have hok := ok_window (a := 8 - n) (n := 57) h₀ rfl (by omega_arith) hs.x4 hs.keep.wr
  obtain ⟨s₁, run₁, l₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := group_run (by decide) gA_lt bodyA_check hok
  rw [show stageBody (fun k => 8 * k) 8 16 =
    bodyA ++ ([.addImm .x .x4 .x4 16, .subImm .x .x9 .x9 1] : List Instr) by
      simp only [stageBody, bodyA, List.append_assoc]]
  refine group_step (by decide) run₁ (fun r hr => k₁ r (keeps_of_nogpr bodyA_nogpr hr)) sp₁
    fun s₃ m₃ rd₃ wr₃ sp₃ si₃ c₃ g₃ => ?_
  rw [hs.x4] at f₁ l₁
  -- the lanes after this group
  have lanes₃ : ∀ q < 2, ∀ j < 64, laneAt s₃.mem D q j =
      if j % 8 < 8 - n + 1 then stA (laneW s₀ q) j else laneW s₀ q j := by
    intro q hq j hj
    rw [m₃]
    by_cases hw : 8 - n ≤ j ∧ j < 8 - n + 57
    · obtain ⟨j', rfl⟩ : ∃ j', j = 8 - n + j' := ⟨j - (8 - n), by omega_arith⟩
      have hj' : j' < 57 := by omega_arith
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [← lane_in, l₁ q hq j' hj' p hp, lane_in]
      by_cases h8 : j' % 8 = 0
      · obtain ⟨e₁, e₂⟩ := gA_idx (j' / 8) (by omega_arith) p hp
        have eg : gA j' p = 64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j' / 8) <<< 3)) := by
          simp only [gA, h8, ↓reduceIte]
        rw [eg, show (64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j' / 8) <<< 3))) / 64 =
            8 * ((p >>> 3) &&& 7) by omega_arith,
          show (64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j' / 8) <<< 3))) % 64 =
            ((p &&& 7) ||| ((j' / 8) <<< 3)) by omega_arith,
          hs.lanes q hq _ (by omega_arith)]
        have c₁ : ¬ (8 - n + 8 * ((p >>> 3) &&& 7)) % 8 < 8 - n := by omega_arith
        have c₂ : (8 - n + j') % 8 < 8 - n + 1 := by omega_arith
        simp only [c₁, c₂, ↓reduceIte, stA, getLsbD_ofBits, hp, decide_true, Bool.true_and]
        rw [show (8 - n + j') % 8 = 8 - n by omega_arith, show (8 - n + j') / 8 = j' / 8 by omega_arith]
      · have eg : gA j' p = 64 * j' + p := by simp only [gA, h8, ↓reduceIte]
        rw [eg, show (64 * j' + p) / 64 = j' by omega_arith, show (64 * j' + p) % 64 = p by omega_arith,
          hs.lanes q hq _ hj]
        have : ((8 - n + j') % 8 < 8 - n) = ((8 - n + j') % 8 < 8 - n + 1) := by
          apply propext; constructor <;> intro h <;> omega_arith
        simp only [this]
    · rw [lane_out (by omega_arith) f₁ hj (by omega_arith) q, hs.lanes q hq j hj]
      have : (j % 8 < 8 - n) = (j % 8 < 8 - n + 1) := by
        apply propext; constructor <;> intro h <;> omega_arith
      simp only [this]
  have keep₃ : Keep s₀ s₃ :=
    ⟨fun r a b c => (g₃ r a b c).trans (hs.keep.gpr r a b c), rd₃.trans (rd₁.trans hs.keep.rd),
      wr₃.trans (wr₁.trans hs.keep.wr), sp₃.trans hs.keep.sp, hs.keep.frame.trans (m₃ ▸ frame_state (by omega_arith) f₁)⟩
  have rsi₃ : s₃.gpr .x4 = vAddr D (8 - n + 1) := by
    rw [si₃, hs.x4, show BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 1) from rfl]
    exact vAddr_succ D (8 - n) 1
  have cnt : s.gpr .x9 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.x9]; exact cnt8_sub n hn₁
  rw [eval_nz, c₃, cnt, cnt8_zero (n - 1) (by omega_arith)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, rsi₃, fun q hq j hj => ?_⟩
    have c : j % 8 < 8 - 1 + 1 := by omega_arith
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp; omega_arith, n - 1, by omega_arith, keep₃, by omega_arith, by omega_arith,
      by rw [rsi₃]; congr 1; omega_arith, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega_arith]

/-- Before the second stage: the first done, `x4` back at the state words. -/
structure PreB (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  x4 : s.gpr .x4 = s₀.gpr .x4
  lanes : ∀ q < 2, ∀ j < 64, laneAt s.mem (s₀.gpr .x4) q j = stA (laneW s₀ q) j

/-- After the groups below `8 - n` of the second stage. -/
structure InvB (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  pos : 1 ≤ n
  le : n ≤ 8
  x4 : s.gpr .x4 = vAddr (s₀.gpr .x4) (8 * (8 - n))
  x9 : s.gpr .x9 = BitVec.ofNat 64 n
  lanes : ∀ q < 2, ∀ j < 64, laneAt s.mem (s₀.gpr .x4) q j =
    if j / 8 < 8 - n then stB (stA (laneW s₀ q)) j else stA (laneW s₀ q) j

/-- The second stage, done. -/
structure DoneB (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  x4 : s.gpr .x4 = vAddr (s₀.gpr .x4) 64
  lanes : ∀ q < 2, ∀ j < 64, laneAt s.mem (s₀.gpr .x4) q j = stB (stA (laneW s₀ q)) j

theorem stageB_step {s₀ : State} (h₀ : Ok stateCfg s₀) {n : Nat} {s : State} (hs : InvB s₀ n s) :
    WP isa (.block (stageBody (fun k => k) 1 128)) s fun s' =>
      (isa.eval (.nonzero .x .x9) s' = some false ∧ DoneB s₀ s') ∨
      (isa.eval (.nonzero .x .x9) s' = some true ∧ ∃ m < n, InvB s₀ m s') := by
  let D := s₀.gpr .x4
  have hn₁ := hs.pos
  have hn₂ := hs.le
  have hok := ok_window (a := 8 * (8 - n)) (n := 8) h₀ rfl (by omega_arith) hs.x4 hs.keep.wr
  obtain ⟨s₁, run₁, l₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := group_run (by decide) gB_lt bodyB_check hok
  rw [show stageBody (fun k => k) 1 128 =
    bodyB ++ ([.addImm .x .x4 .x4 128, .subImm .x .x9 .x9 1] : List Instr) by
      simp only [stageBody, bodyB, List.append_assoc]]
  refine group_step (by decide) run₁ (fun r hr => k₁ r (keeps_of_nogpr bodyB_nogpr hr)) sp₁
    fun s₃ m₃ rd₃ wr₃ sp₃ si₃ c₃ g₃ => ?_
  rw [hs.x4] at f₁ l₁
  have lanes₃ : ∀ q < 2, ∀ j < 64, laneAt s₃.mem D q j =
      if j / 8 < 8 - n + 1 then stB (stA (laneW s₀ q)) j else stA (laneW s₀ q) j := by
    intro q hq j hj
    rw [m₃]
    by_cases hw : 8 * (8 - n) ≤ j ∧ j < 8 * (8 - n) + 8
    · obtain ⟨j', rfl⟩ : ∃ j', j = 8 * (8 - n) + j' := ⟨j - 8 * (8 - n), by omega_arith⟩
      have hj' : j' < 8 := by omega_arith
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [← lane_in, l₁ q hq j' hj' p hp, lane_in]
      obtain ⟨e₁, e₂⟩ := gB_idx j' hj' p hp
      rw [show gB j' p / 64 = p &&& 7 by simp only [gB]; omega_arith,
        show gB j' p % 64 = (p &&& 56) ||| j' by simp only [gB]; omega_arith,
        hs.lanes q hq _ (by omega_arith)]
      have c₁ : ¬ (8 * (8 - n) + (p &&& 7)) / 8 < 8 - n := by omega_arith
      have c₂ : (8 * (8 - n) + j') / 8 < 8 - n + 1 := by omega_arith
      simp only [c₁, c₂, ↓reduceIte, stB, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      rw [show (8 * (8 - n) + j') / 8 = 8 - n by omega_arith, show (8 * (8 - n) + j') % 8 = j' by omega_arith]
    · rw [lane_out (by omega_arith) f₁ hj (by omega_arith) q, hs.lanes q hq j hj]
      have : (j / 8 < 8 - n) = (j / 8 < 8 - n + 1) := by
        apply propext; constructor <;> intro h <;> omega_arith
      simp only [this]
  have keep₃ : Keep s₀ s₃ :=
    ⟨fun r a b c => (g₃ r a b c).trans (hs.keep.gpr r a b c), rd₃.trans (rd₁.trans hs.keep.rd),
      wr₃.trans (wr₁.trans hs.keep.wr), sp₃.trans hs.keep.sp, hs.keep.frame.trans (m₃ ▸ frame_state (by omega_arith) f₁)⟩
  have rsi₃ : s₃.gpr .x4 = vAddr D (8 * (8 - n) + 8) := by
    rw [si₃, hs.x4, show BitVec.ofNat 64 128 = BitVec.ofNat 64 (16 * 8) from rfl]
    exact vAddr_succ D (8 * (8 - n)) 8
  have cnt : s.gpr .x9 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.x9]; exact cnt8_sub n hn₁
  rw [eval_nz, c₃, cnt, cnt8_zero (n - 1) (by omega_arith)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, by rw [rsi₃], fun q hq j hj => ?_⟩
    have c : j / 8 < 8 - 1 + 1 := by omega_arith
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp; omega_arith, n - 1, by omega_arith, keep₃, by omega_arith, by omega_arith,
      by rw [rsi₃]; congr 1; omega_arith, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega_arith]

theorem vAddr_zero (D : Addr) : vAddr D 0 = D := by simp [vAddr]

theorem stageA_ok {s₀ : State} (h₀ : Ok stateCfg s₀) :
    WP isa (stage (fun k => 8 * k) 8 16) s₀ (DoneA s₀) := by
  obtain ⟨s₁, run₁, c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ := movz8_run s₀ .x9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (InvA s₀) (fun n s hs => stageA_step h₀ hs) 8 s₁
    ⟨⟨fun r _ _ c => g₁ r c, rd₁, wr₁, sp₁, m₁ ▸ Frame.refl _ _⟩, by decide, by decide,
      by rw [g₁ _ (by decide), Nat.sub_self, vAddr_zero], by rw [c₁], fun q _ j _ => ?_⟩
  simp only [laneAt, m₁]; rfl

theorem stageB_ok {s₀ s : State} (h₀ : Ok stateCfg s₀) (hs : PreB s₀ s) :
    WP isa (stage (fun k => k) 1 128) s (DoneB s₀) := by
  obtain ⟨s₁, run₁, c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ := movz8_run s .x9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (InvB s₀) (fun n s hs => stageB_step h₀ hs) 8 s₁
    ⟨⟨fun r a b c => (g₁ r c).trans (hs.keep.gpr r a b c), rd₁.trans hs.keep.rd, wr₁.trans hs.keep.wr,
      sp₁.trans hs.keep.sp, m₁ ▸ hs.keep.frame⟩, by decide, by decide,
      by rw [g₁ _ (by decide), hs.x4, Nat.sub_self, Nat.mul_zero, vAddr_zero], by rw [c₁],
      fun q hq j hj => ?_⟩
  simp only [m₁]
  exact hs.lanes q hq j hj

/-- Each doubleword lane of the state words, transposed. Only `x10` (the
masks' constants), `x9` (the count of groups) and vector registers change,
and in memory only the state words. -/
theorem transpose_ok {s : State} (hok : Room s) :
    WP isa transpose s fun s' => (∀ q < 2, ∀ j < 64, laneW s' q j = transposeW (laneW s q) j) ∧
      (∀ r, r ≠ .x10 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  let D := s.gpr .x4
  refine WP.seq (WP.mono (stageA_ok hok) fun sA hA => ?_)
  obtain ⟨s₂, run₂, si₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := subX_run sA .x4 (k := 128) (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have pre : PreB s s₂ :=
    ⟨⟨fun r a b c => (g₂ r b).trans (hA.keep.gpr r a b c), rd₂.trans hA.keep.rd, wr₂.trans hA.keep.wr,
      sp₂.trans hA.keep.sp, m₂ ▸ hA.keep.frame⟩,
      by rw [si₂, hA.x4]; simp only [vAddr]; rw [show (16 * 8 : Nat) = 128 from rfl, BitVec.add_sub_cancel],
      fun q hq j hj => by rw [m₂]; exact hA.lanes q hq j hj⟩
  refine WP.seq (WP.mono (stageB_ok hok pre) fun sB hB => ?_)
  obtain ⟨s₄, run₄, si₄, g₄, m₄, rd₄, wr₄, sp₄⟩ := subX_run sB .x4 (k := 1024) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have rsi₄ : s₄.gpr .x4 = D := by
    rw [si₄, hB.x4]; simp only [vAddr]
    rw [show (16 * 64 : Nat) = 1024 from rfl, BitVec.add_sub_cancel]
  refine ⟨fun q hq j hj => ?_, fun r a b => ?_, sp₄.trans hB.keep.sp, rd₄.trans hB.keep.rd,
    wr₄.trans hB.keep.wr, m₄ ▸ hB.keep.frame⟩
  · show laneAt s₄.mem (s₄.gpr .x4) q j = _
    rw [rsi₄, m₄, hB.lanes q hq j hj, stB_stA _ hj]
  · by_cases hr : r = .x4
    · subst hr; exact rsi₄
    · rw [g₄ r hr]; exact hB.keep.gpr r a hr b

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-!
# An AdvSIMD batch

A batch of 128 blocks, in place: each doubleword lane `q` of the 64 state
words (the 1024 bytes at `x4`) is transposed, so that lane `64 q + i` of
the words is IP of block `2 i + q`; the three passes run; the lanes are
transposed back, and each block becomes its TDEA encryption or decryption
(`batch_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW ipLane_bit passW passW_congr tdeaW tdeaW_lane
  blockOut blockOut_cores ipLane_congr wAt)

/-! ## Doubleword lanes as blocks -/

/-- Doubleword `q` of state word `i` is block `2 i + q`. -/
theorem laneW_eq (s : State) {q i : Nat} (hq : q < 2) :
    laneW s q i = s.mem.readW (wAt (s.gpr .x4) (2 * i + q)) 64 := by
  simp only [laneW, words, vAddr]
  rw [← read16_readW, vdword_read16 _ _ hq, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show 16 * i + 8 * q = 8 * (2 * i + q) by omega_using []]

/-- Lane `64 q + i` of 128-bit words is lane `i` of their doublewords `q`. -/
theorem ipLane_dw {W : Nat → BitVec 128} {q i : Nat} (hi : i < 64) :
    ipLane W (64 * q + i) = ipLane (fun j => vdword (W j) q) i := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, getLsbD_vdword _ hi]

/-! ## The passes -/

/-- What the passes leave. -/
structure PassesPost (d : Direction) (s s' : State) : Prop where
  room : Room s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  words : ∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (s.gpr .x0)) d (words s) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r
  frame : Frame [stateR s] s.mem s'.mem

/-- A pass, followed by what is left of the passes, `Q`, of its result. -/
theorem pass_then {c : Nat} (hc : c < 3) (d : Direction) {s : State} (h : Room s)
    (hz : s.v zeroReg = 0) (hS : Sched s) {p : Prog isa} {Q : State → Prop}
    (k : ∀ s', PassPost c d s s' → WP isa p s' Q) : WP isa (.seq (pass c d) p) s Q :=
  WP.seq (WP.mono (pass_ok hc d h hz hS) k)

theorem PassPost.sched {c : Nat} {d : Direction} {s s' : State} (p : PassPost c d s s')
    (hS : Sched s) : Sched s' :=
  hS.congr (p.gpr _ (by decide) (by decide) (by decide)) (p.gpr _ (by decide) (by decide) (by decide))
    p.rd p.wr

theorem PassPost.schedule {c : Nat} {d : Direction} {s s' : State} (p : PassPost c d s s')
    (hS : Sched s) : scheduleAt s'.mem (s'.gpr .x0) = scheduleAt s.mem (s.gpr .x0) := by
  rw [p.gpr _ (by decide) (by decide) (by decide)]
  exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ p.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hS.sep

theorem PassPost.state {c : Nat} {d : Direction} {s s' : State} (p : PassPost c d s s') :
    stateR s' = stateR s := by
  simp only [stateR, p.gpr .x4 (by decide) (by decide) (by decide)]

theorem passes_ok (d : Direction) {s : State} (h : Room s) (hz : s.v zeroReg = 0)
    (hS : Sched s) : WP isa (passes d) s (PassesPost d s) := by
  cases d with
  | encrypt =>
    refine pass_then (by decide) .encrypt h hz hS fun s₁ p₁ => ?_
    refine pass_then (by decide) .decrypt p₁.room p₁.zero (p₁.sched hS) fun s₂ p₂ => ?_
    apply WP.mono (pass_ok (by decide) .encrypt p₂.room p₂.zero (p₂.sched (p₁.sched hS)))
    intro s₃ p₃
    have K₁ := p₁.schedule hS
    have K₂ := p₂.schedule (p₁.sched hS)
    refine ⟨p₃.room, p₃.rd.trans (p₂.rd.trans p₁.rd), p₃.wr.trans (p₂.wr.trans p₁.wr),
      p₃.sp.trans (p₂.sp.trans p₁.sp), fun x hx => ?_,
      fun r a b c => (p₃.gpr r a b c).trans ((p₂.gpr r a b c).trans (p₁.gpr r a b c)), ?_⟩
    · rw [p₃.words x hx, K₂, K₁]
      exact passW_congr _ _ (fun y hy => by
        rw [p₂.words y hy, K₁]; exact passW_congr _ _ p₁.words y hy) x hx
    · have f₂ := p₂.frame
      rw [p₁.state] at f₂
      have f₃ := p₃.frame
      rw [p₂.state, p₁.state] at f₃
      exact p₁.frame.trans (f₂.trans f₃)
  | decrypt =>
    refine pass_then (by decide) .decrypt h hz hS fun s₁ p₁ => ?_
    refine pass_then (by decide) .encrypt p₁.room p₁.zero (p₁.sched hS) fun s₂ p₂ => ?_
    apply WP.mono (pass_ok (by decide) .decrypt p₂.room p₂.zero (p₂.sched (p₁.sched hS)))
    intro s₃ p₃
    have K₁ := p₁.schedule hS
    have K₂ := p₂.schedule (p₁.sched hS)
    refine ⟨p₃.room, p₃.rd.trans (p₂.rd.trans p₁.rd), p₃.wr.trans (p₂.wr.trans p₁.wr),
      p₃.sp.trans (p₂.sp.trans p₁.sp), fun x hx => ?_,
      fun r a b c => (p₃.gpr r a b c).trans ((p₂.gpr r a b c).trans (p₁.gpr r a b c)), ?_⟩
    · rw [p₃.words x hx, K₂, K₁]
      exact passW_congr _ _ (fun y hy => by
        rw [p₂.words y hy, K₁]; exact passW_congr _ _ p₁.words y hy) x hx
    · have f₂ := p₂.frame
      rw [p₁.state] at f₂
      have f₃ := p₃.frame
      rw [p₂.state, p₁.state] at f₃
      exact p₁.frame.trans (f₂.trans f₃)

/-! ## The batch -/

structure BatchPost (d : Direction) (s s' : State) : Prop where
  out : ∀ b < 128, blockAt s'.mem (wAt (s.gpr .x4) b) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) d (blockAt s.mem (wAt (s.gpr .x4) b))
  gpr : ∀ r, r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [stateR s] s.mem s'.mem

theorem batch_ok (d : Direction) {s : State} (h : Room s) (hS : Sched s) :
    WP isa (batch d) s (BatchPost d s) := by
  let S := s.gpr .x0
  let D := s.gpr .x4
  rw [batch]
  -- the transposition, and zero
  refine WP.seq (WP.mono (transpose_ok h) fun s₁ ⟨w₁, g₁, sp₁, rd₁, wr₁, f₁⟩ => ?_)
  apply WP.seq
  let s₂ := s₁.setV zeroReg 0
  refine WP.of_runBlock ⟨s₂, (by
    rw [runBlock_cons]; exact (by rfl : runStep isa (some s₂) [] = some s₂)), ?_⟩
  have g₂ : ∀ r, r ≠ .x10 → r ≠ .x9 → s₂.gpr r = s.gpr r := g₁
  have h₂ : Room s₂ := room_congr h (g₂ _ (by decide) (by decide)) wr₁
  have S₂ : Sched s₂ := hS.congr (g₂ _ (by decide) (by decide)) (g₂ _ (by decide) (by decide)) rd₁ wr₁
  have st₂ : stateR s₂ = stateR s := by simp only [stateR, g₂ .x4 (by decide) (by decide)]
  apply WP.seq
  apply WP.mono (passes_ok d h₂ (v_setV_self _ _ _) S₂)
  intro s₃ q₃
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → r ≠ .x10 → s₃.gpr r = s.gpr r :=
    fun r a b c e => (q₃.gpr r a b c).trans (g₂ r e a)
  -- the transposition back
  refine WP.mono (transpose_ok q₃.room) fun s₄ ⟨w₄, g₄, sp₄, rd₄, wr₄, f₄⟩ => ?_
  have si₄ : s₄.gpr .x4 = D :=
    (g₄ .x4 (by decide) (by decide)).trans (g₃ _ (by decide) (by decide) (by decide) (by decide))
  have K₂ : scheduleAt s₂.mem (s₂.gpr .x0) = scheduleAt s.mem S := by
    rw [g₂ _ (by decide) (by decide)]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS.sep
  refine ⟨fun b hb => ?_, fun r a c e f => by rw [g₄ r f e, g₃ r e a c f], rd₄.trans (q₃.rd.trans rd₁),
    wr₄.trans (q₃.wr.trans wr₁), sp₄.trans (q₃.sp.trans sp₁), ?_⟩
  · have hq : b % 2 < 2 := Nat.mod_lt _ (by decide)
    have hi : b / 2 < 64 := by omega_using [hb]
    have eb : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
    -- lane 64 q + i before the passes: IP of the block
    have lane₂ : ipLane (words s₂) (64 * (b % 2) + b / 2) =
        permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [ipLane_dw hi]
      have e : ∀ j < 64, vdword (words s₂ j) (b % 2) = transposeW (laneW s (b % 2)) j := by
        intro j hj; exact w₁ _ hq j hj
      rw [ipLane_congr e]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hi fun j hj => ?_
      rw [laneW_eq s hq, eb]
      exact readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    have word₄ : s₄.mem.readW (wAt D b) 64 = transposeW (laneW s₃ (b % 2)) (b / 2) := by
      rw [← w₄ _ hq _ hi, laneW_eq s₄ hq, si₄, eb]
    rw [blockOut_cores, ← K₂]
    apply blockAt_of_readW
    intro j hj
    rw [word₄, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj]
    have e₃ : ipLane (laneW s₃ (b % 2)) (b / 2) = ipLane (words s₃) (64 * (b % 2) + b / 2) :=
      (ipLane_dw hi).symm
    rw [e₃, ipLane_congr q₃.words, tdeaW_lane _ d _ (by omega_using [hb]), lane₂]
  · have a : Frame [stateR s] s.mem s₂.mem := f₁
    have b : Frame [stateR s] s₂.mem s₃.mem := by rw [← st₂]; exact q₃.frame
    have c : Frame [stateR s] s₃.mem s₄.mem := by
      rw [show stateR s₃ = stateR s by
        simp only [stateR, g₃ .x4 (by decide) (by decide) (by decide) (by decide)]] at f₄
      exact f₄
    exact (a.trans b).trans c

end VG.Proof.TripleDes.AArch64.BitslicedNeon
