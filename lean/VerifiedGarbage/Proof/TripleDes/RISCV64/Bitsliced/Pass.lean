module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Step
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Bitsliced DES rounds and passes on RISC-V

`round_ok`: the code of a round loads the round key at the key pointer `a3`
into `a5`, steps the pointer by `δ d` (8 or −8) and does to the state words
what `roundW` does with the key's low 48 bits. `pass_ok`: a pass points
`a3` at its first key in the schedules' copy (`schedOff`), runs eight pairs
of rounds (counted down in `a4`) and exchanges the halves: what `passW`
does with the component schedule. `passes_ok`: the three passes do what
`tdeaW` does.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.RISCV64.Straight (wordAddr wordAddr_al)

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 64 := BitVec.ofInt 64 (if d = .encrypt then 8 else -8)

/-- The schedules' copy. -/
def schedA (s : State) : Addr := s.gpr .s0 + BitVec.ofNat 64 schedOff

/-- A round key's address: word `i < 48` of the schedules' copy. -/
def KeyAt (s : State) (A : Addr) : Prop := ∃ i < 48, A = schedA s + BitVec.ofNat 64 (8 * i)

theorem keyAt_addr {s : State} {A : Addr} (h : KeyAt s A) :
    ∃ i < 48, A = s.gpr .s0 + BitVec.ofNat 64 (schedOff + 8 * i) := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, Offset.add_add _ _ _⟩

theorem KeyAt.congr {s s' : State} {A : Addr} (h : KeyAt s A) (hb : s'.gpr .s0 = s.gpr .s0) : KeyAt s' A := by
  simp only [KeyAt, schedA, hb]; exact h

theorem keyAt_rd {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) :
    InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 0) 8 := by
  obtain ⟨i, hi, rfl⟩ := keyAt_addr hk
  rw [BitVec.add_zero]
  have := slot_in h (k := 64 + i) (by omega)
  simp only [wordAddr, schedOff] at this ⊢
  rw [show 512 + 8 * i = 8 * (64 + i) by omega]
  let ⟨r, hr, hc⟩ := this; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem keyAt_al {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) :
    (A + BitVec.ofNat 64 0).toNat % 8 = 0 := by
  obtain ⟨i, hi, rfl⟩ := keyAt_addr hk
  rw [BitVec.add_zero, show schedOff + 8 * i = 8 * (64 + i) by unfold schedOff; omega]
  exact wordAddr_al h.al _ (by omega)

/-- Round keys are apart from the state words. -/
theorem keyAt_apart {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) :
    (⟨A, 8⟩ : Region).Disjoint (stR s) := by
  obtain ⟨i, hi, rfl⟩ := keyAt_addr hk
  have := h.fit
  exact Offset.disjoint_base _ (by unfold schedOff; omega) (by unfold schedOff frameBytes at *; omega)

theorem stR_congr {s s' : State} (hb : s'.gpr .s0 = s.gpr .s0) : stR s' = stR s := by
  simp only [stR, hb]

/-! ## A round -/

theorem keyLoad_ok (d : Direction) {s : State} (h : Room s) {A : Addr} (hA : s.gpr .a3 = A)
    (hk : KeyAt s A) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧ s'.gpr .a5 = s.mem.readW A 64 ∧
      s'.gpr .a3 = A + δ d ∧ (∀ r, r ≠ .a5 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e₁ := exec_load_d (s := s) (t := .a5) (n := .a3) (off := 0) (by decide)
    (by rw [hA]; exact keyAt_al h hk) (by rw [hA]; exact keyAt_rd h hk)
  let s₁ := s.write .a5 (s.mem.readW (s.gpr .a3 + BitVec.ofNat 64 0) 64)
  have e₂ := exec_addi (s := s₁) (d := .a3) (n := .a3) (imm := if d = .encrypt then 8 else -8)
    (by cases d <;> decide)
  let s₂ := s₁.write .a3 (s₁.gpr .a3 + BitVec.ofInt 64 (if d = .encrypt then 8 else -8))
  have g3 : s₁.gpr .a3 = s.gpr .a3 := by simp [s₁, RegUpd.gpr_write]
  refine ⟨s₂, ?_, ?_, ?_, fun r h5 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [keyLoad, runBlock_cons, show key = .a5 from rfl, show keyPtr = .a3 from rfl, e₁, runStep_some,
      runBlock_cons, e₂, runStep_some, runBlock_nil]
  · simp [s₂, s₁, RegUpd.gpr_write, hA]
  · simp only [s₂, RegUpd.gpr_write, ite_true, g3, hA, δ]
  · simp [s₂, s₁, RegUpd.gpr_write, h5, h3]

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : ∀ b < 48, (s.gpr .a5).getLsbD b = k.getLsbD b) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega)
    have g0 : s₁.gpr .s0 = s.gpr .s0 := k₁ _ (by decide)
    have g5 : s₁.gpr .a5 = s.gpr .a5 := k₁ _ (by decide)
    obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, f₂⟩ :=
      sboxStep_ok ρ (j := n) (by omega) (h.congr g0 wr₁) k (by rw [g5]; exact hkey)
    refine ⟨s₂, ?_, fun x hx => ?_, fun r hr => by rw [k₂ r hr, k₁ r hr], rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega) w₁ (w₁ x hx)
    · rw [stR_congr g0] at f₂; exact f₁.trans f₂

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

/-- The registers a round leaves alone. -/
def roundKept : List Reg := [.s0, .a1, .a2, .a4]

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) {A : Addr} (hA : s.gpr .a3 = A)
    (hk : KeyAt s A) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW A 64).setWidth 48) (words s) x) ∧
      s'.gpr .a3 = A + δ d ∧ (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, p₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := keyLoad_ok d h hA hk
  have g0 : s₁.gpr .s0 = s.gpr .s0 := o₁ _ (by decide) (by decide)
  obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, f₂⟩ :=
    stepsCode_ok ρ ((s.mem.readW A 64).setWidth 48) (Nat.le_refl 8) (h.congr g0 wr₁)
      (fun b hb => by rw [k₁, BitVec.getLsbD_setWidth]; simp [hb])
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r hr => ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8)
      (fun y _ => by simp only [words, sl, m₁, g0]) x hx
  · rw [k₂ _ (by decide), p₁]
  · have hs : r ∈ stepKept ∧ r ≠ .a5 ∧ r ≠ .a3 := by
      simp only [roundKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [k₂ r hs.1, o₁ r hs.2.1 hs.2.2]
  · rw [stR_congr g0, m₁] at f₂; exact f₂

/-! ## Pairs of rounds -/

theorem roundPair_eq (d : Direction) :
    roundPair d = round d .ba ++ (round d .ab ++ ([.addi pairs pairs (-1)] : List Instr)) := by
  simp only [roundPair, List.append_assoc]

theorem Frame.readKey {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) {m : Mem}
    (hf : Frame [stR s] s.mem m) : m.readW A 64 = s.mem.readW A 64 :=
  hf.readW (Region.contains_self A 8) (by simpa using keyAt_apart h hk) (by decide)

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) {A : Addr} (hA : s.gpr .a3 = A)
    (hk₁ : KeyAt s A) (hk₂ : KeyAt s (A + δ d)) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (A + δ d) 64).setWidth 48)
        (roundW .ba ((s.mem.readW A 64).setWidth 48) (words s)) x) ∧
      s'.gpr .a3 = A + δ d + δ d ∧ s'.gpr .a4 = s.gpr .a4 + BitVec.ofInt 64 (-1) ∧
      (∀ r ∈ [Reg.s0, .a1, .a2], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, p₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := round_ok d .ba h hA hk₁
  have g0 : s₁.gpr .s0 = s.gpr .s0 := k₁ _ (by decide)
  have h₁ := h.congr g0 wr₁
  obtain ⟨s₂, run₂, w₂, p₂, k₂, rd₂, wr₂, sp₂, f₂⟩ := round_ok d .ab h₁ p₁ (hk₂.congr g0)
  have e₃ := exec_addi (s := s₂) (d := .a4) (n := .a4) (imm := -1) (by decide)
  have g4 : s₂.gpr .a4 = s.gpr .a4 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  refine ⟨s₂.write .a4 (s₂.gpr .a4 + BitVec.ofInt 64 (-1)), ?_, fun x hx => ?_, ?_, ?_, fun r hr => ?_,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [roundPair_eq]
    refine runBlock_cat_some run₁ (runBlock_cat_some run₂ ?_)
    rw [runBlock_cons, show Impl.TripleDes.RISCV64.Bitslice.pairs = Reg.a4 from rfl, e₃, runStep_some, runBlock_nil]
  · have : words (s₂.write .a4 (s₂.gpr .a4 + BitVec.ofInt 64 (-1))) x = words s₂ x := by
      simp only [words, sl, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [this, w₂ x hx]
    rw [Frame.readKey h hk₂ f₁]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, p₂]
  · simp only [RegUpd.gpr_write, ite_true, g4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_write, reduceCtorEq, ite_false] <;>
      rw [k₂ _ (by decide), k₁ _ (by decide)]
  · simp only [RegUpd.mem_write]
    rw [stR_congr g0] at f₂; exact f₁.trans f₂

/-! ## A pass -/

/-- The offset in the schedules' copy of a pass's first key. -/
def kOff (c : Nat) (d : Direction) : Nat := 128 * c + if d = .encrypt then 0 else 120

/-- The word of the component that is round `r`'s key. -/
def ix (d : Direction) (r : Nat) : Nat := if d = .encrypt then r else 15 - r

theorem kaddr : ∀ c < 3, ∀ d : Direction, ∀ r < 16,
    BitVec.ofNat 64 (kOff c d) + BitVec.ofNat 64 r * δ d = BitVec.ofNat 64 (8 * (16 * c + ix d r)) := by
  intro c hc d r hr
  cases d
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 64 (kOff c .encrypt) + BitVec.ofNat 64 r * δ .encrypt =
      BitVec.ofNat 64 (8 * (16 * c + ix .encrypt r))) c hc r hr
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 64 (kOff c .decrypt) + BitVec.ofNat 64 r * δ .decrypt =
      BitVec.ofNat 64 (8 * (16 * c + ix .decrypt r))) c hc r hr

theorem kptr_succ (a₀ δ : Addr) (r : Nat) :
    a₀ + BitVec.ofNat 64 r * δ + δ = a₀ + BitVec.ofNat 64 (r + 1) * δ := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul]
  exact congrArg (fun t => a₀ + (BitVec.ofNat 64 r * δ + t)) (BitVec.one_mul δ).symm

/-- The keys of a pass: the low 48 bits of the words at `P + r δ`. -/
def keyOf (m : Mem) (P δ : Addr) (r : Nat) : BitVec 48 :=
  (m.readW (P + BitVec.ofNat 64 r * δ) 64).setWidth 48

/-- The pass's first key's address. -/
def passP (s : State) (c : Nat) (d : Direction) : Addr := schedA s + BitVec.ofNat 64 (kOff c d)

theorem passKeyAt {s : State} {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    KeyAt s (passP s c d + BitVec.ofNat 64 r * δ d) := by
  refine ⟨16 * c + ix d r, by unfold ix; split <;> omega, ?_⟩
  rw [passP, BitVec.add_assoc, kaddr c hc d r hr]

theorem keyOf_pass (m : Mem) (s : State) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    keyOf m (passP s c d) (δ d) r = roundKey (componentSchedule (scheduleAt m (schedA s)) c) d r := by
  have hi : ix d r < 16 := by unfold ix; split <;> omega
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl, componentSchedule_readW m _ _ _ hc hi, keyOf, passP, BitVec.add_assoc, kaddr c hc d r hr]


/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (c : Nat) (d : Direction) (m : Nat) (s : State) : Prop where
  le : m ≤ 8
  s0 : s.gpr .s0 = s₀.gpr .s0
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = s₀.gpr .a2
  ptr : s.gpr .a3 = passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d
  cnt : s.gpr .a4 = BitVec.ofNat 64 (8 - m)
  wds : ∀ x < 64, words s x = VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP s₀ c d) (δ d)) m (words s₀) x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀] s₀.mem s.mem

theorem pair_step {s₀ : State} (h₀ : Room s₀) {c : Nat} (hc : c < 3) {d : Direction} {m : Nat} (hm : m < 8)
    {s : State} (I : PairInv s₀ c d m s) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧ PairInv s₀ c d (m + 1) s' := by
  have h : Room s := h₀.congr I.s0 I.wr
  have hk₁ := (passKeyAt (s := s₀) hc d (r := 2 * m) (by omega)).congr I.s0
  have hk₂ := (passKeyAt (s := s₀) hc d (r := 2 * m + 1) (by omega)).congr I.s0
  rw [← kptr_succ] at hk₂
  obtain ⟨s', run, w, p3, p4, k, rd, wr, sp, f⟩ := roundPair_ok d h I.ptr hk₁ hk₂
  have rk : ∀ r < 16, s.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 =
      s₀.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 := fun r hr => by
    have := Frame.readKey h₀ (passKeyAt (s := s₀) hc d hr) I.frame
    exact this
  refine ⟨s', run, ⟨by omega, (k _ (by decide)).trans I.s0, (k _ (by decide)).trans I.a1,
    (k _ (by decide)).trans I.a2, ?_, ?_, fun x hx => ?_, rd.trans I.rd, wr.trans I.wr, sp.trans I.sp, ?_⟩⟩
  · rw [p3, kptr_succ, kptr_succ]; congr 3
  · rw [p4, I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 64 (8 - m) + BitVec.ofInt 64 (-1) =
      BitVec.ofNat 64 (8 - (m + 1))) m hm
  · have e : passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d + δ d =
        passP s₀ c d + BitVec.ofNat 64 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega), rk _ (by omega)]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · have := I.frame.trans (by rw [← stR_congr I.s0]; exact f)
    exact this

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) {c : Nat} (hc : c < 3) (d : Direction) {s : State}
    (I : PairInv s₀ c d 0 s) :
    WP isa (.loop (.block (roundPair d)) (.nonzero pairs)) s (PairInv s₀ c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  obtain ⟨v', run, J'⟩ := pair_step h₀ hc hm J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show Impl.TripleDes.RISCV64.Bitslice.pairs = Reg.a4 from rfl, Steps.eval_nonzero_ofNat _ _ (by omega) J'.cnt]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right; exact ⟨by simp; omega, 8 - (m + 1), by omega, m + 1, by omega, rfl, J'⟩

/-- The registers a pass leaves alone. -/
def passKept : List Reg := [.s0, .a1, .a2]

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x = passW (componentSchedule (scheduleAt s.mem (schedA s)) c) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  unfold pass
  apply WP.seq
  have e₁ := exec_addi (s := s) (d := .a3) (n := .s0)
    (imm := ((schedOff : Int) + 128 * (c : Int) + if d = .encrypt then 0 else 120))
    (by cases d <;> (simp only [imm12, schedOff, reduceCtorEq, ite_true, ite_false]; omega))
  let s₁ := s.write .a3 (s.gpr .s0 +
    BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) + if d = .encrypt then 0 else 120))
  have e₂ := exec_li (s := s₁) (d := .a4) (imm := 8) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, show keyPtr = .a3 from rfl, show base = .s0 from rfl, e₁, runStep_some,
      runBlock_cons, show Impl.TripleDes.RISCV64.Bitslice.pairs = Reg.a4 from rfl, e₂, runStep_some, runBlock_nil], ?_⟩
  have hI : BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) + if d = .encrypt then 0 else 120) =
      BitVec.ofNat 64 schedOff + BitVec.ofNat 64 (kOff c d) := by
    cases d
    · exact (by decide : ∀ c : Nat, c < 3 → BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) +
        if Direction.encrypt = .encrypt then 0 else 120) =
        BitVec.ofNat 64 schedOff + BitVec.ofNat 64 (kOff c .encrypt)) c hc
    · exact (by decide : ∀ c : Nat, c < 3 → BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) +
        if Direction.decrypt = .encrypt then 0 else 120) =
        BitVec.ofNat 64 schedOff + BitVec.ofNat 64 (kOff c .decrypt)) c hc
  have z : BitVec.ofNat 64 (2 * 0) * δ d = 0#64 := by cases d <;> decide
  have I0 : PairInv s c d 0 (s₁.write .a4 (BitVec.ofInt 64 8)) := by
    refine ⟨by decide, by simp [s₁, RegUpd.gpr_write], by simp [s₁, RegUpd.gpr_write],
      by simp [s₁, RegUpd.gpr_write], ?_, by simp [RegUpd.gpr_write], fun x hx => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
    simp only [s₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, passP, schedA, z]
    rw [hI, BitVec.add_zero]
    exact (BitVec.add_assoc _ _ _).symm
  apply WP.seq
  refine WP.mono (pairLoop_ok h hc d I0) fun v J => ?_
  have hv : Room v := h.congr J.s0 J.wr
  obtain ⟨v', run, w, k, rd, wr, sp, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, fun r hr => ?_, rd.trans J.rd, wr.trans J.wr,
    sp.trans J.sp, ?_⟩
  · rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
    refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
    rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8 (fun r hr => keyOf_pass _ _ hc d hr)]
  · simp only [passKept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [k _ (by decide) (by decide), J.s0]
    · rw [k _ (by decide) (by decide), J.a1]
    · rw [k _ (by decide) (by decide), J.a2]
  · rw [stR_congr J.s0] at f; exact J.frame.trans f

/-! ## The three passes -/

theorem passes_ok (d : Direction) {s : State} (h : Room s) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (schedA s)) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  have step : ∀ (c : Nat) (hc : c < 3) (d' : Direction) {u : State}, Room u → schedA u = schedA s →
      scheduleAt u.mem (schedA s) = scheduleAt s.mem (schedA s) → u.gpr .s0 = s.gpr .s0 →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (schedA s)) c) d' (words u) x) → (∀ r ∈ passKept, u'.gpr r = u.gpr r) →
        u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → Frame [stR u] u.mem u'.mem → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u hu hA hK _ Q hQ
    refine WP.mono (pass_ok c hc d' hu) fun u' ⟨w, k, rd, wr, sp, f⟩ => hQ u' ?_ k rd wr sp f
    rw [hA, hK] at w; exact w
  have hK : ∀ {u : State}, u.gpr .s0 = s.gpr .s0 → Frame [stR s] s.mem u.mem →
      scheduleAt u.mem (schedA s) = scheduleAt s.mem (schedA s) := fun hb hf =>
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := h.fit
      exact Offset.disjoint_base _ (by unfold schedOff; omega) (by unfold schedOff frameBytes at *; omega)
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ h rfl rfl rfl fun u₁ w₁ k₁ rd₁ wr₁ sp₁ f₁ => ?_
    have g₁ : u₁.gpr .s0 = s.gpr .s0 := k₁ _ (by decide)
    have h₁ : Room u₁ := h.congr g₁ wr₁
    apply WP.seq
    refine step _ (by decide) _ h₁ (by simp only [schedA, g₁]) (hK g₁ f₁) g₁
      fun u₂ w₂ k₂ rd₂ wr₂ sp₂ f₂ => ?_
    have g₂ : u₂.gpr .s0 = s.gpr .s0 := (k₂ _ (by decide)).trans g₁
    have h₂ : Room u₂ := h.congr g₂ (wr₂.trans wr₁)
    have f₁₂ : Frame [stR s] s.mem u₂.mem := f₁.trans (by rw [← stR_congr g₁]; exact f₂)
    refine step _ (by decide) _ h₂ (by simp only [schedA, g₂]) (hK g₂ f₁₂) g₂
      fun u₃ w₃ k₃ rd₃ wr₃ sp₃ f₃ => ⟨fun x hx => ?_, fun r hr => by rw [k₃ r hr, k₂ r hr, k₁ r hr],
        rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
        f₁₂.trans (by rw [← stR_congr g₂]; exact f₃)⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.RISCV64.Bitsliced
