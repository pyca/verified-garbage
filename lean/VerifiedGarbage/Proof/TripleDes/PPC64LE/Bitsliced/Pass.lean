module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Step
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Bitsliced DES rounds and passes on PPC64LE

`round_ok`: the code of a round loads the round key at the key pointer `r3`
into `r9`, complements it, steps the pointer by `δ d` (8 or −8) and does to
the state words what `roundW` does with the key's low 48 bits. `pass_ok`: a
pass points `r3` at its first key in the schedule (`r7`), runs eight pairs
of rounds (counted down in `r5`) and exchanges the halves: what `passW`
does with the component schedule. `passes_ok`: the three passes do what
`tdeaW` does. As on RISC-V (`Proof/TripleDes/RISCV64/Bitsliced/Pass.lean`),
but for the schedule, which the code reads where the caller keeps it.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Bitslice VG.Impl.TripleDes.PPC64LE.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.PPC64LE.Straight (wordAddr)

/-- The schedule at `r7`: readable, and apart from the scratch buffer. -/
structure Sched (s : State) : Prop where
  rd : (⟨s.gpr .r7, 384⟩ : Region) ∈ s.rd
  sep : (⟨s.gpr .r7, 384⟩ : Region).Disjoint (frameR s)

theorem Sched.congr {s s' : State} (h : Sched s) (h7 : s'.gpr .r7 = s.gpr .r7)
    (h10 : s'.gpr .r10 = s.gpr .r10) (hrd : s'.rd = s.rd) : Sched s' where
  rd := by rw [h7, hrd]; exact h.rd
  sep := by simp only [frameR, h7, h10]; exact h.sep

/-- The ones register holds all ones. -/
def Ones (s : State) : Prop := s.gpr .r11 = BitVec.allOnes 64

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 64 := BitVec.ofInt 64 (if d = .encrypt then 8 else -8)

/-- A round key's address: word `i < 48` of the schedule. -/
def KeyAt (s : State) (A : Addr) : Prop := ∃ i < 48, A = s.gpr .r7 + BitVec.ofNat 64 (8 * i)

theorem KeyAt.congr {s s' : State} {A : Addr} (h : KeyAt s A) (hb : s'.gpr .r7 = s.gpr .r7) :
    KeyAt s' A := by
  simp only [KeyAt, hb]; exact h

theorem keyAt_rd {s : State} (h : Sched s) {A : Addr} (hk : KeyAt s A) :
    InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 0) 8 := by
  obtain ⟨i, hi, rfl⟩ := hk
  rw [BitVec.add_zero]
  exact ⟨_, List.mem_append_left _ h.rd, Offset.contains_base _ (by omega) (by omega)⟩

/-- Round keys are apart from the state words. -/
theorem keyAt_apart {s : State} (h : Sched s) {A : Addr} (hk : KeyAt s A) :
    (⟨A, 8⟩ : Region).Disjoint (stR s) := by
  obtain ⟨i, hi, rfl⟩ := hk
  exact (h.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))

theorem stR_congr {s s' : State} (hb : s'.gpr .r10 = s.gpr .r10) : stR s' = stR s := by
  simp only [stR, hb]

/-! ## A round -/

theorem δ_encrypt : δ .encrypt = BitVec.ofNat 64 8 := by decide

theorem δ_decrypt : δ .decrypt = -BitVec.ofNat 64 8 := by decide

theorem keyStep (d : Direction) (s : State) :
    runBlock isa [if d = .encrypt then Instr.addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8] s =
      some (s.write .r3 (s.gpr .r3 + δ d)) := by
  cases d
  · rw [ite_eq_left (rfl : Direction.encrypt = .encrypt), runBlock_cons, show keyPtr = .r3 from rfl,
      exec_addi (by decide) (by decide), runStep_some, runBlock_nil, δ_encrypt]
  · rw [ite_eq_right (by decide : ¬ Direction.decrypt = .encrypt), runBlock_cons, show keyPtr = .r3 from rfl,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil, δ_decrypt, BitVec.sub_eq_add_neg]

theorem keyLoad_ok (d : Direction) {s : State} (h : Sched s) {A : Addr} (hA : s.gpr .r3 = A)
    (hk : KeyAt s A) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧ s'.gpr .r9 = s.mem.readW A 64 ^^^ s.gpr .r11 ∧
      s'.gpr .r3 = A + δ d ∧ (∀ r, r ≠ .r9 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  have e₁ := exec_load_d (s := s) (t := .r9) (n := .r3) (off := 0) (by decide) (by decide)
    (by rw [hA]; exact keyAt_rd h hk)
  let s₁ := s.write .r9 (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 0) 64)
  let s₂ := s₁.write .r9 (s₁.gpr .r9 ^^^ s₁.gpr .r11)
  have e₂ : exec (.logic .xor .r9 .r9 .r11) s₁ = some s₂ := exec_logic
  refine ⟨s₂.write .r3 (s₂.gpr .r3 + δ d), ?_, ?_, ?_, fun r h9 h3 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [keyLoad, show key = .r9 from rfl, show ones = .r11 from rfl, show [Instr.load .d .r9 keyPtr 0,
      .logic .xor .r9 .r9 .r11, if d = .encrypt then .addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8] =
      [Instr.load .d .r9 .r3 0, .logic .xor .r9 .r9 .r11] ++
        [if d = .encrypt then .addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8] from rfl]
    refine runBlock_cat_some ?_ (keyStep d s₂)
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil]
  · simp [s₂, s₁, gpr_write, hA]
  · simp [s₂, s₁, gpr_write, hA]
  · simp [s₂, s₁, gpr_write, h9, h3]

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : ∀ b < 48, (~~~(s.gpr .r9)).getLsbD b = k.getLsbD b) (hones : Ones s) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, rd₁, wr₁, sp₁, lr₁, f₁⟩ := ih (by omega)
    have g0 : s₁.gpr .r10 = s.gpr .r10 := k₁ _ (by decide)
    have g9 : s₁.gpr .r9 = s.gpr .r9 := k₁ _ (by decide)
    have g11 : s₁.gpr .r11 = s.gpr .r11 := k₁ _ (by decide)
    obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, lr₂, f₂⟩ :=
      sboxStep_ok ρ (j := n) (by omega) (h.congr g0 wr₁) k (by rw [g9]; exact hkey)
        (by rw [g11]; exact hones)
    refine ⟨s₂, ?_, fun x hx => ?_, fun r hr => by rw [k₂ r hr, k₁ r hr], rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, lr₂.trans lr₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega) w₁ (w₁ x hx)
    · rw [stR_congr g0] at f₂; exact f₁.trans f₂

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

/-- The registers a round leaves alone. -/
def roundKept : List Reg := [.r10, .r4, .r8, .r5, .r7, .r11]

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) (hs : Sched s) (hones : Ones s)
    {A : Addr} (hA : s.gpr .r3 = A) (hk : KeyAt s A) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW A 64).setWidth 48) (words s) x) ∧
      s'.gpr .r3 = A + δ d ∧ (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, p₁, o₁, m₁, rd₁, wr₁, sp₁, lr₁⟩ := keyLoad_ok d hs hA hk
  have g0 : s₁.gpr .r10 = s.gpr .r10 := o₁ _ (by decide) (by decide)
  have g11 : s₁.gpr .r11 = s.gpr .r11 := o₁ _ (by decide) (by decide)
  obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, lr₂, f₂⟩ :=
    stepsCode_ok ρ ((s.mem.readW A 64).setWidth 48) (Nat.le_refl 8) (h.congr g0 wr₁)
      (fun b hb => by
        rw [k₁, show s.gpr .r11 = BitVec.allOnes 64 from hones, BitVec.xor_allOnes, BitVec.not_not,
          BitVec.getLsbD_setWidth]
        simp [hb])
      (by rw [Ones, g11]; exact hones)
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r hr => ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁,
    lr₂.trans lr₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8)
      (fun y _ => by simp only [words, sl, m₁, g0]) x hx
  · rw [k₂ _ (by decide), p₁]
  · have hs : r ∈ stepKept ∧ r ≠ .r9 ∧ r ≠ .r3 := by
      simp only [roundKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k₂ r hs.1, o₁ r hs.2.1 hs.2.2]
  · rw [stR_congr g0, m₁] at f₂; exact f₂

/-! ## Pairs of rounds -/

theorem roundPair_eq (d : Direction) :
    roundPair d = round d .ba ++ (round d .ab ++ ([.subi pairs pairs 1] : List Instr)) := by
  simp only [roundPair, List.append_assoc]

theorem Frame.readKey {s : State} (h : Sched s) {A : Addr} (hk : KeyAt s A) {m : Mem}
    (hf : Frame [stR s] s.mem m) : m.readW A 64 = s.mem.readW A 64 :=
  hf.readW (Region.contains_self A 8) (by simpa using keyAt_apart h hk) (by decide)

/-- The registers a pair of rounds leaves alone. -/
def pairKept : List Reg := [.r10, .r4, .r8, .r7, .r11]

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) (hs : Sched s) (hones : Ones s)
    {A : Addr} (hA : s.gpr .r3 = A) (hk₁ : KeyAt s A) (hk₂ : KeyAt s (A + δ d)) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (A + δ d) 64).setWidth 48)
        (roundW .ba ((s.mem.readW A 64).setWidth 48) (words s)) x) ∧
      s'.gpr .r3 = A + δ d + δ d ∧ s'.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 1 ∧
      (∀ r ∈ pairKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, p₁, k₁, rd₁, wr₁, sp₁, lr₁, f₁⟩ := round_ok d .ba h hs hones hA hk₁
  have g0 : s₁.gpr .r10 = s.gpr .r10 := k₁ _ (by decide)
  have g7 : s₁.gpr .r7 = s.gpr .r7 := k₁ _ (by decide)
  have g11 : s₁.gpr .r11 = s.gpr .r11 := k₁ _ (by decide)
  have h₁ := h.congr g0 wr₁
  obtain ⟨s₂, run₂, w₂, p₂, k₂, rd₂, wr₂, sp₂, lr₂, f₂⟩ :=
    round_ok d .ab h₁ (hs.congr g7 g0 rd₁) (by rw [Ones, g11]; exact hones) p₁ (hk₂.congr g7)
  have e₃ := exec_subi (s := s₂) (d := .r5) (n := .r5) (imm := 1) (by decide) (by decide)
  have g5 : s₂.gpr .r5 = s.gpr .r5 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  refine ⟨s₂.write .r5 (s₂.gpr .r5 - BitVec.ofNat 64 1), ?_, fun x hx => ?_, ?_, ?_, fun r hr => ?_,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, lr₂.trans lr₁, ?_⟩
  · rw [roundPair_eq]
    refine runBlock_cat_some run₁ (runBlock_cat_some run₂ ?_)
    rw [runBlock_cons, show Impl.TripleDes.PPC64LE.Bitslice.pairs = Reg.r5 from rfl, e₃, runStep_some,
      runBlock_nil]
  · have : words (s₂.write .r5 (s₂.gpr .r5 - BitVec.ofNat 64 1)) x = words s₂ x := by
      simp only [words, sl, mem_write, gpr_write, reduceCtorEq, ite_false]
    rw [this, w₂ x hx]
    rw [Frame.readKey hs hk₂ f₁]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · simp only [gpr_write, reduceCtorEq, ite_false, p₂]
  · simp only [gpr_write, ite_true, g5]
  · simp only [pairKept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_write, reduceCtorEq, ite_false] <;>
      rw [k₂ _ (by decide), k₁ _ (by decide)]
  · simp only [mem_write]
    rw [stR_congr g0] at f₂; exact f₁.trans f₂

/-! ## A pass -/

/-- The offset in the schedule of a pass's first key. -/
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
def passP (s : State) (c : Nat) (d : Direction) : Addr := s.gpr .r7 + BitVec.ofNat 64 (kOff c d)

theorem passKeyAt {s : State} {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    KeyAt s (passP s c d + BitVec.ofNat 64 r * δ d) := by
  refine ⟨16 * c + ix d r, by unfold ix; split <;> omega, ?_⟩
  rw [passP, BitVec.add_assoc, kaddr c hc d r hr]

theorem keyOf_pass (m : Mem) (s : State) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    keyOf m (passP s c d) (δ d) r = roundKey (componentSchedule (scheduleAt m (s.gpr .r7)) c) d r := by
  have hi : ix d r < 16 := by unfold ix; split <;> omega
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl, componentSchedule_readW m _ _ _ hc hi,
    keyOf, passP, BitVec.add_assoc, kaddr c hc d r hr]

/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (c : Nat) (d : Direction) (m : Nat) (s : State) : Prop where
  le : m ≤ 8
  kept : ∀ r ∈ pairKept, s.gpr r = s₀.gpr r
  ptr : s.gpr .r3 = passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d
  cnt : s.gpr .r5 = BitVec.ofNat 64 (8 - m)
  wds : ∀ x < 64, words s x =
    VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP s₀ c d) (δ d)) m (words s₀) x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [stR s₀] s₀.mem s.mem

theorem eval_nonzero_ofNat (s : State) (r : Reg) {a : Nat} (ha : a < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 a) : isa.eval (.nonzero .d r) s = some (decide (a ≠ 0)) := by
  change VG.PPC64LE.eval (.nonzero .d r) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, h]
  congr 1
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
  constructor
  · intro hx h0; subst h0; exact hx rfl
  · intro hx h0
    apply hx
    have := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this

theorem pair_step {s₀ : State} (h₀ : Room s₀) (hs₀ : Sched s₀) (ho₀ : Ones s₀) {c : Nat} (hc : c < 3)
    {d : Direction} {m : Nat} (hm : m < 8) {s : State} (I : PairInv s₀ c d m s) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧ PairInv s₀ c d (m + 1) s' := by
  have g10 := I.kept .r10 (by decide)
  have g7 := I.kept .r7 (by decide)
  have h : Room s := h₀.congr g10 I.wr
  have hs : Sched s := hs₀.congr g7 g10 I.rd
  have ho : Ones s := by rw [Ones, I.kept .r11 (by decide)]; exact ho₀
  have hk₁ := (passKeyAt (s := s₀) hc d (r := 2 * m) (by omega)).congr g7
  have hk₂ := (passKeyAt (s := s₀) hc d (r := 2 * m + 1) (by omega)).congr g7
  rw [← kptr_succ] at hk₂
  obtain ⟨s', run, w, p3, p5, k, rd, wr, sp, lr, f⟩ := roundPair_ok d h hs ho I.ptr hk₁ hk₂
  have rk : ∀ r < 16, s.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 =
      s₀.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 := fun r hr =>
    Frame.readKey hs₀ (passKeyAt (s := s₀) hc d hr) I.frame
  refine ⟨s', run, ⟨by omega, fun r hr => (k r hr).trans (I.kept r hr), ?_, ?_, fun x hx => ?_,
    rd.trans I.rd, wr.trans I.wr, sp.trans I.sp, lr.trans I.lr, ?_⟩⟩
  · rw [p3, kptr_succ, kptr_succ]; congr 3
  · rw [p5, I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 64 (8 - m) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (8 - (m + 1))) m hm
  · have e : passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d + δ d =
        passP s₀ c d + BitVec.ofNat 64 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega), rk _ (by omega)]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · exact I.frame.trans (by rw [← stR_congr g10]; exact f)

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) (hs₀ : Sched s₀) (ho₀ : Ones s₀) {c : Nat} (hc : c < 3)
    (d : Direction) {s : State} (I : PairInv s₀ c d 0 s) :
    WP isa (.loop (.block (roundPair d)) (.nonzero .d pairs)) s (PairInv s₀ c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  obtain ⟨v', run, J'⟩ := pair_step h₀ hs₀ ho₀ hc hm J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show Impl.TripleDes.PPC64LE.Bitslice.pairs = Reg.r5 from rfl,
    eval_nonzero_ofNat _ _ (by omega) J'.cnt]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right; exact ⟨by simp; omega, 8 - (m + 1), by omega, m + 1, by omega, rfl, J'⟩

/-- The registers a pass leaves alone. -/
def passKept : List Reg := [.r10, .r4, .r8, .r7, .r11]

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) (hs : Sched s)
    (ho : Ones s) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x =
        passW (componentSchedule (scheduleAt s.mem (s.gpr .r7)) c) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  unfold pass
  apply WP.seq
  have e₁ := exec_addi (s := s) (d := .r3) (n := .r7)
    (imm := 128 * c + if d = .encrypt then 0 else 120) (by decide)
    (by cases d <;> (simp only [reduceCtorEq, ite_true, ite_false]; omega))
  let s₁ := s.write .r3 (s.gpr .r7 + BitVec.ofNat 64 (128 * c + if d = .encrypt then 0 else 120))
  have e₂ := exec_li (s := s₁) (d := .r5) (imm := 8) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, show keyPtr = .r3 from rfl, show sched = .r7 from rfl, e₁, runStep_some,
      runBlock_cons, show Impl.TripleDes.PPC64LE.Bitslice.pairs = Reg.r5 from rfl, e₂, runStep_some,
      runBlock_nil], ?_⟩
  have z : BitVec.ofNat 64 (2 * 0) * δ d = 0#64 := by cases d <;> decide
  have I0 : PairInv s c d 0 (s₁.write .r5 (BitVec.ofNat 64 8)) := by
    refine ⟨by decide, fun r hr => ?_, ?_, by simp [gpr_write], fun x hx => rfl, rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
    · simp only [pairKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [s₁, gpr_write]
    · simp only [s₁, gpr_write, reduceCtorEq, ite_false, ite_true, passP, z, kOff, BitVec.add_zero]
  apply WP.seq
  refine WP.mono (pairLoop_ok h hs ho hc d I0) fun v J => ?_
  have hv : Room v := h.congr (J.kept .r10 (by decide)) J.wr
  obtain ⟨v', run, w, k, rd, wr, sp, lr, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, fun r hr => ?_, rd.trans J.rd, wr.trans J.wr,
    sp.trans J.sp, lr.trans J.lr, ?_⟩
  · rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
    refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
    rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8 (fun r hr => keyOf_pass _ _ hc d hr)]
  · have hne : r ≠ .r12 ∧ r ≠ .r14 := by
      simp only [passKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k _ hne.1 hne.2, J.kept r hr]
  · rw [stR_congr (J.kept .r10 (by decide))] at f; exact J.frame.trans f

/-! ## The three passes -/

theorem passes_ok (d : Direction) {s : State} (h : Room s) (hs : Sched s) (ho : Ones s) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (s.gpr .r7)) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  have hK : ∀ {u : State}, Frame [stR s] s.mem u.mem →
      scheduleAt u.mem (s.gpr .r7) = scheduleAt s.mem (s.gpr .r7) := fun hf =>
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (Region.sub_prefix (by omega))
  have step : ∀ (c : Nat) (hc : c < 3) (d' : Direction) {u : State}, Room u → Sched u → Ones u →
      u.gpr .r7 = s.gpr .r7 → Frame [stR s] s.mem u.mem →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (s.gpr .r7)) c) d' (words u) x) → (∀ r ∈ passKept, u'.gpr r = u.gpr r) →
        u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → u'.lr = u.lr → Frame [stR u] u.mem u'.mem → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u hu hsu hou h7 hf Q hQ
    refine WP.mono (pass_ok c hc d' hu hsu hou) fun u' ⟨w, k, rd, wr, sp, lr, f⟩ =>
      hQ u' ?_ k rd wr sp lr f
    rw [h7, hK hf] at w; exact w
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ h hs ho rfl (Frame.refl _ _) fun u₁ w₁ k₁ rd₁ wr₁ sp₁ lr₁ f₁ => ?_
    have g₁ : u₁.gpr .r10 = s.gpr .r10 := k₁ _ (by decide)
    have g₁7 : u₁.gpr .r7 = s.gpr .r7 := k₁ _ (by decide)
    have h₁ : Room u₁ := h.congr g₁ wr₁
    have hs₁ : Sched u₁ := hs.congr g₁7 g₁ rd₁
    have ho₁ : Ones u₁ := by rw [Ones, k₁ _ (by decide)]; exact ho
    apply WP.seq
    refine step _ (by decide) _ h₁ hs₁ ho₁ g₁7 f₁ fun u₂ w₂ k₂ rd₂ wr₂ sp₂ lr₂ f₂ => ?_
    have g₂ : u₂.gpr .r10 = s.gpr .r10 := (k₂ _ (by decide)).trans g₁
    have g₂7 : u₂.gpr .r7 = s.gpr .r7 := (k₂ _ (by decide)).trans g₁7
    have h₂ : Room u₂ := h.congr g₂ (wr₂.trans wr₁)
    have hs₂ : Sched u₂ := hs.congr g₂7 g₂ (rd₂.trans rd₁)
    have ho₂ : Ones u₂ := by rw [Ones, k₂ _ (by decide), k₁ _ (by decide)]; exact ho
    have f₁₂ : Frame [stR s] s.mem u₂.mem := f₁.trans (by rw [← stR_congr g₁]; exact f₂)
    refine step _ (by decide) _ h₂ hs₂ ho₂ g₂7 f₁₂
      fun u₃ w₃ k₃ rd₃ wr₃ sp₃ lr₃ f₃ => ⟨fun x hx => ?_, fun r hr => by rw [k₃ r hr, k₂ r hr, k₁ r hr],
        rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
        lr₃.trans (lr₂.trans lr₁), f₁₂.trans (by rw [← stR_congr g₂]; exact f₃)⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.PPC64LE.Bitsliced
