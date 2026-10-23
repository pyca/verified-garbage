module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Rounds

/-! # RC2 on PPC64LE: composition of the sixteen rounds -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- `c` maps the words to `g` of them, on memory `m` with the schedule at `T`. -/
def RunsTo (T : Addr) (m : Mem) (c : Prog isa) (g : Spec.Rc2.State → Spec.Rc2.State) : Prop :=
  ∀ u, KeyEnv T u → u.mem = m → ∀ v, Holds v u →
    WP isa c u fun t => Holds (g v) t ∧ t.mem = m ∧ Keep roundRegs u t

theorem roundRegs_append : ∀ r ∈ roundRegs ++ roundRegs, r ∈ roundRegs := fun r h => by
  rcases List.mem_append.1 h with h | h <;> exact h

theorem RunsTo.of_eq {T : Addr} {m : Mem} {c : Prog isa} {g g' : Spec.Rc2.State → Spec.Rc2.State}
    (h : RunsTo T m c g) (e : ∀ v, g v = g' v) : RunsTo T m c g' := fun u E hm v H =>
  WP.mono (h u E hm v H) fun _ ⟨a, b, c⟩ => ⟨e v ▸ a, b, c⟩

theorem RunsTo.nil {T : Addr} {m : Mem} : RunsTo T m (.block []) id := fun _ _ hm _ H =>
  WP.block_nil ⟨H, hm, Keep.refl _ _⟩

theorem RunsTo.seq {T : Addr} {m : Mem} {c₁ c₂ : Prog isa} {g₁ g₂ : Spec.Rc2.State → Spec.Rc2.State}
    (h₁ : RunsTo T m c₁ g₁) (h₂ : RunsTo T m c₂ g₂) : RunsTo T m (.seq c₁ c₂) (fun v => g₂ (g₁ v)) :=
  fun u E hm v H => WP.seq <| WP.mono (h₁ u E hm v H) fun t ⟨a, b, k⟩ =>
    WP.mono (h₂ t (E.keep k (by decide)) b _ a) fun t' ⟨a', b', k'⟩ =>
      ⟨a', b', (k.trans k').mono roundRegs_append⟩

theorem RunsTo.append {T : Addr} {m : Mem} {l₁ l₂ : List Instr} {g₁ g₂ : Spec.Rc2.State → Spec.Rc2.State}
    (h₁ : RunsTo T m (.block l₁) g₁) (h₂ : RunsTo T m (.block l₂) g₂) :
    RunsTo T m (.block (l₁ ++ l₂)) (fun v => g₂ (g₁ v)) := fun u E hm v H => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ u E hm v H) fun t ⟨a, b, k⟩ =>
    WP.mono (h₂ t (E.keep k (by decide)) b _ a) fun t' ⟨a', b', k'⟩ =>
      ⟨a', b', (k.trans k').mono roundRegs_append⟩

theorem RunsTo.foldr {T : Addr} {m : Mem} (f : Nat → Prog isa) (g : Nat → Spec.Rc2.State → Spec.Rc2.State)
    (l : List Nat) (h : ∀ i ∈ l, RunsTo T m (f i) (g i)) :
    RunsTo T m (l.foldr (fun i rest => .seq (f i) rest) (.block [])) (fun v => l.foldl (fun v i => g i v) v) := by
  induction l with
  | nil => exact RunsTo.nil
  | cons i l ih =>
    exact (RunsTo.seq (h i (by simp)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))).of_eq fun _ => rfl

theorem RunsTo.flatMap {T : Addr} {m : Mem} (f : Nat → List Instr) (g : Nat → Spec.Rc2.State → Spec.Rc2.State)
    (l : List Nat) (h : ∀ i ∈ l, RunsTo T m (.block (f i)) (g i)) :
    RunsTo T m (.block (l.flatMap f)) (fun v => l.foldl (fun v i => g i v) v) := by
  induction l with
  | nil => exact RunsTo.nil
  | cons i l ih =>
    rw [List.flatMap_cons]
    exact (RunsTo.append (h i (by simp)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))).of_eq fun _ => rfl

theorem mix_regs : ∀ i < 4, ∀ r ∈ [Reg.r0, .r10, .r11, .r12, wordReg i], r ∈ roundRegs := by decide
theorem mash_regs : ∀ i < 4, ∀ r ∈ [Reg.r0, .r5, .r10, .r11, .r12, wordReg i], r ∈ roundRegs := by decide

theorem mix_runsTo {T : Addr} {m : Mem} {j i : Nat} (hj : j < 64) (hi : i < 4) :
    RunsTo T m (.block (mix j i)) (Spec.Rc2.mix (Spec.Rc2.scheduleAt m T) j i) := fun u E hm _ H =>
  WP.mono (mix_run u E H hj hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mix_regs i hi)⟩

theorem reverseMix_runsTo {T : Addr} {m : Mem} {j i : Nat} (hj : j < 64) (hi : i < 4) :
    RunsTo T m (.block (reverseMix j i)) (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) j i) := fun u E hm _ H =>
  WP.mono (reverseMix_run u E H hj hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mix_regs i hi)⟩

theorem mash_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {i : Nat} (hi : i < 4) :
    RunsTo T m (mash d i) (mashSpec d (Spec.Rc2.scheduleAt m T) i) := fun u E hm _ H =>
  WP.mono (mash_run u E H d hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mash_regs i hi)⟩

def mixRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat) (v : Spec.Rc2.State) :
    Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mixRound k j v
  | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat) (v : Spec.Rc2.State) :
    Spec.Rc2.State :=
  if j = 4 ∨ j = 10 then mashRoundSpec d k (mixRoundSpec d k j v) else mixRoundSpec d k j v

theorem mixRound_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {j : Nat} (hj : j < 16) :
    RunsTo T m (.block (mixRound d j)) (mixRoundSpec d (Spec.Rc2.scheduleAt m T) j) := by
  cases d with
  | encrypt =>
    refine (RunsTo.flatMap (fun i => mix (4 * j + i) i)
      (fun i => Spec.Rc2.mix (Spec.Rc2.scheduleAt m T) (4 * j + i) i) (List.range 4) fun i hi => ?_).of_eq fun _ => rfl
    have := List.mem_range.1 hi
    exact mix_runsTo (by omega) this
  | decrypt =>
    refine (RunsTo.flatMap (fun i => reverseMix (4 * (15 - j) + i) i)
      (fun i => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) (4 * (15 - j) + i) i) [3, 2, 1, 0]
      fun i hi => ?_).of_eq fun _ => rfl
    have : i < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    exact reverseMix_runsTo (by omega) this

theorem order_lt (d : Spec.Rc2.Direction) : ∀ i ∈ order d, i < 4 := by cases d <;> decide

theorem mashRound_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) :
    RunsTo T m (mashRound d) (mashRoundSpec d (Spec.Rc2.scheduleAt m T)) :=
  (RunsTo.foldr _ _ _ fun i hi => mash_runsTo d (order_lt d i hi)).of_eq fun _ => by cases d <;> rfl

theorem round_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {j : Nat} (hj : j < 16) :
    RunsTo T m (round d j) (roundSpec d (Spec.Rc2.scheduleAt m T) j) := by
  unfold round
  by_cases h : j = 4 ∨ j = 10
  · rw [ite_eq_left h]
    exact (RunsTo.seq (mixRound_runsTo d hj) (mashRound_runsTo d)).of_eq fun v => by
      simp only [roundSpec, ite_eq_left h]
  · rw [ite_eq_right h]
    exact (RunsTo.seq (mixRound_runsTo d hj) RunsTo.nil).of_eq fun v => by
      simp only [roundSpec, ite_eq_right h, id]

theorem rounds_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) :
    RunsTo T m (rounds d) (fun v => (List.range 16).foldl (fun v j => roundSpec d (Spec.Rc2.scheduleAt m T) j v) v) :=
  RunsTo.foldr _ _ _ fun _ hj => round_runsTo d (List.mem_range.1 hj)

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

end VG.Proof.Rc2.PPC64LE
