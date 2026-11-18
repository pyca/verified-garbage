module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Rounds
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Rounds
public import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.Memory

/-! ### `Rc2.PPC64LE.BlockIO`, which only this module used -/

section

/-! # RC2 on PPC64LE: loading and storing the block -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem lane (x : BitVec 64) {i : Nat} (hi : i < 4) :
    (x <<< (48 - 16 * i)) >>> 48 = ((x >>> (16 * i)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp only [h, hj, decide_true, Bool.true_and, show 48 + j < 64 by omega_using [h], show ¬48 + j < 48 - 16 * i by omega_using [],
      decide_false, Bool.not_false]
    rw [show 48 + j - (48 - 16 * i) = 16 * i + j by omega_using [hi]]
  · simp only [h, show ¬48 + j < 64 by omega_using [h], decide_false, Bool.false_and, Bool.and_false]

theorem lane3 (x : BitVec 64) : x >>> 48 = ((x >>> (16 * 3)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp [h, hj]
  · simp only [h, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge x (48 + j) (by omega_using [h])]
    simp

theorem blockLoad_run (u : State) (hr : InRegions (u.rd ++ u.wr) (u.gpr .r4) 8) :
    WP isa (.block blockLoad) u fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .r4))) t ∧ t.mem = u.mem ∧
        Keep [.r6, .r7, .r8, .r9, .r11] u t := by
  refine WP.mono (WP.keep [.r6, .r7, .r8, .r9, .r11] (c := .block blockLoad) (Q := fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .r4))) t ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold blockLoad
  rrun [hr]
  intro i hi
  rw [decode_read64 _ _ _ hi]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact lane _ (i := 0) (by decide)
  · exact lane _ (i := 1) (by decide)
  · exact lane _ (i := 2) (by decide)
  · exact lane3 _

theorem pack_or (v : Spec.Rc2.State) :
    (v.getD 1 0).setWidth 64 <<< 16 ||| (v.getD 0 0).setWidth 64 ||| (v.getD 2 0).setWidth 64 <<< 32 |||
      (v.getD 3 0).setWidth 64 <<< 48 = pack v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h₁ : j < 16
  · simp (disch := omega_arith) [h₁, hj, show j < 32 by omega_using [h₁], show j < 48 by omega_using [h₁]]
  · by_cases h₂ : j < 32
    · simp (disch := omega) [h₁, h₂, hj, show j < 48 by omega_using [h₂], show j - 16 < 64 by omega_using [hj], show j - 16 < 16 by omega_using [h₂],
        BitVec.getLsbD_of_ge]
    · by_cases h₃ : j < 48
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 32 < 64 by omega_using [hj], show ¬j - 16 < 16 by omega_using [h₂],
          show j - 16 - 16 = j - 32 by omega_using [], show j - 32 < 16 by omega_using [h₃], BitVec.getLsbD_of_ge]
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 48 < 64 by omega_using [hj], show ¬j - 16 < 16 by omega_using [h₂],
          show j - 16 - 16 = j - 32 by omega_using [], show ¬j - 32 < 16 by omega_using [h₃], show j - 32 - 16 = j - 48 by omega_using [],
          BitVec.getLsbD_of_ge]

theorem blockStore_run (u : State) {v : Spec.Rc2.State} (H : Holds v u) (hw : InRegions u.wr (u.gpr .r4) 8) :
    WP isa (.block blockStore) u fun t =>
      t.mem = u.mem.writeW (u.gpr .r4) (pack v) ∧ Keep [.r11, .r12] u t := by
  refine WP.mono (WP.keep [.r11, .r12] (c := .block blockStore) (Q := fun t =>
      t.mem = u.mem.writeW (u.gpr .r4) (pack v)) ?_
    (by rfl) rfl) fun t ⟨a, c⟩ => ⟨a, c⟩
  have h0 := H 0 (by decide)
  have h1 := H 1 (by decide)
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  rw [wordReg_0] at h0
  rw [wordReg_1] at h1
  rw [wordReg_2] at h2
  rw [wordReg_3] at h3
  unfold blockStore
  rrun [hw, h0, h1, h2, h3]
  exact congrArg _ (pack_or v)

end VG.Proof.Rc2.PPC64LE

end

end

/-! ### `Rc2.PPC64LE.Cipher`, which this module and modules that import it used -/

section

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
    exact mix_runsTo (by omega_using [hj, this]) this
  | decrypt =>
    refine (RunsTo.flatMap (fun i => reverseMix (4 * (15 - j) + i) i)
      (fun i => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) (4 * (15 - j) + i) i) [3, 2, 1, 0]
      fun i hi => ?_).of_eq fun _ => rfl
    have : i < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
    exact reverseMix_runsTo (by omega_using [this]) this

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

end

end

/-! # Verified RC2 block encryption and decryption on PPC64LE -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The block contract as the code sees it. -/
def blockC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .r3, 128⟩] ∧ s.wr = [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 256⟩]
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .r4) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .r3)) (Spec.Rc2.blockAt s.mem (s.gpr .r4))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem block_wp (d : Spec.Rc2.Direction) (s : State) (hs : (blockC d).pre s) :
    WP isa (blockCode d) s fun s' => (blockC d).post s s' := by
  obtain ⟨hrd, hwr⟩ := hs
  unfold blockCode
  apply WP.seq
  refine WP.mono (blockLoad_run s (by rw [hwr]; exact ⟨_, by simp, Region.contains_self _ _⟩))
    fun t₁ ⟨H₁, m₁, k₁⟩ => ?_
  apply WP.seq
  have E : KeyEnv (s.gpr .r3) t₁ := ⟨k₁.gpr (by decide), fun o n hn => by
    rw [k₁.2.1, k₁.2.2, hrd]; exact ⟨_, by simp, Offset.contains_base _ hn (by omega_using [hn])⟩⟩
  refine WP.mono (rounds_runsTo d t₁ E rfl _ H₁) fun t₂ ⟨H₂, m₂, k₂⟩ => ?_
  have p4 : t₂.gpr .r4 = s.gpr .r4 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (blockStore_run t₂ H₂ (by rw [p4, k₂.2.2, k₁.2.2, hwr]; exact ⟨_, by simp, Region.contains_self _ _⟩))
    fun t₃ ⟨m₃, _⟩ => ?_
  change Spec.Rc2.blockAt t₃.mem (s.gpr .r4) = _
  rw [m₃, p4, m₂, Proof.Rc2.blockAt_write64, cipher_rounds, m₁]

/-- The registers the block functions write. -/
def blockRegs : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem block_ok (d : Spec.Rc2.Direction) (hw : writesOnly blockRegs (blockCode d) = true)
    (hn : (blockCode d).noCalls = true) (hl : (instrs (blockCode d)).all (fun i => !i.writesLr) = true)
    (s : State) (hs : (blockC d).pre s) :
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep blockRegs (block_wp d s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) hn hl, hp⟩

end VG.Proof.Rc2.PPC64LE
