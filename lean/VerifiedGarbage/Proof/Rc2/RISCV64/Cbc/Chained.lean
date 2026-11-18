module

public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Run
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Io
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Proof.Rc2.RISCV64.Rounds
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Rounds
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Rc2.CbcList
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Io

/-! ### `Rc2.RISCV64.Cbc.Verified`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Cbc.Body`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Cbc.Call`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Block`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.BlockIO`, which only this module used -/

section

/-! # RC2 on RISC-V: loading and storing the block

The block is read and written a byte at a time, as a little-endian
doubleword (`Bytes.loadLE64_ok`, `Bytes.storeLE64_ok`), and split into the
words, or joined from them, as on PPC64LE (`Proof/Rc2/PPC64LE/Block.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

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

theorem blockLoad_run (u : State) (hr0 : InRegions (u.rd ++ u.wr) (u.gpr .a1) 4)
    (hr4 : InRegions (u.rd ++ u.wr) (u.gpr .a1 + BitVec.ofNat 64 4) 4) :
    WP isa (.block blockLoad) u fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .a1))) t ∧ t.mem = u.mem ∧
        Keep [.a3, .a4, .a5, .a6, .t1, .t2, .a7] u t := by
  refine WP.mono (WP.keep [.a3, .a4, .a5, .a6, .t1, .t2, .a7] (c := .block blockLoad) (Q := fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .a1))) t ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold blockLoad
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := .t1) (tmp := .a7) (hi := .t2) (n := .a1) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hr0) hr4) fun s₁ ⟨h1, _, hm, _, _, _⟩ => ?_
  rw [BitVec.add_zero] at h1
  rrun [h1, hm]
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

theorem blockStore_run (u : State) {v : Spec.Rc2.State} (H : Holds v u)
    (hw0 : InRegions u.wr (u.gpr .a1) 4) (hw4 : InRegions u.wr (u.gpr .a1 + BitVec.ofNat 64 4) 4) :
    WP isa (.block blockStore) u fun t =>
      t.mem = u.mem.writeW (u.gpr .a1) (pack v) ∧ Keep [.t1, .t2, .a7] u t := by
  refine WP.mono (WP.keep [.t1, .t2, .a7] (c := .block blockStore) (Q := fun t =>
      t.mem = u.mem.writeW (u.gpr .a1) (pack v)) ?_
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
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s₁ : State) => s₁.gpr .t1 = pack v ∧ s₁.gpr .a1 = u.gpr .a1 ∧ s₁.mem = u.mem ∧
      s₁.wr = u.wr) (by rrun [h0, h1, h2, h3]; exact pack_or v) fun s₁ ⟨e1, e2, e3, e4⟩ => ?_
  refine WP.mono (Bytes.storeLE64_ok (v := .t1) (tmp := .a7) (hi := .t2) (n := .a1) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [e2, e4]; simpa using hw0) (by rw [e2, e4]; exact hw4)) fun s₂ ⟨m₂, _⟩ => ?_
  rw [m₂, e1, e2, e3, BitVec.add_zero, Words64.writeW64_split]

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.Cipher`, which this module and modules that import it used -/

section

/-! # RC2 on RISC-V: composition of the sixteen rounds -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg := [.a7, .t3, .a3, .a4, .a5, .a6, .t0, .t1, .t2]

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

theorem mix_regs : ∀ i < 4, ∀ r ∈ [Reg.a7, .t0, .t1, .t2, wordReg i], r ∈ roundRegs := by decide
theorem mash_regs : ∀ i < 4, ∀ r ∈ [Reg.a7, .t3, .t0, .t1, .t2, wordReg i], r ∈ roundRegs := by decide

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

end VG.Proof.Rc2.RISCV64

end

end

/-! # Verified RC2 block encryption and decryption on RISC-V

The rounds read the schedule (`rounds_runsTo`) at `a2`, between the
block's load and store: the schedule itself if it is aligned, else its copy
in the working space (`copyLoop_ok`), as `placeSchedule_run` proves.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The block contract as the code sees it. -/
def blockC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a1, 8⟩
    let scratch : Region := ⟨s.gpr .a2, 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧
      key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .a1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .a0)) (Spec.Rc2.blockAt s.mem (s.gpr .a1))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem scheduleAt_copy {m m' : Mem} {S D : Addr}
    (h : ∀ i < 128, m' (D + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i)) :
    Spec.Rc2.scheduleAt m' D = Spec.Rc2.scheduleAt m S := by
  apply Vector.ext; intro i hi
  simp only [Spec.Rc2.scheduleAt, Vector.getElem_ofFn]
  rw [h _ (by omega_using [hi]), h _ (by omega_using [hi])]

/-- The schedule's copy: its bytes in the working space, the rest of memory
as it was. -/
theorem copySchedule_run (s : State) (hrd : s.rd = [⟨s.gpr .a0, 128⟩])
    (hwr : ∀ i < 128, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .a2) 128 (s.gpr .a0) 128) :
    WP isa copySchedule s fun t =>
      (∀ i < 128, t.mem (s.gpr .a2 + BitVec.ofNat 64 i) = s.mem (s.gpr .a0 + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr .a2, 128⟩] s.mem t.mem ∧ Keep [.t3, .t4, .t5, .a7] s t := by
  unfold copySchedule
  apply WP.seq
  refine WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun u => u.gpr .t3 = s.gpr .a0 ∧ u.gpr .t4 = s.gpr .a2 ∧
      u.gpr .t5 = BitVec.ofNat 64 128 ∧ u.mem = s.mem) (by rrun) (by rfl) rfl) fun u ⟨⟨u3, u4, u5, um⟩, uk⟩ => ?_
  refine WP.mono (copyLoop_ok (tmp := .a7) (src := .t3) (dst := .t4) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) u (N := 128) (by decide) (by decide) u5
    (fun i hi => by
      rw [uk.2.1, uk.2.2, u3, hrd]
      exact ⟨⟨s.gpr .a0, 128⟩, List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by rw [uk.2.2, u4]; exact hwr i hi) (by rw [u3, u4]; exact hsep))
    fun t ⟨tc, tf, tk⟩ => ⟨fun i hi => by rw [← u4, tc i hi, u3, um], by rw [← um, ← u4]; exact tf,
      (uk.trans tk).mono (by decide)⟩

/-- The schedule the rounds read, at `a2`: aligned, readable and holding the
schedule, the schedule itself or its copy; memory is changed only in the
working space's first 128 bytes. -/
theorem placeSchedule_run (s : State) (hrd : s.rd = [⟨s.gpr .a0, 128⟩])
    (hwr : ∀ i < 128, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .a2) 128 (s.gpr .a0) 128) (hal : (s.gpr .a2).toNat % 8 = 0)
    (hin : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 o) n) :
    WP isa placeSchedule s fun t =>
      (t.gpr .a2).toNat % 8 = 0 ∧
      (∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (t.gpr .a2 + BitVec.ofNat 64 o) n) ∧
      Spec.Rc2.scheduleAt t.mem (t.gpr .a2) = Spec.Rc2.scheduleAt s.mem (s.gpr .a0) ∧
      Frame [⟨s.gpr .a2, 128⟩] s.mem t.mem ∧ Keep [.t0, .t3, .t4, .t5, .a7, .a2] s t := by
  unfold placeSchedule
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = s.gpr .a0 &&& 7#64 ∧ u.mem = s.mem) (by rrun)
    (by rfl) rfl) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
  have ga0 : u.gpr .a0 = s.gpr .a0 := uk.gpr (by decide)
  have ga2 : u.gpr .a2 = s.gpr .a2 := uk.gpr (by decide)
  refine WP.ite _ (rfl : isa.eval (.zero .t0) u = some (u.gpr .t0 == 0)) (fun hz => ?_) (fun hnz => ?_)
  · have h0 : s.gpr .a0 &&& 7#64 = 0 := by rw [← u0]; simpa using hz
    have hal0 : (s.gpr .a0).toNat % 8 = 0 := by
      have e := congrArg BitVec.toNat h0
      rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e
      exact e
    refine WP.mono (WP.keep [.a2] (Q := fun t => t.gpr .a2 = s.gpr .a0 ∧ t.mem = s.mem) (by rrun [ga0, um])
      (by rfl) rfl) fun t ⟨⟨t2, tm⟩, tk⟩ => ?_
    refine ⟨by rw [t2]; exact hal0, fun o n hn => ?_, by rw [t2, tm], by rw [tm]; exact Frame.refl _ _,
      (uk.trans tk).mono (by decide)⟩
    rw [t2, hrd]
    exact ⟨⟨s.gpr .a0, 128⟩, List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ hn (by omega_using [hn])⟩
  · refine WP.mono (copySchedule_run u (by rw [uk.2.1, ga0]; exact hrd) (fun i hi => by
        rw [uk.2.2, ga2]; exact hwr i hi) (by rw [ga0, ga2]; exact hsep)) fun t ⟨tc, tf, tk⟩ => ?_
    have t2 : t.gpr .a2 = s.gpr .a2 := by rw [tk.gpr (by decide), ga2]
    refine ⟨by rw [t2]; exact hal, by rw [t2]; exact hin, ?_, by rw [← um, ← ga2]; exact tf,
      (uk.trans tk).mono (by decide)⟩
    rw [t2, ← ga2, ← ga0, ← um]
    exact scheduleAt_copy tc

theorem block_wp (d : Spec.Rc2.Direction) (s : State) (hs : (blockC d).pre s) :
    WP isa (blockCode d) s fun s' => (blockC d).post s s' := by
  obtain ⟨hrd, hwr, hal, hfit1, hfit2, hks, hds⟩ := hs
  have inScratch : ∀ o n, o + n ≤ 256 → InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_using [h])⟩
  have inData : ∀ o n, o + n ≤ 8 → InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_using [h])⟩
  unfold blockCode
  apply WP.seq
  refine WP.mono (placeSchedule_run s hrd (fun i hi => inScratch i 1 (by omega_using [hi]))
    (hks.symm.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
    (Region.contains_self _ _)) hal (fun o n hn => by
      obtain ⟨r, hr, hc⟩ := inScratch o n (by omega_using [hn]); exact ⟨r, List.mem_append_right _ hr, hc⟩))
    fun t₀ ⟨al₀, rd₀, K₀, f₀, k₀⟩ => ?_
  have p1₀ : t₀.gpr .a1 = s.gpr .a1 := k₀.gpr (by decide)
  have B₀ : Spec.Rc2.blockAt t₀.mem (s.gpr .a1) = Spec.Rc2.blockAt s.mem (s.gpr .a1) :=
    Proof.Rc2.blockAt_frame f₀ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hds.sub_right fun a h => by simp only [Region.Contains] at h ⊢; omega_using [h]
  apply WP.seq
  refine WP.mono (blockLoad_run t₀ (by
      rw [p1₀, k₀.2.1, k₀.2.2]
      obtain ⟨r, hr, hc⟩ := inData 0 4 (by omega_using [])
      rw [BitVec.add_zero] at hc
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [p1₀, k₀.2.1, k₀.2.2]
        obtain ⟨r, hr, hc⟩ := inData 4 4 (by omega_using []); exact ⟨r, List.mem_append_right _ hr, hc⟩))
    fun t₁ ⟨H₁, m₁, k₁⟩ => ?_
  apply WP.seq
  have E : KeyEnv (t₀.gpr .a2) t₁ := ⟨k₁.gpr (by decide), al₀, fun o n hn => by
    rw [k₁.2.1, k₁.2.2, k₀.2.1, k₀.2.2]; exact rd₀ o n hn⟩
  refine WP.mono (rounds_runsTo d t₁ E rfl _ H₁) fun t₂ ⟨H₂, m₂, k₂⟩ => ?_
  have p4 : t₂.gpr .a1 = s.gpr .a1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide), p1₀]
  refine WP.mono (blockStore_run t₂ H₂
    (by rw [p4, k₂.2.2, k₁.2.2, k₀.2.2]; simpa using inData 0 4 (by omega_using []))
    (by rw [p4, k₂.2.2, k₁.2.2, k₀.2.2]; exact inData 4 4 (by omega_using [])))
    fun t₃ ⟨m₃, _⟩ => ?_
  change Spec.Rc2.blockAt t₃.mem (s.gpr .a1) = _
  rw [m₃, p4, m₂, Proof.Rc2.blockAt_write64, cipher_rounds, m₁, K₀, p1₀, B₀]

/-- The registers the block functions write: no preserved register, nor `ra`. -/
def blockRegs : List Reg := [.a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5]

theorem block_ok (d : Spec.Rc2.Direction) (hw : writesOnly blockRegs (blockCode d) = true)
    (hn : callFree (blockCode d) = true) (s : State) (hs : (blockC d).pre s) :
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep blockRegs (block_wp d s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

end VG.Proof.Rc2.RISCV64

end

end

/-! # RC2-CBC on RISC-V: the calls of the block function -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem block_exec (d : Spec.Rc2.Direction) : ∀ s, (blockC d).pre s →
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  cases d
  · exact block_ok .encrypt (by lit_decide) (by lit_decide)
  · exact block_ok .decrypt (by lit_decide) (by lit_decide)

theorem blockCall_eq (d : Spec.Rc2.Direction) :
    ∃ nm, blockCall d = .call nm (blockCode d) := by cases d <;> exact ⟨_, rfl⟩

theorem blockCode_noFrames (d : Spec.Rc2.Direction) : (blockCode d).noFrames = true := by
  cases d
  · exact (by lit_decide : encryptBlock.noFrames = true)
  · exact (by lit_decide : decryptBlock.noFrames = true)

/-- A call of the block function on the block at `p`, with the schedule at
`T` and the working space at `W`. -/
theorem call_run (d : Spec.Rc2.Direction) (u : State) {T p W : Addr} (h3 : u.gpr .a0 = T) (h4 : u.gpr .a1 = p)
    (h5 : u.gpr .a2 = W) (hal : W.toNat % 8 = 0) (hfp : p.toNat + 8 ≤ 2 ^ 64) (hfw : W.toNat + 256 ≤ 2 ^ 64)
    (hTW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 256⟩) (hpW : (⟨p, 8⟩ : Region).Disjoint ⟨W, 256⟩)
    (hc : Covers ([⟨T, 128⟩] ++ [⟨p, 8⟩, ⟨W, 256⟩]) (u.rd ++ u.wr))
    (hw : Covers [⟨p, 8⟩, ⟨W, 256⟩] u.wr) :
    WP isa (blockCall d) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨p, 8⟩, ⟨W, 256⟩] u.mem u'.mem ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      Spec.Rc2.blockAt u'.mem p = cipher d (Spec.Rc2.scheduleAt u.mem T) (Spec.Rc2.blockAt u.mem p) := by
  obtain ⟨nm, e⟩ := blockCall_eq d
  rw [e]
  have e3 : u.callEntry.gpr .a0 = T := by rw [State.callEntry_gpr u (by decide), h3]
  have e4 : u.callEntry.gpr .a1 = p := by rw [State.callEntry_gpr u (by decide), h4]
  have e5 : u.callEntry.gpr .a2 = W := by rw [State.callEntry_gpr u (by decide), h5]
  refine WP.call (k := blockC d) (block_exec d) (rd := [⟨T, 128⟩]) (wr := [⟨p, 8⟩, ⟨W, 256⟩]) ?_ hc hw
    (fun s' hr hwr _ hf hp _ hpost => ⟨hr, hwr, hf, hp, ?_⟩) (blockCode_noFrames d)
  · show [(⟨T, 128⟩ : Region)] = [⟨u.callEntry.gpr .a0, 128⟩] ∧
      [(⟨p, 8⟩ : Region), ⟨W, 256⟩] = [⟨u.callEntry.gpr .a1, 8⟩, ⟨u.callEntry.gpr .a2, 256⟩] ∧
      (u.callEntry.gpr .a2).toNat % 8 = 0 ∧ (u.callEntry.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧
      (u.callEntry.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧
      (⟨u.callEntry.gpr .a0, 128⟩ : Region).Disjoint ⟨u.callEntry.gpr .a2, 256⟩ ∧
      (⟨u.callEntry.gpr .a1, 8⟩ : Region).Disjoint ⟨u.callEntry.gpr .a2, 256⟩
    rw [e3, e4, e5]
    exact ⟨rfl, rfl, hal, hfp, hfw, hTW, hpW⟩
  · have := hpost
    simp only [blockC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [e3, e4] at this
    exact this

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! ### `Rc2.RISCV64.Cbc.Step`, which only this module used -/

section

/-!
# RC2-CBC on RISCV64: one block

`body_run`: an iteration of the loop takes the invariant `Inv` from `j` blocks
done to `j + 1`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

/-- The buffers: the schedule at `T`, the chaining value at `I`, `n` blocks
at `D` and the working space at `W`, apart, not wrapping around, the working
space aligned. -/
structure Regions (T I D W : Addr) (n : Nat) : Prop where
  TI : (⟨T, 128⟩ : Region).Disjoint ⟨I, 8⟩
  TD : (⟨T, 128⟩ : Region).Disjoint ⟨D, 8 * n⟩
  TW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 512⟩
  ID : (⟨I, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  IW : (⟨I, 8⟩ : Region).Disjoint ⟨W, 512⟩
  DW : (⟨D, 8 * n⟩ : Region).Disjoint ⟨W, 512⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  fitW : W.toNat + 512 ≤ 2 ^ 64
  al : W.toNat % 8 = 0

/-- After `j` of the `n` blocks, from memory `m₀` and with our caller's
registers `g`. -/
structure Inv (d : Spec.Rc2.Direction) (T I D W : Addr) (n : Nat) (g : Reg → BitVec 64) (m₀ : Mem)
    (s₀ : State) (j : Nat) (t : State) : Prop where
  rd : t.rd = [⟨T, 128⟩]
  wr : t.wr = [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]
  s1 : t.gpr .s1 = T
  s2 : t.gpr .s2 = I
  s3 : t.gpr .s3 = D + BitVec.ofNat 64 (8 * j)
  s4 : t.gpr .s4 = BitVec.ofNat 64 (n - j)
  s5 : t.gpr .s5 = W
  pres : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → t.gpr r = s₀.gpr r
  saved : Spill.Saved W g saved t.mem
  sched : Spec.Rc2.scheduleAt t.mem T = Spec.Rc2.scheduleAt m₀ T
  done : Spec.Rc2.blocksAt t.mem D j =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).1
  iv : Spec.Rc2.blockAt t.mem I =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).2
  rest : ∀ i, j ≤ i → i < n → Spec.Rc2.blockAt t.mem (D + BitVec.ofNat 64 (8 * i)) =
    Spec.Rc2.blockAt m₀ (D + BitVec.ofNat 64 (8 * i))

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide
theorem saved_in : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 312 := by decide

/-- What a step leaves alone: anything apart from the block, the chaining
value and the block function's working space. -/
theorem step_frame {T I D W : Addr} {n j : Nat} (R : Regions T I D W n) (hj : j < n) {m m' : Mem}
    (F : Frame [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] m m') :
    Spec.Rc2.scheduleAt m' T = Spec.Rc2.scheduleAt m T ∧
    (∀ g, Spill.Saved W g saved m → Spill.Saved W g saved m') ∧
    (∀ i, i < n → i ≠ j → Spec.Rc2.blockAt m' (D + BitVec.ofNat 64 (8 * i)) =
      Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * i))) ∧
    Spec.Rc2.blocksAt m' D j = Spec.Rc2.blocksAt m D j := by
  have hf := R.fit
  obtain bj : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨Proof.Rc2.scheduleAt_frame F T ?_, fun g sv => sv.frame F ?_, fun i hi hne => Proof.Rc2.blockAt_frame F _ ?_,
    Proof.Rc2.blocksAt_frame F D j ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact R.TD.sub_right bj
    · exact R.TI
    · exact R.TW.sub_right W256
  · intro p hp r hr
    obtain hb := saved_in p hp
    obtain slot : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ ⟨W, 512⟩ := Offset.sub_base W (by omega_using [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (R.DW.sub_left bj).symm.sub_left slot
    · exact (R.IW.symm.sub_left slot)
    · exact Offset.disjoint_base W (by omega_using [hb]) (by omega_using [hb])
  · have bi : Region.Sub ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hi])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.disjoint D (by omega_using [hne]) (by omega_using [hf, hi]) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bi).symm
    · exact (R.DW.sub_left bi).sub_right W256
  · have bp : Region.Sub ⟨D, 8 * j⟩ ⟨D, 8 * n⟩ := Region.sub_prefix (by omega_using [hj])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.base_disjoint D (by omega_using []) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bp).symm
    · exact (R.DW.sub_left bp).sub_right W256

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Rc2.blocksAt m p 1 = [Spec.Rc2.blockAt m p] := by
  simp [Spec.Rc2.blocksAt]

/-- The done blocks, one more. -/
theorem done_succ (m : Mem) (D : Addr) (j : Nat) :
    Spec.Rc2.blocksAt m D (j + 1) = Spec.Rc2.blocksAt m D j ++ [Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * j))] := by
  rw [Proof.Rc2.blocksAt_add, blocksAt_one]

theorem covers {T I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers ([⟨T, 128⟩] ++ [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩])
      ([⟨T, 128⟩] ++ [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem covers_wr {I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩] [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Rc2.RISCV64.Cbc

end

end


/-! # RC2-CBC on RISCV64: an iteration of the loop -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem count_sub {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (n - j) - 1#64 = BitVec.ofNat 64 (n - (j + 1)) := by
  rw [Offset.ofNat_sub_ofNat (by omega_using [hj])]; congr 1

theorem preserved_not : ∀ r ∈ preserved, r ∉ saved.map Prod.fst →
    r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2, .s3, .s4, .s6] := by decide

theorem enc_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .encrypt iv [b] =
      ([Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)], Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)) := rfl

theorem dec_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .decrypt iv [b] = ([Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock k b) iv], b) := rfl

theorem body_run (d : Spec.Rc2.Direction) {T I D W : Addr} {n : Nat} {g : Reg → BitVec 64} {m₀ : Mem} {s₀ : State}
    (R : Regions T I D W n) {j : Nat} (hj : j < n) (t : State) (H : Inv d T I D W n g m₀ s₀ j t) :
    WP isa (body d) t fun t' => Inv d T I D W n g m₀ s₀ (j + 1) t' ∧
      (t'.gpr .s4 != (0 : BitVec 64)) = !decide (j + 1 = n) := by
  have hf := R.fit
  let p := D + BitVec.ofNat 64 (8 * j)
  obtain pIn : InRegions t.wr p 8 := by
    rw [H.wr]; exact ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hf])⟩
  obtain pIn' : InRegions (t.rd ++ t.wr) p 8 := by
    obtain ⟨r, hr, hc⟩ := pIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain iIn : InRegions t.wr I 8 := by rw [H.wr]; exact ⟨⟨I, 8⟩, by simp, Region.contains_self _ _⟩
  obtain iIn' : InRegions (t.rd ++ t.wr) I 8 := by
    obtain ⟨r, hr, hc⟩ := iIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain bj : Region.Sub ⟨p, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain pI : (⟨p, 8⟩ : Region).Disjoint ⟨I, 8⟩ := (R.ID.sub_right bj).symm
  have r28 : t.gpr .s3 = p := H.s3
  obtain b₀ : Spec.Rc2.blockAt t.mem p = Spec.Rc2.blockAt m₀ p := H.rest j (Nat.le_refl _) hj
  obtain hpt : p.toNat = D.toNat + 8 * j := by
    simp only [p, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega_using [hj, hf]), Nat.mod_eq_of_lt (by omega_using [hj, hf])]
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  have hfw := R.fitW
  obtain spec := Proof.Rc2.cbc_append (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I)
    (Spec.Rc2.blocksAt m₀ D j) [Spec.Rc2.blockAt m₀ p]
  unfold body
  cases d with
  | encrypt =>
    apply WP.seq
    refine WP.mono (beforeEnc_run t H.s1 H.s2 r28 H.s5 pIn' pIn iIn')
      fun t₁ ⟨a3, a4, a5, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .encrypt t₁ a3 a4 a5 R.al (by omega_using [hj, hf, hpt]) (by omega_using [hfw]) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    obtain h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    obtain h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    refine WP.mono (afterEnc_run t₂ h27 h28 h29 pIn₂ iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    -- the frame of the whole step
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      refine Frame.trans (Frame.trans ?_ (F₂.mono (by simp))) ?_
      · rw [m₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      · rw [m₃]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    -- the new block and chaining value
    obtain out : Spec.Rc2.blockAt t₂.mem p =
        Spec.Rc2.encryptBlock (Spec.Rc2.scheduleAt m₀ T) (Proof.Rc2.xorBlock (Spec.Rc2.blockAt m₀ p)
          (Spec.Rc2.blockAt t.mem I)) := by
      obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by
        rw [m₁, Proof.Rc2.scheduleAt_frame (Proof.Rc2.frame_store64 _ _ _) T (by simpa using R.TD.sub_right bj),
          H.sched]
      rw [c₂, hs₁, m₁, Proof.Rc2.blockAt_xor, b₀]; rfl
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p = Spec.Rc2.blockAt t₂.mem p := by
      rw [m₃]; exact Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI)
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt t₂.mem p := by rw [m₃, Proof.Rc2.blockAt_copy]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s1], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s5],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, enc_spec, ← H.iv, b₃, out]
    · rw [done_succ, spec, enc_spec, ← H.iv, i₃, out]
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])
  | decrypt =>
    apply WP.seq
    refine WP.mono (beforeDec_run t H.s1 r28 H.s5 pIn') fun t₁ ⟨a3, a4, a5, a31, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .decrypt t₁ a3 a4 a5 R.al (by omega_using [hj, hf, hpt]) (by omega_using [hfw]) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.s6, .a7, .t1, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    obtain h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    obtain h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    obtain h31 : t₂.gpr .s6 = t.mem.readW p 64 := by rw [P₂ _ (by decide), a31]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain pW₂ : InRegions t₂.wr p 8 := by rw [wr₂, k₁.2.2]; exact pIn
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    obtain iIn₂' : InRegions (t₂.rd ++ t₂.wr) I 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact iIn'
    refine WP.mono (afterDec_run t₂ h27 h28 h29 h31 pIn₂ pW₂ iIn₂' iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      rw [← m₁]
      refine Frame.trans (F₂.mono (by simp)) ?_
      rw [m₃]
      obtain f₁ : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t₂.mem
          (t₂.mem.writeW p (t₂.mem.readW p 64 ^^^ t₂.mem.readW I 64)) :=
        (Frame.refl _ _).writeW (r := ⟨p, 8⟩) (by simp) _ (Region.contains_self _ _)
      exact f₁.writeW (r := ⟨I, 8⟩) (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    obtain i₂ : Spec.Rc2.blockAt t₂.mem I = Spec.Rc2.blockAt t.mem I := by
      rw [Proof.Rc2.blockAt_frame F₂ I (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact pI.symm
        · exact R.IW.sub_right (Region.sub_prefix (by decide))), m₁]
    obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by rw [m₁, H.sched]
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p =
        Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m₀ T) (Spec.Rc2.blockAt m₀ p))
          (Spec.Rc2.blockAt t.mem I) := by
      rw [m₃, Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI),
        Proof.Rc2.blockAt_xor, i₂, c₂, hs₁, m₁, b₀]; rfl
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt m₀ p := by
      rw [m₃, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, b₀]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s1], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s5],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, dec_spec, ← H.iv, b₃]
    · rw [done_succ, spec, dec_spec, i₃]
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! # Verified RC2-CBC on RISCV64 -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

/-- The CBC contract as the code sees it. -/
def cbcC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
    let buf : Region := ⟨s.gpr .a4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ key.Disjoint iv ∧ key.Disjoint data ∧
      key.Disjoint buf ∧ iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 512 ≤ 2 ^ 64
  post s s' :=
    let result := Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .a0)) d (Spec.Rc2.blockAt s.mem (s.gpr .a1))
      (Spec.Rc2.blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .a2) (s.gpr .a3).toNat = result.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .a1) = result.2
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem save_eq : save = Spill.saveCode .a4 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .s5 saved := rfl

theorem cbc_wp (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    WP isa (cbc d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      (cbcC d).post s s' := by
  obtain ⟨hrd, hwr, hal, TI, TD, TW, ID, IW, DW, fit, fitW⟩ := hs
  let T := s.gpr .a0
  let I := s.gpr .a1
  let D := s.gpr .a2
  let n := (s.gpr .a3).toNat
  let W := s.gpr .a4
  have R : Regions T I D W n := ⟨TI, TD, TW, ID, IW, DW, fit, fitW, hal⟩
  let g := s.gpr
  have wW : ∀ p ∈ saved, InRegions s.wr (s.gpr .a4 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    have hb := saved_in p hp
    rw [hwr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold cbc
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok hal saved_fits wW ?_
  let M₀ := Spill.saveMem s.mem (s.gpr .a4) g saved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => by have := saved_in p hp; omega_arith)
    (by decide) _ _ _
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4, .s5] (c := .block setup) (Q := fun t =>
      t.gpr .s1 = T ∧ t.gpr .s2 = I ∧ t.gpr .s3 = D ∧ t.gpr .s4 = s.gpr .a3 ∧ t.gpr .s5 = W ∧ t.mem = M₀)
    (by unfold setup; rrun [mov, T, I, D, W, M₀, g]) (by rfl) rfl)
    fun t₀ ⟨⟨a26, a27, a28, a29, a30, m₀⟩, k₀⟩ => ?_
  have H₀ : Inv d T I D W n g M₀ s 0 t₀ := by
    refine ⟨by rw [k₀.2.1]; exact hrd, by rw [k₀.2.2]; exact hwr, a26, a27, by rw [a28]; simp, by
      rw [a29, Nat.sub_zero]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm, a30,
      fun r hr hn => ?_, by rw [m₀]; exact Spill.saveMem_saved (by decide) _ _ _, by rw [m₀], by rw [m₀]; rfl,
      by rw [m₀]; rfl, fun i _ _ => by rw [m₀]⟩
    rw [k₀.gpr (by revert hn; revert r; decide)]
  apply WP.seq
  have loop : WP isa (.ite (.zero .s4) (.block []) (.loop (body d) (.nonzero .s4))) t₀
      (Inv d T I D W n g M₀ s n) := by
    have hz : isa.eval (.zero .s4) t₀ = some (decide (n = 0)) := by
      rw [Steps.eval_zero, H₀.s4, Nat.sub_zero, Steps.ofNat_beq_zero (by omega_arith)]
    refine WP.ite _ hz (fun h => WP.block_nil ?_) (fun h => countLoop _ _ _ n
      (fun j hj t H => body_run d R hj t H) 0 (by have := of_decide_eq_false h; omega_arith) t₀ H₀)
    have e : n = 0 := of_decide_eq_true h
    rw [e]; rw [e] at H₀; exact H₀
  refine WP.mono loop fun t H => ?_
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp hal H.s5 saved_fits (by decide) (fun p hp => ?_) H.saved)
    fun t' Rs => ⟨fun r hr => ?_, ?_, ?_⟩
  · have hb := saved_in p hp
    rw [H.rd, H.wr]
    exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · by_cases h : r ∈ saved.map Prod.fst
    · exact Rs.gpr_of (.inl h)
    · rw [Rs.other r h, H.pres r hr h]
  · exact Rs.gpr_of (.inl (by decide))
  · have hS : Spec.Rc2.scheduleAt M₀ T = Spec.Rc2.scheduleAt s.mem T :=
      Proof.Rc2.scheduleAt_frame F₀ T (by simpa using TW)
    have hI : Spec.Rc2.blockAt M₀ I = Spec.Rc2.blockAt s.mem I := Proof.Rc2.blockAt_frame F₀ I (by simpa using IW)
    have hD : Spec.Rc2.blocksAt M₀ D n = Spec.Rc2.blocksAt s.mem D n :=
      Proof.Rc2.blocksAt_frame F₀ D n (by simpa using DW)
    show Spec.Rc2.blocksAt t'.mem D n = _ ∧ Spec.Rc2.blockAt t'.mem I = _
    rw [Rs.mem, H.done, H.iv, hS, hI, hD]
    exact ⟨rfl, rfl⟩

theorem cbc_ok (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    ∃ t s', Exec isa (cbc d) s t s' ∧ abiPreserved s s' ∧ (cbcC d).post s s' := by
  obtain ⟨t, s', he, ⟨hp, hra, hq⟩, _, _, hsp⟩ := WP.rdwr (cbc_wp d s hs)
  exact ⟨t, s', he, ⟨hp, hsp, hra⟩, hq⟩

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! # RC2-CBC in place on RISCV64, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64

def scratchSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

def frameSat : State := { scratchSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩] }

theorem encryptChained_ct : ConstantTime isa (cbcC .encrypt).pre (cbcC .encrypt).pub Impl.Rc2.RISCV64.Cbc.encrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptChained_verified :
    Verified RISCV64.target Impl.Rc2.RISCV64.Cbc.encrypt (Proof.Rc2.cbcEncChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .encrypt) (cbc_ok .encrypt) encryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := by sig_implies_sat [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] [scratchSat] using scratchSat }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2

theorem encryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcEncryptChainedContract abi 512).pre s := by
  implies_sat [Spec.Rc2.cbcEncryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs]
    [frameSat, scratchSat] using frameSat

theorem encryptChained_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) encryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcEncChainedPostOut_local _) encryptChainedFrameSat

theorem decryptChained_ct : ConstantTime isa (cbcC .decrypt).pre (cbcC .decrypt).pub Impl.Rc2.RISCV64.Cbc.decrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptChained_verified :
    Verified RISCV64.target Impl.Rc2.RISCV64.Cbc.decrypt (Proof.Rc2.cbcDecChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .decrypt) (cbc_ok .decrypt) decryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := by sig_implies_sat [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] [scratchSat] using scratchSat }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2

theorem decryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcDecryptChainedContract abi 512).pre s := by
  implies_sat [Spec.Rc2.cbcDecryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs]
    [frameSat, scratchSat] using frameSat

theorem decryptChained_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) decryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcDecChainedPostOut_local _) decryptChainedFrameSat

end VG.Proof.Rc2.RISCV64.Cbc
