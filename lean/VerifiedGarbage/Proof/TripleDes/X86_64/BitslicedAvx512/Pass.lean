module
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Step
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit

/-! ### `TripleDes.X86_64.BitslicedAvx512.Round`, which only this module used -/

section

/-!
# An AVX-512 round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`r8` into `rax`, advances the pointer by the step `r9`, and does to the 64
state words what `roundW` does, with the key's low 48 bits.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr rdOff wrOff flipRole rdOff_flip
  wrOff_flip)

/-! ## The round key -/

theorem keyLoad_ok {s : State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .rax = (s.mem.readW (s.gpr .r8) 64).rotateRight 48 ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧ (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let kp := s.gpr .r8
  let K := s.mem.readW kp 64
  let δ := s.gpr .r9
  let s₁ := s.setReg .rax K
  obtain e₁ : exec (.mov .rax (.mem { base := .r8, disp := 0 })) s = some s₁ := by
    obtain hea : s.ea { base := .r8, disp := 0 } = kp := by simp [State.ea, kp]
    obtain hl : s.load64 kp = some K := by simp only [State.load64, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  let v := kp + δ
  let s₂ := (arithFlags s₁ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .r8 v
  obtain e₂ : exec (.alu .add .r8 (.reg .r9)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    obtain ha : s₁.gpr .r8 = kp := by simp [s₁, gpr_setReg, kp]
    obtain hd : s₁.gpr .r9 = δ := by simp [s₁, gpr_setReg, δ]
    rw [ha, hd]
  let s₃ := (s₂.setFlags (some ((s₂.gpr .rax).rotateRight 48).msb) none s₂.zf s₂.sf).setReg .rax
    ((s₂.gpr .rax).rotateRight 48)
  obtain e₃ : exec (.shift .ror .rax 48) s₂ = some s₃ := by
    simp only [exec, execShift]; rfl
  refine ⟨s₃, ?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, K, kp]
  · simp [s₃, s₂, gpr_setReg, gpr_setFlags, v, kp, δ]
  · simp [s₃, s₂, s₁, gpr_setReg, gpr_setFlags, h1, h2]
  · simp [s₃, s₂, s₁, mem_setReg, mem_setFlags, mem_arithFlags]
  · simp [s₃, s₂, s₁, rd_setReg, rd_setFlags, rd_arithFlags]
  · simp [s₃, s₂, s₁, wr_setReg, wr_setFlags, wr_arithFlags]

/-! ## The S-boxes -/

def stepsCode (n : Nat) : List Instr := (List.range n).flatMap sboxStep

theorem stepsCode_succ (n : Nat) :
    stepsCode (n + 1) = stepsCode n ++ sboxStep n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- S-box `j`'s key bits are at the top of the rotated key, shifted by the
bits of the S-boxes before it. -/
theorem keyBits (K : BitVec 64) {j i : Nat} (hj : j < 8) (hi : i < 6) :
    (K.rotateRight 48 <<< (6 * j)).getLsbD (58 + i) = (K.setWidth 48).getLsbD (inBit j i) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth]
  obtain h1 : ¬ 58 + i < 6 * j := by omega_using [hj]
  obtain h2 : ¬ 58 + i - 6 * j < 64 - 48 % 64 := by omega_using [hj]
  obtain h3 : 58 + i - 6 * j - (64 - 48 % 64) = inBit j i := by unfold inBit; omega_using [hj]
  obtain h4 : inBit j i < 48 := by unfold inBit; omega_using [hi]
  simp only [h1, decide_false, Bool.not_false, Bool.true_and, h2, ite_false, h3, h4, decide_true,
    Bool.true_and, show 58 + i < 64 by omega_using [hi], show 58 + i - 6 * j < 64 by omega_using [hi]]

theorem stepsCode_ok (ρ : Role) (K : BitVec 64) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hp : Ptrs ρ s) (hr : s.gpr .rax = K.rotateRight 48) :
    ∃ s', runBlock isa (stepsCode n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      s'.gpr .rax = K.rotateRight 48 <<< (6 * n) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, by simp [hr], fun _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, r₁, g₁, rd₁, wr₁, f₁⟩ := ih (by omega_using [hn])
    obtain c₁ := g₁ .rcx (by decide) (by decide)
    obtain si₁ := g₁ .rsi (by decide) (by decide)
    obtain h₁ := h.congr c₁ si₁ wr₁
    obtain hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) si₁
    obtain ⟨s₂, run₂, w₂, r₂, g₂, rd₂, wr₂, f₂⟩ :=
      sboxStep_ok ρ (by omega_using [hn] : n < 8) h₁ hp₁ (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact keyBits K (by omega_using [hn]) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega_using [hn]) w₁ (w₁ x hx)
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega_using []]
    · rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
        show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
      exact f₁.trans f₂

/-! ## Counting down a register -/

theorem sub1_run (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.imm 1)] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧
      s'.zf = some (s.gpr r - 1 == 0) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.gpr r
  let t := v - (1 : BitVec 32).signExtend 64
  refine ⟨(arithFlags s t (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) t)).setReg r t, ?_, ?_, ?_, fun r' h => ?_,
    ?_, ?_, ?_⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]; rfl
  · simp only [zf_setReg, zf_arithFlags]; rfl
  · simp [gpr_setReg, h]
  · simp [mem_setReg, mem_arithFlags]
  · simp [rd_setReg, rd_arithFlags]
  · simp [wr_setReg, wr_arithFlags]

/-! ## The halves' pointers -/

theorem swapPtrs_run (s : State) :
    ∃ s', runBlock isa swapPtrs s = some s' ∧ s'.gpr .r12 = s.gpr .r13 ∧ s'.gpr .r13 = s.gpr .r12 ∧
      (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setReg .rbx (s.gpr .r12)
  let s₂ := s₁.setReg .r12 (s₁.gpr .r13)
  let s₃ := s₂.setReg .r13 (s₂.gpr .rbx)
  refine ⟨s₃, ?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_⟩
  · rw [swapPtrs, runBlock_cons, show exec (.mov .rbx (.reg .r12)) s = some s₁ from rfl, runStep_some,
      runBlock_cons, show exec (.mov .r12 (.reg .r13)) s₁ = some s₂ from rfl, runStep_some,
      runBlock_cons, show exec (.mov .r13 (.reg .rbx)) s₂ = some s₃ from rfl, runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg]
  · simp [s₃, s₂, s₁, gpr_setReg]
  · simp [s₃, s₂, s₁, gpr_setReg, a, b, c]
  · simp [s₃, s₂, s₁, mem_setReg]
  · simp [s₃, s₂, s₁, rd_setReg]
  · simp [s₃, s₂, s₁, wr_setReg]

/-! ## A round -/

theorem round_eq : round = keyLoad ++ stepsCode 8 ++ swapPtrs ++ ([.alu .sub .r10 (.imm 1)] : List Instr) :=
  rfl

theorem round_ok (ρ : Role) {s : State} (h : Room s) (hp : Ptrs ρ s)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .r8) 8) :
    ∃ s', runBlock isa round s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW (s.gpr .r8) 64).setWidth 48) (words s) x) ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0) ∧ Ptrs (flipRole ρ) s' ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, k₁, g₁, m₁, rd₁, wr₁⟩ := keyLoad_ok hkey
  obtain c₁ := g₁ .rcx (by decide) (by decide)
  obtain si₁ := g₁ .rsi (by decide) (by decide)
  obtain h₁ := h.congr c₁ si₁ wr₁
  obtain hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) si₁
  obtain ⟨s₂, run₂, w₂, -, g₂, rd₂, wr₂, f₂⟩ :=
    stepsCode_ok ρ _ (Nat.le_refl 8) h₁ hp₁ r₁
  obtain ⟨s₃, run₃, p12₃, p13₃, g₃, m₃, rd₃, wr₃⟩ := swapPtrs_run s₂
  obtain ⟨s₄, run₄, cnt₄, zf₄, g₄, m₄, rd₄, wr₄⟩ := sub1_run s₃ .r10
  obtain g₂₁ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1 h2, g₁ r h1 h3]
  obtain g₄₃ : ∀ r, r ≠ .rbx → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s₄.gpr r = s₂.gpr r := fun r a b c d => by
    rw [g₄ r b, g₃ r a c d]
  obtain r10₃ : s₃.gpr .r10 = s.gpr .r10 := by
    rw [g₃ _ (by decide) (by decide) (by decide), g₂₁ _ (by decide) (by decide) (by decide)]
  obtain si₄ : s₄.gpr .rsi = s.gpr .rsi := by
    rw [g₄₃ _ (by decide) (by decide) (by decide) (by decide), g₂₁ _ (by decide) (by decide) (by decide)]
  obtain e₄ : ∀ y, words s₄ y = words s₂ y := fun y => by
    simp only [words, m₄, m₃, si₄, g₂₁ .rsi (by decide) (by decide) (by decide)]
  refine ⟨s₄, ?_, fun x hx => ?_, ?_, by rw [cnt₄, r10₃], by rw [zf₄, r10₃], ⟨?_, ?_⟩,
    fun r h1 h2 h3 h4 h5 h6 => ?_, rd₄.trans (rd₃.trans (rd₂.trans rd₁)),
    wr₄.trans (wr₃.trans (wr₂.trans wr₁)), ?_⟩
  · rw [round_eq]
    exact runBlock_cat_some (runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃) run₄
  · rw [e₄ x, w₂ x hx]
    obtain e : ∀ y, words s₁ y = words s y := fun y => by simp only [words, m₁, si₁]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [g₄₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide), k₁]
  · rw [g₄ _ (by decide), p12₃, si₄, g₂₁ _ (by decide) (by decide) (by decide), hp.wr, rdOff_flip]
  · rw [g₄ _ (by decide), p13₃, si₄, g₂₁ _ (by decide) (by decide) (by decide), hp.rd, wrOff_flip]
  · rw [g₄₃ r h2 h4 h5 h6, g₂₁ r h1 h2 h3]
  · rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
      show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
    rw [m₁] at f₂
    rw [m₄, m₃]
    exact f₂

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-!
# An AVX-512 DES pass on the machine

A pass chooses its first key's address (`r8`) and the step between keys
(`r9`) by the pass count (`r11`, `passStart`), points at the halves, runs
sixteen rounds (counted in `r10`), each exchanging the halves' pointers,
exchanges the halves and counts the pass. `pass_ok`: it does to the state
words what `swapW (pairs …)` does, with the keys read at
the addresses `a₀ + r δ`, which are apart from the scratch buffer and the
state words.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW partner rounds roleAt roleAt_succ rounds_two_mul
  rdOff wrOff)
open VG.Proof.TripleDes.X86_64.Bitsliced (keyAt kptr_succ cnt_sub passA passD roundW_congr pairs_congr
  pairs_keys_congr swapW_congr)
open VG.Impl.TripleDes.X86_64.Bitslice (passKey)

/-- Eight readable bytes, apart from the scratch buffer and the state words. -/
structure Apart (s : State) (a : Addr) : Prop where
  read : InRegions (s.rd ++ s.wr) a 8
  scratch : (⟨a, 8⟩ : Region).Disjoint (scratchR s)
  state : (⟨a, 8⟩ : Region).Disjoint (stateR s)

theorem Apart.congr {s s' : State} {a : Addr} (h : Apart s a) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hsi : s'.gpr .rsi = s.gpr .rsi) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Apart s' a where
  read := by rw [hrd, hwr]; exact h.read
  scratch := by simp only [scratchR, hc]; exact h.scratch
  state := by simp only [stateR, hsi]; exact h.state

theorem Apart.readW {s : State} {a : Addr} (h : Apart s a) {m : Mem}
    (hf : Frame [spillR s, stateR s] s.mem m) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW (Region.contains_self a 8) (by simpa using ⟨h.scratch.sub_right (spill_sub s), h.state⟩)
    (by decide)

/-! ## The loop of rounds -/

/-- The registers a pass changes. -/
def PassRegs (r : Reg) : Prop :=
  r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 ∧ r ≠ .r13

structure LoopInv (s₀ : State) (m : Nat) (s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ 16
  words : ∀ x < 64, words s x = rounds (keyAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9)) (16 - m) (words s₀) x
  key : s.gpr .r8 = s₀.gpr .r8 + BitVec.ofNat 64 (16 - m) * s₀.gpr .r9
  cnt : s.gpr .r10 = BitVec.ofNat 64 m
  ptrs : Ptrs (roleAt (16 - m)) s
  gpr : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

structure LoopPost (s₀ s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = rounds (keyAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9)) 16 (words s₀) x
  gpr : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

theorem roundLoop_ok {s₀ : State} (hk : ∀ r < 16,
      Apart s₀ (s₀.gpr .r8 + BitVec.ofNat 64 r * s₀.gpr .r9))
    (m₀ : Nat) (s₁ : State) (hs₁ : LoopInv s₀ m₀ s₁) :
    WP isa (.loop (.block round) .ne) s₁ (LoopPost s₀) := by
  refine WP.loop (M := isa) (LoopInv s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let a₀ := s₀.gpr .r8
  let δ := s₀.gpr .r9
  have hpos := hs.pos
  have hle := hs.le
  obtain hδ : s.gpr .r9 = δ := hs.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain hc : s.gpr .rcx = s₀.gpr .rcx :=
    hs.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain hsi : s.gpr .rsi = s₀.gpr .rsi :=
    hs.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain a₁ : Apart s (s.gpr .r8) := by
    rw [hs.key]; exact (hk (16 - m) (by omega_using [hpos])).congr hc hsi hs.rd hs.wr
  obtain ⟨s', run', w', key', cnt', zf', ptrs', g', rd', wr', f'⟩ :=
    round_ok (roleAt (16 - m)) hs.room hs.ptrs a₁.read
  refine WP.of_runBlock ⟨s', run', ?_⟩
  obtain frame' : Frame [spillR s₀, stateR s₀] s₀.mem s'.mem := by
    have := hs.frame
    rw [show spillR s = spillR s₀ by simp only [spillR, hc],
      show stateR s = stateR s₀ by simp only [stateR, hsi]] at f'
    exact this.trans f'
  obtain k1 : (s.mem.readW (s.gpr .r8) 64).setWidth 48 = keyAt s₀.mem a₀ δ (16 - m) := by
    rw [hs.key]; simp only [keyAt]
    rw [((hk (16 - m) (by omega_using [hpos])).readW hs.frame)]
  obtain words' : ∀ x < 64, words s' x = rounds (keyAt s₀.mem a₀ δ) (16 - m + 1) (words s₀) x := by
    intro x hx
    rw [w' x hx, k1]
    simp only [rounds]
    exact roundW_congr _ _ hs.words x hx
  obtain gpr' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s₀.gpr r :=
    fun r a b c d e f => (g' r a b c d e f).trans (hs.gpr r a b c d e f)
  obtain room' := hs.room.congr (g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) wr'
  obtain cntv : s.gpr .r10 - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [hs.cnt]
    exact cnt_sub m hs.pos
  rw [← roleAt_succ] at ptrs'
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', rd'.trans hs.rd, wr'.trans hs.wr, words', gpr', frame'⟩⟩
    show s'.zf.map (!·) = some false
    rw [zf', cntv]; rfl
  · right
    refine ⟨?_, m - 1, by omega_using [hpos], ⟨room', rd'.trans hs.rd, wr'.trans hs.wr, by omega_using [hpos, h1],
      by have := hs.le; omega_using [hle], ?_, ?_, ?_, ?_, gpr', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf', cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        have hm : m ≤ 16 := hs.le
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega_using [hle])] at this
        have := hs.pos
        omega_arith
      rw [this]; rfl
    · have e : 16 - (m - 1) = 16 - m + 1 := by have := hs.le; omega_using [hpos, hle]
      rw [e]; exact words'
    · rw [key', hs.key, hδ, kptr_succ]
      congr 3
      have := hs.le; omega_using [hpos, hle]
    · rw [cnt', cntv]
    · have e : 16 - (m - 1) = 16 - m + 1 := by have := hs.le; omega_using [hpos, hle]
      rw [e]; exact ptrs'

/-! ## The start of a pass -/

/-- What the start of a pass leaves. -/
structure StartPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  key : s'.gpr .r8 = s.gpr .rdi + BitVec.ofNat 64 (passKey d p).1
  step : s'.gpr .r9 = BitVec.ofInt 64 (passKey d p).2
  round : s'.gpr .r10 = 16
  ptrs : Ptrs .ba s'
  gpr : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem passKey_imm : ∀ d : Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 →
    (BitVec.ofNat 32 (passKey d p).1).signExtend 64 = BitVec.ofNat 64 (passKey d p).1 ∧
    (BitVec.ofInt 32 (passKey d p).2).signExtend 64 = BitVec.ofInt 64 (passKey d p).2 := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

/-- A comparison of a register with an immediate. -/
def cmpState (s : State) (r : Reg) (v : BitVec 32) : State :=
  arithFlags s (s.gpr r - v.signExtend 64) (decide ((s.gpr r).toNat < (v.signExtend 64).toNat))
    (subOverflow (s.gpr r) (v.signExtend 64) (s.gpr r - v.signExtend 64))

theorem cmp_run (s : State) (r : Reg) (v : BitVec 32) :
    runBlock isa [.alu .cmp r (.imm v)] s = some (cmpState s r v) := by
  rw [runBlock_cons]
  rfl

theorem passStart_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (hc : s.gpr .r11 = BitVec.ofNat 64 p) :
    WP isa (passStart d) s (StartPost d p s) := by
  -- the code of a branch, and what follows it
  obtain branch : ∀ (s₁ : State), s₁.gpr = s.gpr → s₁.mem = s.mem → s₁.rd = s.rd → s₁.wr = s.wr →
      WP isa (.block (passKeyCode d p)) s₁ (fun s₂ =>
        WP isa (.block [.mov .r10 (.imm 16), .mov .r12 (.reg .rsi), .alu .add .r12 (.imm 64),
          .mov .r13 (.reg .rsi)]) s₂ (StartPost d p s)) := by
    intro s₁ g₁ m₁ rd₁ wr₁
    let t₁ := s₁.setReg .r8 (s₁.gpr .rdi)
    let a := BitVec.ofNat 32 (passKey d p).1
    let t₂ := (arithFlags t₁ (t₁.gpr .r8 + a.signExtend 64)
      (decide (2 ^ 64 ≤ (t₁.gpr .r8).toNat + (a.signExtend 64).toNat))
      (addOverflow (t₁.gpr .r8) (a.signExtend 64) (t₁.gpr .r8 + a.signExtend 64))).setReg .r8
      (t₁.gpr .r8 + a.signExtend 64)
    let t₃ := t₂.setReg .r9 ((BitVec.ofInt 32 (passKey d p).2).signExtend 64)
    refine WP.of_runBlock ⟨t₃, ?_, ?_⟩
    · rw [passKeyCode, runBlock_cons, show exec (.mov .r8 (.reg .rdi)) s₁ = some t₁ from rfl,
        runStep_some, runBlock_cons, show exec (.alu .add .r8 (.imm a)) t₁ = some t₂ from rfl,
        runStep_some, runBlock_cons, show exec (.mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))) t₂ =
          some t₃ from rfl, runStep_some, runBlock_nil]
    let t₄ := t₃.setReg .r10 ((16 : BitVec 32).signExtend 64)
    let t₅ := t₄.setReg .r12 (t₄.gpr .rsi)
    let c := (64 : BitVec 32).signExtend 64
    let t₆ := (arithFlags t₅ (t₅.gpr .r12 + c) (decide (2 ^ 64 ≤ (t₅.gpr .r12).toNat + c.toNat))
      (addOverflow (t₅.gpr .r12) c (t₅.gpr .r12 + c))).setReg .r12 (t₅.gpr .r12 + c)
    let t₇ := t₆.setReg .r13 (t₆.gpr .rsi)
    refine WP.of_runBlock ⟨t₇, by
      rw [runBlock_cons, show exec (.mov .r10 (.imm 16)) t₃ = some t₄ from rfl, runStep_some,
        runBlock_cons, show exec (.mov .r12 (.reg .rsi)) t₄ = some t₅ from rfl, runStep_some,
        runBlock_cons, show exec (.alu .add .r12 (.imm 64)) t₅ = some t₆ from rfl, runStep_some,
        runBlock_cons, show exec (.mov .r13 (.reg .rsi)) t₆ = some t₇ from rfl, runStep_some,
        runBlock_nil], ?_⟩
    obtain ⟨i1, i2⟩ := passKey_imm d p hp.1 hp.2
    refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, fun r a b c d e => ?_, ?_, ?_, ?_⟩
    · simp [t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setReg, g₁, a, i1]
    · simp [t₇, t₆, t₅, t₄, t₃, gpr_setReg, i2]
    · simp [t₇, t₆, t₅, t₄, gpr_setReg]
    · simp [t₇, t₆, t₅, gpr_setReg] <;> rfl
    · simp [t₇, t₆, t₅, gpr_setReg, wrOff]
    · simp [t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setReg, a, b, c, d, e, g₁]
    · simp [t₇, t₆, t₅, t₄, t₃, t₂, t₁, mem_setReg, mem_arithFlags, m₁]
    · simp [t₇, t₆, t₅, t₄, t₃, t₂, t₁, rd_setReg, rd_arithFlags, rd₁]
    · simp [t₇, t₆, t₅, t₄, t₃, t₂, t₁, wr_setReg, wr_arithFlags, wr₁]
  apply WP.seq
  let t₁ := cmpState s .r11 3
  refine WP.of_runBlock ⟨t₁, cmp_run s .r11 3, ?_⟩
  apply WP.seq
  obtain zf₁ : isa.eval .e t₁ = some (p == 3) := by
    show t₁.zf = _
    simp only [t₁, cmpState, zf_arithFlags, hc]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    have : p = 3 := by simpa using h3
    subst this
    exact branch t₁ (by simp [t₁, cmpState]) (by simp [t₁, cmpState, mem_arithFlags])
      (by simp [t₁, cmpState, rd_arithFlags]) (by simp [t₁, cmpState, wr_arithFlags])
  · intro h3
    obtain hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := cmpState t₁ .r11 2
    refine WP.of_runBlock ⟨t₂, cmp_run t₁ .r11 2, ?_⟩
    obtain zf₂ : isa.eval .e t₂ = some (p == 2) := by
      show t₂.zf = _
      simp only [t₂, t₁, cmpState, zf_arithFlags, gpr_arithFlags, hc]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    obtain g₂ : t₂.gpr = s.gpr := by simp [t₂, t₁, cmpState]
    obtain m₂ : t₂.mem = s.mem := by simp [t₂, t₁, cmpState, mem_arithFlags]
    obtain rd₂ : t₂.rd = s.rd := by simp [t₂, t₁, cmpState, rd_arithFlags]
    obtain wr₂ : t₂.wr = s.wr := by simp [t₂, t₁, cmpState, wr_arithFlags]
    apply WP.ite (p == 2) zf₂
    · intro h2
      have : p = 2 := by simpa using h2
      subst this
      exact branch t₂ g₂ m₂ rd₂ wr₂
    · intro h2
      have : p = 1 := by have : p ≠ 2 := by simpa using h2
                         omega_using [hp, hp3, this]
      subst this
      exact branch t₂ g₂ m₂ rd₂ wr₂

/-! ## A pass -/

structure PassPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  room : Room s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  words : ∀ x < 64, words s' x =
    swapW (pairs (keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p)) 8 (words s)) x
  count : s'.gpr .r11 = s.gpr .r11 - 1
  zf : s'.zf = some (s.gpr .r11 - 1 == 0)
  gpr : ∀ r, PassRegs r → s'.gpr r = s.gpr r
  frame : Frame [spillR s, stateR s] s.mem s'.mem

theorem pass_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (h : Room s) (hc : s.gpr .r11 = BitVec.ofNat 64 p)
    (hk : ∀ r < 16, Apart s (passA d p (s.gpr .rdi) + BitVec.ofNat 64 r * passD d p)) :
    WP isa (pass d) s (PassPost d p s) := by
  apply WP.seq
  apply WP.mono (passStart_ok d hp hc)
  intro s₁ p₁
  obtain c₁ := p₁.gpr .rcx (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain si₁ := p₁.gpr .rsi (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain h₁ := h.congr c₁ si₁ p₁.wr
  apply WP.seq
  obtain hk₁ : ∀ r < 16, Apart s₁ (s₁.gpr .r8 + BitVec.ofNat 64 r * s₁.gpr .r9) := by
    intro r hr
    rw [p₁.key, p₁.step]; exact (hk r hr).congr c₁ si₁ p₁.rd p₁.wr
  obtain inv : LoopInv s₁ 16 s₁ := by
    refine ⟨h₁, rfl, rfl, by decide, by decide, fun _ _ => rfl, ?_, ?_, p₁.ptrs,
      fun _ _ _ _ _ _ _ => rfl, Frame.refl _ _⟩
    · simp
    · rw [p₁.round]; rfl
  apply WP.mono (roundLoop_ok hk₁ 16 s₁ inv)
  intro s₂ p₂
  have h₂ := p₂.room
  obtain ⟨s₃, run₃, sw₃, g₃, rd₃, wr₃, f₃⟩ := swapHalves_ok h₂
  obtain ⟨s₄, run₄, cnt₄, zf₄, g₄, m₄, rd₄, wr₄⟩ := sub1_run s₃ .r11
  refine WP.of_runBlock ⟨s₄, runBlock_cat_some run₃ run₄, ?_⟩
  obtain keys : ∀ r < 16, keyAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9) r =
      keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p) r := by
    intro r hr
    simp only [keyAt, p₁.key, p₁.step, p₁.mem]
    rfl
  obtain state₁ : ∀ x < 64, words s₁ x = words s x := fun x _ => by simp only [words, p₁.mem, si₁]
  obtain gs₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → r ≠ .r13 →
      s₂.gpr r = s.gpr r :=
    fun r a b c e f g h => (p₂.gpr r a b c f g h).trans (p₁.gpr r c e f g h)
  obtain r11₃ : s₃.gpr .r11 = s.gpr .r11 := by
    rw [g₃, gs₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain c₂ := gs₂ .rcx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain si₂ := gs₂ .rsi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨h.congr (by rw [g₄ _ (by decide), g₃, c₂]) (by rw [g₄ _ (by decide), g₃, si₂])
      (wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr))),
    rd₄.trans (rd₃.trans (p₂.rd.trans p₁.rd)),
    wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr)), fun x hx => ?_, ?_, ?_,
    fun r hr => ?_, ?_⟩
  · have e : words s₄ x = words s₃ x := by simp only [words, m₄, g₄ .rsi (by decide)]
    rw [e, sw₃ x hx]
    apply swapW_congr _ x hx
    intro y hy
    rw [p₂.words y hy, show (16 : Nat) = 2 * 8 from rfl, rounds_two_mul,
      pairs_keys_congr 8 (fun r hr => keys r (by omega_using [hr]))]
    exact pairs_congr _ 8 state₁ y hy
  · rw [cnt₄, r11₃]
  · rw [zf₄, r11₃]
  · obtain ⟨a, b, c, e, f, g, i, j⟩ := hr
    rw [g₄ r g, g₃, gs₂ r a b c e f i j]
  · have g₃' : Frame [spillR s, stateR s] s₂.mem s₃.mem := by
      refine f₃.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stateR s, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [stateR, si₂]; exact fun _ h => h⟩
    have g₂ := p₂.frame
    rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
      show stateR s₁ = stateR s by simp only [stateR, si₁], p₁.mem] at g₂
    rw [m₄]
    exact g₂.trans g₃'

end VG.Proof.TripleDes.X86_64.BitslicedAvx512
