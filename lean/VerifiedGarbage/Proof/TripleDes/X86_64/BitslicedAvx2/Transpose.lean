module

public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
public import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bitslice.TransposeIdx
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# The transposition of the AVX2 state

The 64 state words are the 32-byte slots at `rsi`. The transposition runs
two stages of eight groups each, in loops: a group moves and XORs bits
within the quadword lanes of eight words, masked with constants, so the
lane domain evaluates one group once, on words of atoms (bit `t` of word
`i` is atom `64 i + t`), for any base (`bodyA_check`, `bodyB_check`). The
first stage's group at word `i` exchanges the high three bits of the word
index and the bit index of the words `i + 8 k` (`stA`); the second's group
at word `8 g` exchanges the low three bits of those of the words `8 g + k`
(`stB`). Together they transpose the 64 quadwords of every lane
(`stB_stA`, `transpose_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.StraightY VG.X86_64.RegUpd VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceAvx2
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The state words. -/
def stateCfg : Cfg := { base := .rsi, slots := 64 }

/-- State word `j`. -/
def words (s : State) (j : Nat) : BitVec 256 := s.mem.readW (yAddr (s.gpr .rsi) j) 256

/-- Quadword lane `q` of the state words. -/
def laneW (s : State) (q : Nat) : Nat → BitVec 64 := fun j => qw (words s j) q

/-- The state words' area. -/
def stateR (s : State) : Region := ⟨s.gpr .rsi, 2048⟩

/-- Quadword lane `q` of the 32-byte words at `D`. -/
def laneAt (m : Mem) (D : Addr) (q j : Nat) : BitVec 64 := qw (m.readW (yAddr D j) 256) q

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
slot `j`, for the `n` slots at `rsi`. -/
theorem group_run {n K : Nat} {is : List Instr} {g : Nat → Nat → Nat} {s : State}
    (hn : 64 * n ≤ 2 ^ K) (hg : ∀ j < n, ∀ p < 64, g j p < 64 * n)
    (hchk : check (lanes 64 K) ⟨.rsi, n⟩ is (envIn n) (postOut n g) = true)
    (hok : Ok ⟨.rsi, n⟩ s) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ q < 4, ∀ j < n, ∀ p < 64, (laneAt s'.mem (s.gpr .rsi) q j).getLsbD p =
        (laneAt s.mem (s.gpr .rsi) q (g j p / 64)).getLsbD (g j p % 64)) ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨s.gpr .rsi, 32 * n⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  have hrel : Rel (fun q => LaneRel K (assign (laneW s q) (2 ^ K))) ⟨.rsi, n⟩ (envIn n) s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl q hq => ?_), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
    have hj' : j < n := hj
    simp only [envIn, hj', ↓reduceIte, Option.some.injEq] at hsl
    subst hsl
    exact inWord_rel (laneW s q) (by omega)
  obtain ⟨s', hs', p⟩ := run (fun _ _ => lanes_sound) hok hrel he
  refine ⟨s', hs', fun q hq j hj b hb => ?_, fun r hr => p.gpr r (by simp [hr]), p.rd, p.wr, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot j _ hj (beq_iff_eq.mp hpj) q hq
  have bits := outWord_rel (fun p hp a ha => by
    simp only [List.mem_singleton] at ha; subst ha; have := hg j hj p hp; omega) hs
  have hb' : s'.gpr .rsi = s.gpr .rsi := p.base
  have hsj : laneAt s'.mem (s.gpr .rsi) q j =
      qw (s'.mem.readW (yAddr (s'.gpr (⟨.rsi, n⟩ : Cfg).base) j) 256) q := by
    show _ = qw (s'.mem.readW (yAddr (s'.gpr .rsi) j) 256) q
    rw [hb']; rfl
  rw [hsj, bits b hb]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false]
  rfl

/-- A group of the first stage: the words `8 k` from `rsi` of the 57 words. -/
def bodyA : List Instr := masks 8 ++ group (fun k => 8 * k) 8

/-- A group of the second stage: the eight words from `rsi`. -/
def bodyB : List Instr := masks 1 ++ group (fun k => k) 1

def gA (j p : Nat) : Nat :=
  if j % 8 = 0 then 64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j / 8) <<< 3)) else 64 * j + p

def gB (j p : Nat) : Nat := 64 * (p &&& 7) + ((p &&& 56) ||| j)

theorem bodyA_check : check (lanes 64 12) ⟨.rsi, 57⟩ bodyA (envIn 57) (postOut 57 gA) = true := by
  decide +kernel

theorem bodyB_check : check (lanes 64 9) ⟨.rsi, 8⟩ bodyB (envIn 8) (postOut 8 gB) = true := by
  decide +kernel

theorem gA_lt : ∀ j < 57, ∀ p < 64, gA j p < 64 * 57 := by
  intro j hj p hp
  unfold gA
  split
  · have h1 : (p >>> 3) &&& 7 ≤ 7 := Nat.and_le_right
    have h2 : ((p &&& 7) ||| ((j / 8) <<< 3)) < 2 ^ 6 :=
      Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) (by rw [Nat.shiftLeft_eq]; omega)
    omega
  · omega

theorem gB_lt : ∀ j < 8, ∀ p < 64, gB j p < 64 * 8 := by decide +kernel

theorem bodyA_nogpr : bodyA.all (fun op => op.dst == none || op.dst == some .rbx) = true := by
  decide +kernel

theorem bodyB_nogpr : bodyB.all (fun op => op.dst == none || op.dst == some .rbx) = true := by
  decide +kernel

theorem keeps_of_nogpr {is : List Instr} (h : is.all (fun op => op.dst == none || op.dst == some .rbx) = true)
    {r : Reg} (hr : r ≠ .rbx) : (is.all fun i => i.dst != some r) = true := by
  rw [List.all_eq_true] at h ⊢
  intro op hop
  have := h op hop
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h0 | h0
  · simp [h0]
  · simp only [h0, bne_iff_ne, ne_eq, Option.some.injEq]; exact fun h => hr h.symm

/-! ## Where a group is, in the state -/

theorem yAddr_add (D : Addr) (a k : Nat) : yAddr (yAddr D a) k = yAddr D (a + k) := by
  simp only [yAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

/-- The slots of a group, within the state's. -/
theorem ok_window {s₀ s : State} {D : Addr} (h₀ : Ok stateCfg s₀) (hD : s₀.gpr .rsi = D) {a n : Nat}
    (ha : a + n ≤ 64) (hb : s.gpr .rsi = yAddr D a) (hw : s.wr = s₀.wr) : Ok ⟨.rsi, n⟩ s where
  slotIn k hk := by
    have hk' : k < n := hk
    show InRegions s.wr (yAddr (s.gpr .rsi) k) 32
    rw [hb, yAddr_add, hw, ← hD]
    exact h₀.slotIn (a + k) (by show a + k < 64; omega)
  slots := by show 32 * n < 2 ^ 64; omega

/-- A word outside a group's slots is unchanged. -/
theorem lane_out {m m' : Mem} {D : Addr} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨yAddr D a, 32 * n⟩] m m') {j : Nat} (hj : j < 64) (hout : j < a ∨ a + n ≤ j) (q : Nat) :
    laneAt m' D q j = laneAt m D q j := by
  simp only [laneAt]
  rw [hf.readW (r := ⟨yAddr D j, 32⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega) (by omega) (by omega)) (by decide)]

/-- A word in a group's slots, from the group's view. -/
theorem lane_in (m : Mem) (D : Addr) (a q j : Nat) : laneAt m (yAddr D a) q j = laneAt m D q (a + j) := by
  simp only [laneAt, yAddr_add]

/-! ## The register steps -/

theorem addImm_run (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .add r (.imm v)] s = some s' ∧ s'.gpr r = s.gpr r + v.signExtend 64 ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let x := s.gpr r
  let t := x + v.signExtend 64
  refine ⟨(arithFlags s t (decide (2 ^ 64 ≤ x.toNat + (v.signExtend 64).toNat))
    (addOverflow x (v.signExtend 64) t)).setReg r t, ?_, ?_, fun r' h => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]; rfl
  · simp [gpr_setReg, h]
  · simp [mem_setReg, mem_arithFlags]
  · simp [rd_setReg, rd_arithFlags]
  · simp [wr_setReg, wr_arithFlags]

theorem subImm_run (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .sub r (.imm v)] s = some s' ∧ s'.gpr r = s.gpr r - v.signExtend 64 ∧
      s'.zf = some (s.gpr r - v.signExtend 64 == 0) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let x := s.gpr r
  let t := x - v.signExtend 64
  refine ⟨(arithFlags s t (decide (x.toNat < (v.signExtend 64).toNat))
    (subOverflow x (v.signExtend 64) t)).setReg r t, ?_, ?_, ?_, fun r' h => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]; rfl
  · simp only [zf_setReg, zf_arithFlags]; rfl
  · simp [gpr_setReg, h]
  · simp [mem_setReg, mem_arithFlags]
  · simp [rd_setReg, rd_arithFlags]
  · simp [wr_setReg, wr_arithFlags]

theorem movImm_run (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.mov r (.imm v)] s = some s' ∧ s'.gpr r = v.signExtend 64 ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg r (v.signExtend 64), ?_, ?_, fun r' h => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]
  · simp [gpr_setReg, h]
  · simp [mem_setReg]
  · simp [rd_setReg]
  · simp [wr_setReg]

theorem cnt8_sub (n : Nat) (h₁ : 1 ≤ n) :
    BitVec.ofNat 64 n - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - 1) := by
  rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h₁]

theorem cnt8_zero : ∀ n < 8, (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

/-! ## The stages -/

/-- What every step of a stage keeps, from `s₀`, with the state words at `D`. -/
structure Keep (s₀ s : State) : Prop where
  gpr : ∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stateR s₀] s₀.mem s.mem

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

/-- A group's slots are in the state words. -/
theorem frame_state {s₀ : State} {m m' : Mem} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨yAddr (s₀.gpr .rsi) a, 32 * n⟩] m m') : Frame [stateR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩

/-- A group's code, then `rsi` past it and the count down: what each keeps. -/
theorem group_step {s : State} {body : List Instr} {step : BitVec 32} {Q : State → Prop}
    {s₁ : State} (run₁ : runBlock isa body s = some s₁) (hk₁ : ∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r)
    (hQ : ∀ s₃ : State, s₃.mem = s₁.mem → s₃.rd = s₁.rd → s₃.wr = s₁.wr →
      s₃.gpr .rsi = s.gpr .rsi + step.signExtend 64 → s₃.gpr .r11 = s.gpr .r11 - 1 →
      s₃.zf = some (s.gpr .r11 - 1 == 0) → (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .r11 → s₃.gpr r = s.gpr r) →
      Q s₃) :
    WP isa (.block (body ++ ([.alu .add .rsi (.imm step), .alu .sub .r11 (.imm 1)] : List Instr))) s Q := by
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [show ([.alu .add .rsi (.imm step), .alu .sub .r11 (.imm 1)] : List Instr) =
    [.alu .add .rsi (.imm step)] ++ [.alu .sub .r11 (.imm 1)] from rfl, WP.block_append_iff]
  obtain ⟨s₂, run₂, si₂, g₂, m₂, rd₂, wr₂⟩ := addImm_run s₁ .rsi step
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, c₃, z₃, g₃, m₃, rd₃, wr₃⟩ := subImm_run s₂ .r11 1
  refine WP.of_runBlock ⟨s₃, run₃, hQ s₃ (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂) ?_ ?_ ?_ ?_⟩
  · rw [g₃ _ (by decide), si₂, hk₁ _ (by decide)]
  · rw [c₃, g₂ _ (by decide), hk₁ _ (by decide)]; rfl
  · rw [z₃, g₂ _ (by decide), hk₁ _ (by decide)]; rfl
  · intro r a b c; rw [g₃ r c, g₂ r b, hk₁ r a]

theorem yAddr_succ (D : Addr) (i : Nat) (k : Nat) :
    yAddr D i + BitVec.ofNat 64 (32 * k) = yAddr D (i + k) := by
  simp only [yAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

/-- After the groups below `8 - n` of the first stage. -/
structure InvA (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  pos : 1 ≤ n
  le : n ≤ 8
  rsi : s.gpr .rsi = yAddr (s₀.gpr .rsi) (8 - n)
  r11 : s.gpr .r11 = BitVec.ofNat 64 n
  lanes : ∀ q < 4, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j =
    if j % 8 < 8 - n then stA (laneW s₀ q) j else laneW s₀ q j

/-- The first stage, done. -/
structure DoneA (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  rsi : s.gpr .rsi = yAddr (s₀.gpr .rsi) 8
  lanes : ∀ q < 4, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j = stA (laneW s₀ q) j

theorem gA_idx : ∀ k < 8, ∀ p < 64, ((p &&& 7) ||| (k <<< 3)) < 64 ∧ ((p >>> 3) &&& 7) < 8 := by
  decide +kernel

theorem gB_idx : ∀ k < 8, ∀ p < 64, ((p &&& 56) ||| k) < 64 ∧ (p &&& 7) < 8 := by
  decide +kernel

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

theorem stageA_step {s₀ : State} (h₀ : Ok stateCfg s₀) {n : Nat} {s : State} (hs : InvA s₀ n s) :
    WP isa (.block (stageBody (fun k => 8 * k) 8 32)) s fun s' =>
      (isa.eval .ne s' = some false ∧ DoneA s₀ s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, InvA s₀ m s') := by
  let D := s₀.gpr .rsi
  have hn₁ := hs.pos
  have hn₂ := hs.le
  have hok := ok_window (a := 8 - n) (n := 57) h₀ rfl (by omega) hs.rsi hs.keep.wr
  obtain ⟨s₁, run₁, l₁, k₁, rd₁, wr₁, f₁⟩ := group_run (by decide) gA_lt bodyA_check hok
  rw [show stageBody (fun k => 8 * k) 8 32 =
    bodyA ++ ([.alu .add .rsi (.imm ((32 : Nat) : BitVec 32)), .alu .sub .r11 (.imm 1)] : List Instr) by
      simp only [stageBody, bodyA, List.append_assoc]]
  refine group_step run₁ (fun r hr => k₁ r (keeps_of_nogpr bodyA_nogpr hr))
    fun s₃ m₃ rd₃ wr₃ si₃ c₃ z₃ g₃ => ?_
  rw [hs.rsi] at f₁ l₁
  -- the lanes after this group
  have lanes₃ : ∀ q < 4, ∀ j < 64, laneAt s₃.mem D q j =
      if j % 8 < 8 - n + 1 then stA (laneW s₀ q) j else laneW s₀ q j := by
    intro q hq j hj
    rw [m₃]
    by_cases hw : 8 - n ≤ j ∧ j < 8 - n + 57
    · obtain ⟨j', rfl⟩ : ∃ j', j = 8 - n + j' := ⟨j - (8 - n), by omega⟩
      have hj' : j' < 57 := by omega
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [← lane_in, l₁ q hq j' hj' p hp, lane_in]
      by_cases h8 : j' % 8 = 0
      · obtain ⟨e₁, e₂⟩ := gA_idx (j' / 8) (by omega) p hp
        have eg : gA j' p = 64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j' / 8) <<< 3)) := by
          simp only [gA, h8, ↓reduceIte]
        rw [eg, show (64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j' / 8) <<< 3))) / 64 =
            8 * ((p >>> 3) &&& 7) by omega,
          show (64 * (8 * ((p >>> 3) &&& 7)) + ((p &&& 7) ||| ((j' / 8) <<< 3))) % 64 =
            ((p &&& 7) ||| ((j' / 8) <<< 3)) by omega,
          hs.lanes q hq _ (by omega)]
        have c₁ : ¬ (8 - n + 8 * ((p >>> 3) &&& 7)) % 8 < 8 - n := by omega
        have c₂ : (8 - n + j') % 8 < 8 - n + 1 := by omega
        simp only [c₁, c₂, ↓reduceIte, stA, getLsbD_ofBits, hp, decide_true, Bool.true_and]
        rw [show (8 - n + j') % 8 = 8 - n by omega, show (8 - n + j') / 8 = j' / 8 by omega]
      · have eg : gA j' p = 64 * j' + p := by simp only [gA, h8, ↓reduceIte]
        rw [eg, show (64 * j' + p) / 64 = j' by omega, show (64 * j' + p) % 64 = p by omega,
          hs.lanes q hq _ hj]
        have : ((8 - n + j') % 8 < 8 - n) = ((8 - n + j') % 8 < 8 - n + 1) := by
          apply propext; constructor <;> intro h <;> omega
        simp only [this]
    · rw [lane_out (by omega) f₁ hj (by omega) q, hs.lanes q hq j hj]
      have : (j % 8 < 8 - n) = (j % 8 < 8 - n + 1) := by
        apply propext; constructor <;> intro h <;> omega
      simp only [this]
  have keep₃ : Keep s₀ s₃ :=
    ⟨fun r a b c => (g₃ r a b c).trans (hs.keep.gpr r a b c), rd₃.trans (rd₁.trans hs.keep.rd),
      wr₃.trans (wr₁.trans hs.keep.wr), hs.keep.frame.trans (m₃ ▸ frame_state (by omega) f₁)⟩
  have rsi₃ : s₃.gpr .rsi = yAddr D (8 - n + 1) := by
    rw [si₃, hs.rsi, show (((32 : Nat) : BitVec 32)).signExtend 64 = BitVec.ofNat 64 (32 * 1) from rfl]
    exact yAddr_succ D (8 - n) 1
  have cnt : s.gpr .r11 - 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.r11]; exact cnt8_sub n hn₁
  rw [eval_ne, z₃, cnt, cnt8_zero (n - 1) (by omega)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, rsi₃, fun q hq j hj => ?_⟩
    have c : j % 8 < 8 - 1 + 1 := by omega
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp only [Option.map_some]; simp; omega, n - 1, by omega, keep₃, by omega, by omega,
      by rw [rsi₃]; congr 1; omega, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega]

/-- Before the second stage: the first done, `rsi` back at the state words. -/
structure PreB (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  rsi : s.gpr .rsi = s₀.gpr .rsi
  lanes : ∀ q < 4, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j = stA (laneW s₀ q) j

/-- After the groups below `8 - n` of the second stage. -/
structure InvB (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  pos : 1 ≤ n
  le : n ≤ 8
  rsi : s.gpr .rsi = yAddr (s₀.gpr .rsi) (8 * (8 - n))
  r11 : s.gpr .r11 = BitVec.ofNat 64 n
  lanes : ∀ q < 4, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j =
    if j / 8 < 8 - n then stB (stA (laneW s₀ q)) j else stA (laneW s₀ q) j

/-- The second stage, done. -/
structure DoneB (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  rsi : s.gpr .rsi = yAddr (s₀.gpr .rsi) 64
  lanes : ∀ q < 4, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j = stB (stA (laneW s₀ q)) j

theorem stageB_step {s₀ : State} (h₀ : Ok stateCfg s₀) {n : Nat} {s : State} (hs : InvB s₀ n s) :
    WP isa (.block (stageBody (fun k => k) 1 256)) s fun s' =>
      (isa.eval .ne s' = some false ∧ DoneB s₀ s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, InvB s₀ m s') := by
  let D := s₀.gpr .rsi
  have hn₁ := hs.pos
  have hn₂ := hs.le
  have hok := ok_window (a := 8 * (8 - n)) (n := 8) h₀ rfl (by omega) hs.rsi hs.keep.wr
  obtain ⟨s₁, run₁, l₁, k₁, rd₁, wr₁, f₁⟩ := group_run (by decide) gB_lt bodyB_check hok
  rw [show stageBody (fun k => k) 1 256 =
    bodyB ++ ([.alu .add .rsi (.imm ((256 : Nat) : BitVec 32)), .alu .sub .r11 (.imm 1)] : List Instr) by
      simp only [stageBody, bodyB, List.append_assoc]]
  refine group_step run₁ (fun r hr => k₁ r (keeps_of_nogpr bodyB_nogpr hr))
    fun s₃ m₃ rd₃ wr₃ si₃ c₃ z₃ g₃ => ?_
  rw [hs.rsi] at f₁ l₁
  have lanes₃ : ∀ q < 4, ∀ j < 64, laneAt s₃.mem D q j =
      if j / 8 < 8 - n + 1 then stB (stA (laneW s₀ q)) j else stA (laneW s₀ q) j := by
    intro q hq j hj
    rw [m₃]
    by_cases hw : 8 * (8 - n) ≤ j ∧ j < 8 * (8 - n) + 8
    · obtain ⟨j', rfl⟩ : ∃ j', j = 8 * (8 - n) + j' := ⟨j - 8 * (8 - n), by omega⟩
      have hj' : j' < 8 := by omega
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [← lane_in, l₁ q hq j' hj' p hp, lane_in]
      obtain ⟨e₁, e₂⟩ := gB_idx j' hj' p hp
      rw [show gB j' p / 64 = p &&& 7 by simp only [gB]; omega,
        show gB j' p % 64 = (p &&& 56) ||| j' by simp only [gB]; omega,
        hs.lanes q hq _ (by omega)]
      have c₁ : ¬ (8 * (8 - n) + (p &&& 7)) / 8 < 8 - n := by omega
      have c₂ : (8 * (8 - n) + j') / 8 < 8 - n + 1 := by omega
      simp only [c₁, c₂, ↓reduceIte, stB, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      rw [show (8 * (8 - n) + j') / 8 = 8 - n by omega, show (8 * (8 - n) + j') % 8 = j' by omega]
    · rw [lane_out (by omega) f₁ hj (by omega) q, hs.lanes q hq j hj]
      have : (j / 8 < 8 - n) = (j / 8 < 8 - n + 1) := by
        apply propext; constructor <;> intro h <;> omega
      simp only [this]
  have keep₃ : Keep s₀ s₃ :=
    ⟨fun r a b c => (g₃ r a b c).trans (hs.keep.gpr r a b c), rd₃.trans (rd₁.trans hs.keep.rd),
      wr₃.trans (wr₁.trans hs.keep.wr), hs.keep.frame.trans (m₃ ▸ frame_state (by omega) f₁)⟩
  have rsi₃ : s₃.gpr .rsi = yAddr D (8 * (8 - n) + 8) := by
    rw [si₃, hs.rsi, show (((256 : Nat) : BitVec 32)).signExtend 64 = BitVec.ofNat 64 (32 * 8) from rfl]
    exact yAddr_succ D (8 * (8 - n)) 8
  have cnt : s.gpr .r11 - 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.r11]; exact cnt8_sub n hn₁
  rw [eval_ne, z₃, cnt, cnt8_zero (n - 1) (by omega)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, by rw [rsi₃], fun q hq j hj => ?_⟩
    have c : j / 8 < 8 - 1 + 1 := by omega
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp only [Option.map_some]; simp; omega, n - 1, by omega, keep₃, by omega, by omega,
      by rw [rsi₃]; congr 1; omega, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega]

theorem yAddr_zero (D : Addr) : yAddr D 0 = D := by simp [yAddr]

theorem stageA_ok {s₀ : State} (h₀ : Ok stateCfg s₀) :
    WP isa (stage (fun k => 8 * k) 8 32) s₀ (DoneA s₀) := by
  obtain ⟨s₁, run₁, c₁, g₁, m₁, rd₁, wr₁⟩ := movImm_run s₀ .r11 8
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (InvA s₀) (fun n s hs => stageA_step h₀ hs) 8 s₁
    ⟨⟨fun r _ _ c => g₁ r c, rd₁, wr₁, m₁ ▸ Frame.refl _ _⟩, by decide, by decide,
      by rw [g₁ _ (by decide), Nat.sub_self, yAddr_zero], by rw [c₁]; rfl, fun q _ j _ => ?_⟩
  simp only [laneAt, m₁]; rfl

theorem stageB_ok {s₀ s : State} (h₀ : Ok stateCfg s₀) (hs : PreB s₀ s) :
    WP isa (stage (fun k => k) 1 256) s (DoneB s₀) := by
  obtain ⟨s₁, run₁, c₁, g₁, m₁, rd₁, wr₁⟩ := movImm_run s .r11 8
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (InvB s₀) (fun n s hs => stageB_step h₀ hs) 8 s₁
    ⟨⟨fun r a b c => (g₁ r c).trans (hs.keep.gpr r a b c), rd₁.trans hs.keep.rd, wr₁.trans hs.keep.wr,
      m₁ ▸ hs.keep.frame⟩, by decide, by decide,
      by rw [g₁ _ (by decide), hs.rsi, Nat.sub_self, Nat.mul_zero, yAddr_zero], by rw [c₁]; rfl,
      fun q hq j hj => ?_⟩
  simp only [m₁]
  exact hs.lanes q hq j hj

/-- Each quadword lane of the state words, transposed. Only `rbx` (the masks'
constants), `r11` (the count of groups) and vector registers change, and in
memory only the state words. -/
theorem transpose_ok {s : State} (hok : Ok stateCfg s) :
    WP isa transpose s fun s' => (∀ q < 4, ∀ j < 64, laneW s' q j = transposeW (laneW s q) j) ∧
      (∀ r, r ≠ .rbx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  let D := s.gpr .rsi
  refine WP.seq (WP.mono (stageA_ok hok) fun sA hA => ?_)
  obtain ⟨s₂, run₂, si₂, -, g₂, m₂, rd₂, wr₂⟩ := subImm_run sA .rsi 256
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have pre : PreB s s₂ :=
    ⟨⟨fun r a b c => (g₂ r b).trans (hA.keep.gpr r a b c), rd₂.trans hA.keep.rd, wr₂.trans hA.keep.wr,
      m₂ ▸ hA.keep.frame⟩,
      by rw [si₂, hA.rsi]; simp only [yAddr]; rw [show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (32 * 8)
        from rfl, BitVec.add_sub_cancel],
      fun q hq j hj => by rw [m₂]; exact hA.lanes q hq j hj⟩
  refine WP.seq (WP.mono (stageB_ok hok pre) fun sB hB => ?_)
  obtain ⟨s₄, run₄, si₄, -, g₄, m₄, rd₄, wr₄⟩ := subImm_run sB .rsi 2048
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have rsi₄ : s₄.gpr .rsi = D := by
    rw [si₄, hB.rsi]; simp only [yAddr]
    rw [show (2048 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (32 * 64) from rfl, BitVec.add_sub_cancel]
  refine ⟨fun q hq j hj => ?_, fun r a b => ?_, rd₄.trans hB.keep.rd, wr₄.trans hB.keep.wr,
    m₄ ▸ hB.keep.frame⟩
  · show laneAt s₄.mem (s₄.gpr .rsi) q j = _
    rw [rsi₄, m₄, hB.lanes q hq j hj, stB_stA _ hj]
  · by_cases hr : r = .rsi
    · subst hr; exact rsi₄
    · rw [g₄ r hr]; exact hB.keep.gpr r a hr b

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
