module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.TripleDes.Bitslice.TransposeIdx
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx512
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.SboxLit
public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.TripleDes.Bitslice.OutIdx
import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `TripleDes.X86_64.BitslicedAvx512.Step`, which only this module used -/

section

/-! ### `TripleDes.X86_64.BitslicedAvx512.Machine`, which only this module used -/

section

/-! ### `TripleDes.X86_64.BitslicedAvx512.Transpose`, which only this module used -/

section

/-!
# The transposition of the AVX-512 state

The 64 state words are the 64-byte slots at `rsi`. The transposition runs
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

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The state words. -/
def stateCfg : Cfg := { base := .rsi, slots := 64 }

/-- State word `j`. -/
def words (s : State) (j : Nat) : BitVec 512 := s.mem.readW (zAddr (s.gpr .rsi) j) 512

/-- Quadword lane `q` of the state words. -/
def laneW (s : State) (q : Nat) : Nat → BitVec 64 := fun j => qw (words s j) q

/-- The state words' area. -/
def stateR (s : State) : Region := ⟨s.gpr .rsi, 4096⟩

/-- Quadword lane `q` of the 64-byte words at `D`. -/
def laneAt (m : Mem) (D : Addr) (q j : Nat) : BitVec 64 := qw (m.readW (zAddr D j) 512) q

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
      (∀ q < 8, ∀ j < n, ∀ p < 64, (laneAt s'.mem (s.gpr .rsi) q j).getLsbD p =
        (laneAt s.mem (s.gpr .rsi) q (g j p / 64)).getLsbD (g j p % 64)) ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨s.gpr .rsi, 64 * n⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  have hrel : Rel (fun q => LaneRel K (assign (laneW s q) (2 ^ K))) ⟨.rsi, n⟩ (envIn n) s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl q hq => ?_), (fun _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
    have hj' : j < n := hj
    simp only [envIn, hj', ↓reduceIte, Option.some.injEq] at hsl
    subst hsl
    exact inWord_rel (laneW s q) (by omega_arith)
  obtain ⟨s', hs', p⟩ := run (fun _ _ => lanes_sound) hok hrel he
  refine ⟨s', hs', fun q hq j hj b hb => ?_, fun r hr => p.gpr r (by simp [hr]), p.rd, p.wr, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot j _ hj (beq_iff_eq.mp hpj) q hq
  have bits := outWord_rel (fun p hp a ha => by
    simp only [List.mem_singleton] at ha; subst ha; have := hg j hj p hp; omega_arith) hs
  have hb' : s'.gpr .rsi = s.gpr .rsi := p.base
  have hsj : laneAt s'.mem (s.gpr .rsi) q j =
      qw (s'.mem.readW (zAddr (s'.gpr (⟨.rsi, n⟩ : Cfg).base) j) 512) q := by
    show _ = qw (s'.mem.readW (zAddr (s'.gpr .rsi) j) 512) q
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
      Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) (by rw [Nat.shiftLeft_eq]; omega_arith)
    omega_arith
  · omega_arith

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

theorem zAddr_add (D : Addr) (a k : Nat) : zAddr (zAddr D a) k = zAddr D (a + k) := by
  simp only [zAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

/-- The slots of a group, within the state's. -/
theorem ok_window {s₀ s : State} {D : Addr} (h₀ : Ok stateCfg s₀) (hD : s₀.gpr .rsi = D) {a n : Nat}
    (ha : a + n ≤ 64) (hb : s.gpr .rsi = zAddr D a) (hw : s.wr = s₀.wr) : Ok ⟨.rsi, n⟩ s where
  slotIn k hk := by
    have hk' : k < n := hk
    show InRegions s.wr (zAddr (s.gpr .rsi) k) 64
    rw [hb, zAddr_add, hw, ← hD]
    exact h₀.slotIn (a + k) (by show a + k < 64; omega_arith)
  slots := by show 64 * n < 2 ^ 64; omega_arith

/-- A word outside a group's slots is unchanged. -/
theorem lane_out {m m' : Mem} {D : Addr} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨zAddr D a, 64 * n⟩] m m') {j : Nat} (hj : j < 64) (hout : j < a ∨ a + n ≤ j) (q : Nat) :
    laneAt m' D q j = laneAt m D q j := by
  simp only [laneAt]
  rw [hf.readW (r := ⟨zAddr D j, 64⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]

/-- A word in a group's slots, from the group's view. -/
theorem lane_in (m : Mem) (D : Addr) (a q j : Nat) : laneAt m (zAddr D a) q j = laneAt m D q (a + j) := by
  simp only [laneAt, zAddr_add]

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

/-- A group's slots are in the state words. -/
theorem frame_state {s₀ : State} {m m' : Mem} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨zAddr (s₀.gpr .rsi) a, 64 * n⟩] m m') : Frame [stateR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_arith)⟩

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

theorem zAddr_succ (D : Addr) (i : Nat) (k : Nat) :
    zAddr D i + BitVec.ofNat 64 (64 * k) = zAddr D (i + k) := by
  simp only [zAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_add]

/-- After the groups below `8 - n` of the first stage. -/
structure InvA (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  pos : 1 ≤ n
  le : n ≤ 8
  rsi : s.gpr .rsi = zAddr (s₀.gpr .rsi) (8 - n)
  r11 : s.gpr .r11 = BitVec.ofNat 64 n
  lanes : ∀ q < 8, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j =
    if j % 8 < 8 - n then stA (laneW s₀ q) j else laneW s₀ q j

/-- The first stage, done. -/
structure DoneA (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  rsi : s.gpr .rsi = zAddr (s₀.gpr .rsi) 8
  lanes : ∀ q < 8, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j = stA (laneW s₀ q) j

theorem gA_idx : ∀ k < 8, ∀ p < 64, ((p &&& 7) ||| (k <<< 3)) < 64 ∧ ((p >>> 3) &&& 7) < 8 := by
  decide +kernel

theorem gB_idx : ∀ k < 8, ∀ p < 64, ((p &&& 56) ||| k) < 64 ∧ (p &&& 7) < 8 := by
  decide +kernel

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

theorem stageA_step {s₀ : State} (h₀ : Ok stateCfg s₀) {n : Nat} {s : State} (hs : InvA s₀ n s) :
    WP isa (.block (stageBody (fun k => 8 * k) 8 64)) s fun s' =>
      (isa.eval .ne s' = some false ∧ DoneA s₀ s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, InvA s₀ m s') := by
  let D := s₀.gpr .rsi
  have hn₁ := hs.pos
  have hn₂ := hs.le
  have hok := ok_window (a := 8 - n) (n := 57) h₀ rfl (by omega_arith) hs.rsi hs.keep.wr
  obtain ⟨s₁, run₁, l₁, k₁, rd₁, wr₁, f₁⟩ := group_run (by decide) gA_lt bodyA_check hok
  rw [show stageBody (fun k => 8 * k) 8 64 =
    bodyA ++ ([.alu .add .rsi (.imm ((64 : Nat) : BitVec 32)), .alu .sub .r11 (.imm 1)] : List Instr) by
      simp only [stageBody, bodyA, List.append_assoc]]
  refine group_step run₁ (fun r hr => k₁ r (keeps_of_nogpr bodyA_nogpr hr))
    fun s₃ m₃ rd₃ wr₃ si₃ c₃ z₃ g₃ => ?_
  rw [hs.rsi] at f₁ l₁
  -- the lanes after this group
  have lanes₃ : ∀ q < 8, ∀ j < 64, laneAt s₃.mem D q j =
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
      wr₃.trans (wr₁.trans hs.keep.wr), hs.keep.frame.trans (m₃ ▸ frame_state (by omega_arith) f₁)⟩
  have rsi₃ : s₃.gpr .rsi = zAddr D (8 - n + 1) := by
    rw [si₃, hs.rsi, show (((64 : Nat) : BitVec 32)).signExtend 64 = BitVec.ofNat 64 (64 * 1) from rfl]
    exact zAddr_succ D (8 - n) 1
  have cnt : s.gpr .r11 - 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.r11]; exact cnt8_sub n hn₁
  rw [eval_ne, z₃, cnt, cnt8_zero (n - 1) (by omega_arith)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, rsi₃, fun q hq j hj => ?_⟩
    have c : j % 8 < 8 - 1 + 1 := by omega_arith
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp only [Option.map_some]; simp; omega_arith, n - 1, by omega_arith, keep₃, by omega_arith, by omega_arith,
      by rw [rsi₃]; congr 1; omega_arith, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega_arith]

/-- Before the second stage: the first done, `rsi` back at the state words. -/
structure PreB (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  rsi : s.gpr .rsi = s₀.gpr .rsi
  lanes : ∀ q < 8, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j = stA (laneW s₀ q) j

/-- After the groups below `8 - n` of the second stage. -/
structure InvB (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  pos : 1 ≤ n
  le : n ≤ 8
  rsi : s.gpr .rsi = zAddr (s₀.gpr .rsi) (8 * (8 - n))
  r11 : s.gpr .r11 = BitVec.ofNat 64 n
  lanes : ∀ q < 8, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j =
    if j / 8 < 8 - n then stB (stA (laneW s₀ q)) j else stA (laneW s₀ q) j

/-- The second stage, done. -/
structure DoneB (s₀ : State) (s : State) : Prop where
  keep : Keep s₀ s
  rsi : s.gpr .rsi = zAddr (s₀.gpr .rsi) 64
  lanes : ∀ q < 8, ∀ j < 64, laneAt s.mem (s₀.gpr .rsi) q j = stB (stA (laneW s₀ q)) j

theorem stageB_step {s₀ : State} (h₀ : Ok stateCfg s₀) {n : Nat} {s : State} (hs : InvB s₀ n s) :
    WP isa (.block (stageBody (fun k => k) 1 512)) s fun s' =>
      (isa.eval .ne s' = some false ∧ DoneB s₀ s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, InvB s₀ m s') := by
  let D := s₀.gpr .rsi
  have hn₁ := hs.pos
  have hn₂ := hs.le
  have hok := ok_window (a := 8 * (8 - n)) (n := 8) h₀ rfl (by omega_arith) hs.rsi hs.keep.wr
  obtain ⟨s₁, run₁, l₁, k₁, rd₁, wr₁, f₁⟩ := group_run (by decide) gB_lt bodyB_check hok
  rw [show stageBody (fun k => k) 1 512 =
    bodyB ++ ([.alu .add .rsi (.imm ((512 : Nat) : BitVec 32)), .alu .sub .r11 (.imm 1)] : List Instr) by
      simp only [stageBody, bodyB, List.append_assoc]]
  refine group_step run₁ (fun r hr => k₁ r (keeps_of_nogpr bodyB_nogpr hr))
    fun s₃ m₃ rd₃ wr₃ si₃ c₃ z₃ g₃ => ?_
  rw [hs.rsi] at f₁ l₁
  have lanes₃ : ∀ q < 8, ∀ j < 64, laneAt s₃.mem D q j =
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
      wr₃.trans (wr₁.trans hs.keep.wr), hs.keep.frame.trans (m₃ ▸ frame_state (by omega_arith) f₁)⟩
  have rsi₃ : s₃.gpr .rsi = zAddr D (8 * (8 - n) + 8) := by
    rw [si₃, hs.rsi, show (((512 : Nat) : BitVec 32)).signExtend 64 = BitVec.ofNat 64 (64 * 8) from rfl]
    exact zAddr_succ D (8 * (8 - n)) 8
  have cnt : s.gpr .r11 - 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.r11]; exact cnt8_sub n hn₁
  rw [eval_ne, z₃, cnt, cnt8_zero (n - 1) (by omega_arith)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, by rw [rsi₃], fun q hq j hj => ?_⟩
    have c : j / 8 < 8 - 1 + 1 := by omega_arith
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp only [Option.map_some]; simp; omega_arith, n - 1, by omega_arith, keep₃, by omega_arith, by omega_arith,
      by rw [rsi₃]; congr 1; omega_arith, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega_arith]

theorem zAddr_zero (D : Addr) : zAddr D 0 = D := by simp [zAddr]

theorem stageA_ok {s₀ : State} (h₀ : Ok stateCfg s₀) :
    WP isa (stage (fun k => 8 * k) 8 64) s₀ (DoneA s₀) := by
  obtain ⟨s₁, run₁, c₁, g₁, m₁, rd₁, wr₁⟩ := movImm_run s₀ .r11 8
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (InvA s₀) (fun n s hs => stageA_step h₀ hs) 8 s₁
    ⟨⟨fun r _ _ c => g₁ r c, rd₁, wr₁, m₁ ▸ Frame.refl _ _⟩, by decide, by decide,
      by rw [g₁ _ (by decide), Nat.sub_self, zAddr_zero], by rw [c₁]; rfl, fun q _ j _ => ?_⟩
  simp only [laneAt, m₁]; rfl

theorem stageB_ok {s₀ s : State} (h₀ : Ok stateCfg s₀) (hs : PreB s₀ s) :
    WP isa (stage (fun k => k) 1 512) s (DoneB s₀) := by
  obtain ⟨s₁, run₁, c₁, g₁, m₁, rd₁, wr₁⟩ := movImm_run s .r11 8
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.loop (M := isa) (InvB s₀) (fun n s hs => stageB_step h₀ hs) 8 s₁
    ⟨⟨fun r a b c => (g₁ r c).trans (hs.keep.gpr r a b c), rd₁.trans hs.keep.rd, wr₁.trans hs.keep.wr,
      m₁ ▸ hs.keep.frame⟩, by decide, by decide,
      by rw [g₁ _ (by decide), hs.rsi, Nat.sub_self, Nat.mul_zero, zAddr_zero], by rw [c₁]; rfl,
      fun q hq j hj => ?_⟩
  simp only [m₁]
  exact hs.lanes q hq j hj

/-- Each quadword lane of the state words, transposed. Only `rbx` (the masks'
constants), `r11` (the count of groups) and vector registers change, and in
memory only the state words. -/
theorem transpose_ok {s : State} (hok : Ok stateCfg s) :
    WP isa transpose s fun s' => (∀ q < 8, ∀ j < 64, laneW s' q j = transposeW (laneW s q) j) ∧
      (∀ r, r ≠ .rbx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  let D := s.gpr .rsi
  refine WP.seq (WP.mono (stageA_ok hok) fun sA hA => ?_)
  obtain ⟨s₂, run₂, si₂, -, g₂, m₂, rd₂, wr₂⟩ := subImm_run sA .rsi 512
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have pre : PreB s s₂ :=
    ⟨⟨fun r a b c => (g₂ r b).trans (hA.keep.gpr r a b c), rd₂.trans hA.keep.rd, wr₂.trans hA.keep.wr,
      m₂ ▸ hA.keep.frame⟩,
      by rw [si₂, hA.rsi]; simp only [zAddr]; rw [show (512 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (64 * 8)
        from rfl, BitVec.add_sub_cancel],
      fun q hq j hj => by rw [m₂]; exact hA.lanes q hq j hj⟩
  refine WP.seq (WP.mono (stageB_ok hok pre) fun sB hB => ?_)
  obtain ⟨s₄, run₄, si₄, -, g₄, m₄, rd₄, wr₄⟩ := subImm_run sB .rsi 4096
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have rsi₄ : s₄.gpr .rsi = D := by
    rw [si₄, hB.rsi]; simp only [zAddr]
    rw [show (4096 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (64 * 64) from rfl, BitVec.add_sub_cancel]
  refine ⟨fun q hq j hj => ?_, fun r a b => ?_, rd₄.trans hB.keep.rd, wr₄.trans hB.keep.wr,
    m₄ ▸ hB.keep.frame⟩
  · show laneAt s₄.mem (s₄.gpr .rsi) q j = _
    rw [rsi₄, m₄, hB.lanes q hq j hj, stB_stA _ hj]
  · by_cases hr : r = .rsi
    · subst hr; exact rsi₄
    · rw [g₄ r hr]; exact hB.keep.gpr r a hr b

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-!
# The AVX-512 machine state of a batch

The 64 state words are the 64-byte slots at `rsi` (`words`), in a writable
region apart from the scratch buffer at `rcx`, which holds the circuits'
spills (`Room`). Code that only moves and XORs whole words (the S-box
outputs, the exchange of the halves) is checked on the variable domain,
quadword lane by quadword lane (`varsRun`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Bitslice
open VG.X86_64.StraightY (qword_xor qword_app)
open VG.Impl.TripleDes.X86_64.BitsliceAvx512

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨s.gpr .rcx, 1024⟩

/-- The circuits' spill slots, at the start of the scratch buffer. -/
def spillR (s : State) : Region := ⟨s.gpr .rcx, 512⟩

theorem spill_sub (s : State) : Region.Sub (spillR s) (scratchR s) := Region.sub_prefix (by decide)

/-- What a batch's code needs of the machine: the scratch buffer writable,
the state words writable and apart from it. -/
structure Room (s : State) : Prop where
  scratch : scratchR s ∈ s.wr
  state : Ok stateCfg s
  sep : (stateR s).Disjoint (scratchR s)

theorem Room.congr {s s' : State} (h : Room s) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hsi : s'.gpr .rsi = s.gpr .rsi) (hw : s'.wr = s.wr) : Room s' where
  scratch := by simp only [scratchR, hc, hw]; exact h.scratch
  state := h.state.congr hsi hw
  sep := by simp only [stateR, scratchR, hc, hsi]; exact h.sep

theorem runBlock_cat (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_cat, h₁, Option.bind_some, h₂]

/-! ## Quadwords -/

theorem eq_of_qw {x y : BitVec 512} (h : ∀ q < 8, qw x q = qw y q) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun z => z.getLsbD (i % 64)) (h (i / 64) (by omega_using [hi]))
  simp only [getLsbD_qw _ (Nat.mod_lt i (by decide) : i % 64 < 64), Nat.div_add_mod] at e
  exact e

theorem qw_xor (x y : BitVec 512) (q : Nat) : qw (x ^^^ y) q = qw x q ^^^ qw y q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [qw, hi]

theorem qw_zero (q : Nat) : qw 0 q = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [qw]

/-! ## Words as XORs of variables -/

/-- Slot `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List XReg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables, in quadword lane `q`. -/
def varVals (s : State) (regs : List XReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then laneW s q v else qw (s.zmm (regs.getD (v - 64) .xmm0)) q

def varN (regs : List XReg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List XReg) :
    Rel (fun q => VarRel (varVals s regs q) (varN regs)) stateCfg (varEnv regs) s where
  reg r a h q hq := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hlt])]
    simp only [varVals, show ¬ 64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h q hq := by
    have hk' : k < 64 := hk
    simp only [varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hk'])]
    simp only [varVals, hk', ite_true, laneW, words, stateCfg]
  gc _ _ h := by cases h
  xc _ _ h := by cases h

/-- Run a block that the variable domain accepts on the state words. -/
theorem varsRun {is : List Instr} (regs : List XReg) {post : Env Nat → Bool}
    (hchk : check (vars 64) stateCfg is (varEnv regs) post = true) {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (fun q => VarRel (varVals s regs q) (varN regs)) stateCfg e' s s'
        (fun r => (is.all fun i => zdst i != some r) = false)
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := run (fun q _ => vars_sound _ _) h.state (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

/-! ## Words above another register -/

/-- The 32-byte words above register `b`. -/
def wordsB (b : Reg) (s : State) (j : Nat) : BitVec 512 := s.mem.readW (zAddr (s.gpr b) j) 512

/-- The values of the variables, the slots above `b`. -/
def varValsB (b : Reg) (s : State) (regs : List XReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then qw (wordsB b s v) q else qw (s.zmm (regs.getD (v - 64) .xmm0)) q

theorem varEnv_relB (b : Reg) {n : Nat} (hn : n ≤ 64) {s : State} (regs : List XReg) :
    Rel (fun q => VarRel (varValsB b s regs q) (varN regs)) ⟨b, n⟩ (varEnv regs) s where
  reg r a h q hq := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hlt])]
    simp only [varValsB, show ¬ 64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h q hq := by
    have hk' : k < 64 := Nat.lt_of_lt_of_le hk hn
    simp only [varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hk'])]
    simp only [varValsB, hk', ite_true, wordsB]
  gc _ _ h := by cases h
  xc _ _ h := by cases h

/-- Run a block that the variable domain accepts on the words above `b`. -/
theorem varsRunB {is : List Instr} (regs : List XReg) {post : Env Nat → Bool} (b : Reg) {n : Nat}
    (hn : n ≤ 64) (hchk : check (vars 64) ⟨b, n⟩ is (varEnv regs) post = true) {s : State}
    (h : Ok ⟨b, n⟩ s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (fun q => VarRel (varValsB b s regs q) (varN regs)) ⟨b, n⟩ e' s s'
        (fun r => (is.all fun i => zdst i != some r) = false)
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := run (fun q _ => vars_sound _ _) h (varEnv_relB b hn regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-! ## Instructions on whole registers -/

theorem zmm_vpxord (s : State) (d a b : XReg) :
    ((ZOp.zbin .vpxord d a b).exec s).zmm d = s.zmm a ^^^ s.zmm b := by
  apply eq_of_qw; intro q hq
  rw [qw_zmm _ _ hq, zlane_zbin _ _ _ _ _ _ (by omega_using [hq]), qw_xor, qw_zmm _ _ hq, qw_zmm _ _ hq]
  simp only [ite_true, ZBinOp.sse, XBinOp.eval, qword_xor]

/-- The all-zero or all-one quadword. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- The all-zero or all-one word. -/
def maskZ (b : Bool) : BitVec 512 := if b then BitVec.allOnes 512 else 0

theorem getLsbD_maskZ (b : Bool) {P : Nat} (hP : P < 512) : (maskZ b).getLsbD P = b := by
  cases b
  · simp [maskZ]
  · simp only [maskZ, ite_true, BitVec.getLsbD_allOnes, hP, decide_true]

/-- `vmovq x, r` then `vpbroadcastq x, x` of a mask. -/
theorem bcast_mask (s : State) (x : XReg) (r : Reg) (b : Bool) (hr : s.gpr r = maskVal b) :
    ((ZOp.vpbroadcastq x x).exec ((VOp.vmovq x r).exec s)).zmm x = maskZ b := by
  apply eq_of_qw; intro q hq
  rw [qw_zmm _ _ hq, zlane_vpbroadcastq _ _ _ _ (by omega_using [hq])]
  simp only [ite_true, VOp.exec, State.setV, hr]
  rw [qword_app _ _ (Nat.mod_lt _ (by decide)), qword_app _ _ (by decide)]
  have e : qw (maskZ b) q = maskVal b := by
    cases b
    · simp only [maskVal, maskZ, Bool.false_eq_true, ite_false, qw_zero]
    · simp only [maskVal, maskZ, ite_true]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [getLsbD_qw _ hi]
      simp only [BitVec.getLsbD_allOnes, hi, show 64 * q + i < 512 by omega_using [hq, hi], decide_true]
  rw [e]
  split <;> rfl

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end

/-! ### `TripleDes.X86_64.BitslicedAvx512.Sbox`, which only this module used -/

section

/-!
# The AVX-512 S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs once,
and the quadword-lane evaluator (`StraightZ`) with the truth-table domain
lifts that check to every bit position of every quadword of arbitrary
512-bit words. The circuits spill to the scratch buffer (`[rcx + 64k]`,
`k < spills`) and write no general-purpose register.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.Bitslice VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

def sboxCfg : Cfg := { base := .rcx, slots := spills }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    check (table 64 64) sboxCfg (instrs (sboxLiteral j)) sboxEnv (sboxPost j) = true := by
  lit_decide

theorem sboxLiteral_eq : ∀ j < 8, sboxLiteral j = .block (sboxCode j)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

theorem sbox_preserves : ∀ j < 8,
    (instrs (sboxLiteral j)).all (fun op => op.dst == none) = true := by
  lit_decide

/-- Bit `P` of each input register, as the S-box's input. -/
def inputAt (s : State) (P : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.zmm (inReg i)).getLsbD P

theorem inputAt_bit (s : State) (P k : Nat) (hk : k < 6) :
    (inputAt s P).toNat.testBit k = (s.zmm (inReg k)).getLsbD P := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

/-- Every S-box output bit, for arbitrary input words and spill slots. Only
the spill slots change in memory, and no general-purpose register or flag
changes. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ P < 512, (s'.zmm (outReg i)).getLsbD P =
        (Spec.TripleDes.sBox j (inputAt s P)).getLsbD i) ∧
      s'.gpr = s.gpr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (fun q => TableRel p (inputAt s (64 * q + p)).toNat) sboxCfg e' s s'
        (fun r => ((sboxCode j).all fun op => zdst op != some r) = false)
        (fun r => ((sboxCode j).all fun op => op.dst != some r) = false) := by
    intro p hp
    refine run (fun q _ => table_sound hp (inputAt s (64 * q + p)).isLt) hok
      ⟨fun r a h q hq => ?_, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
        (fun _ _ h => by cases h)⟩ he
    have hc := (inputAt s (64 * q + p)).isLt
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      inputAt_bit s _ k hk6, getLsbD_qw _ hp]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  have pres := sbox_preserves j hj
  rw [codeEq] at pres
  have pres' := List.all_eq_true.mp pres
  refine ⟨s', hs', fun i hi P hP => ?_, funext fun r => p₀.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h
      have := pres' op hop
      simp [h] at this),
    p₀.cf, p₀.zf, p₀.rd, p₀.wr, p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key (P % 64) (Nat.mod_lt _ (by decide))
  obtain rfl := Straight.run_unique hs'' hs'
  have h := p₁.rel.reg (outReg i) _ (hout i hi) (P / 64) (by omega_using [hP])
  have eP : 64 * (P / 64) + P % 64 = P := Nat.div_add_mod P 64
  simp only [TableRel, outputTable, testBit_tableOf, (inputAt s _).isLt,
    decide_true, Bool.true_and, eP, getLsbD_qw _ (Nat.mod_lt _ (by decide) : P % 64 < 64)] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end


/-!
# One S-box of an AVX-512 round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the next six key bits of
`rax` as masks, broadcast and XORed with the words of `E`; its circuit;
XORing its outputs into their words) does to the state words what `step`
does, given the key bits at the top of `rax`, and shifts them out.
`swapHalves_ok`: the exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.X86_64.BitsliceAvx512 VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW rdOff wrOff readWord_off
  writeWord_off eBit_lt outBit_lt)

theorem add_self_eq (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega_arith

theorem add_self_carry (a : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + a.toNat) = a.msb := by
  rw [BitVec.msb_eq_decide]
  have := a.isLt
  simp only [Nat.add_one_sub_one]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega_arith

theorem sbb_self (a : BitVec 64) (c : Bool) : a - a - (BitVec.ofBool c).setWidth 64 = maskVal c := by
  cases c <;> simp [maskVal]

theorem msb_shiftLeft (R : BitVec 64) {n : Nat} (hn : n < 64) : (R <<< n).msb = R.getLsbD (63 - n) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have : ¬ 63 < n := by omega_arith
  simp [this, show (63 : Nat) < 64 by decide]

/-- A round's pointers: `r12` at the half it reads, `r13` at the one it XORs into. -/
structure Ptrs (ρ : Role) (s : State) : Prop where
  rd : s.gpr .r12 = s.gpr .rsi + BitVec.ofNat 64 (64 * rdOff ρ)
  wr : s.gpr .r13 = s.gpr .rsi + BitVec.ofNat 64 (64 * wrOff ρ)

theorem Ptrs.congr {ρ : Role} {s s' : State} (h : Ptrs ρ s) (h12 : s'.gpr .r12 = s.gpr .r12)
    (h13 : s'.gpr .r13 = s.gpr .r13) (hsi : s'.gpr .rsi = s.gpr .rsi) : Ptrs ρ s' :=
  ⟨by rw [h12, hsi]; exact h.rd, by rw [h13, hsi]; exact h.wr⟩

theorem zAddr_off (b : Addr) (e k : Nat) : zAddr (b + BitVec.ofNat 64 (64 * e)) k = zAddr b (k + e) := by
  simp only [zAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega_arith

theorem Ptrs.ea_rd {ρ : Role} {s : State} (h : Ptrs ρ s) {q : Nat} (hq : q < 32) :
    s.ea (rdWord (lWord q)) = zAddr (s.gpr .rsi) (readWord ρ q) := by
  rw [ea_of (b := .r12) rfl rfl rfl, h.rd, zAddr_off, readWord_off ρ q hq]

theorem zmm_load' (s : State) (d r : XReg) (v : BitVec 512) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)).zmm r = if r = d then v else s.zmm r := by
  split
  · rename_i h; subst h; exact zmm_load s r v
  · rename_i h; exact zmm_setZ_other s h _ _ _ _

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ maskReg := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: the next key bit as a mask, XORed with state word `w`. -/
theorem inputStep_run {s : State} (h : Room s) {x : XReg} (hx : x ≠ maskReg) {v w : Nat} (hw : w < 64)
    (hea : s.ea (rdWord v) = zAddr (s.gpr .rsi) w) :
    ∃ s', runBlock isa [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx),
        .vop (.vmovq maskReg .rbx), .zop (.vpbroadcastq maskReg maskReg), zload x (rdWord v),
        zbin .vpxord x x maskReg] s = some s' ∧
      s'.gpr .rax = s.gpr .rax <<< 1 ∧ s'.zmm x = words s w ^^^ maskZ (s.gpr .rax).msb ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      (∀ y, y ≠ x → y ≠ maskReg → s'.zmm y = s.zmm y) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr .rax
  let s₁ := (arithFlags s (a + a) (decide (2 ^ 64 ≤ a.toNat + a.toNat)) (addOverflow a a (a + a))).setReg
    .rax (a + a)
  have e₁ : exec (.alu .add .rax (.reg .rax)) s = some s₁ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]; rfl
  have cf₁ : s₁.cf = some a.msb := by
    simp only [s₁, cf_setReg, cf_arithFlags, add_self_carry]
  let b := s₁.gpr .rbx
  let r := b - b - (BitVec.ofBool a.msb).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (b.toNat < b.toNat + a.msb.toNat)) (subOverflow b b r)).setReg .rbx r
  have e₂ : exec (.alu .sbb .rbx (.reg .rbx)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some, cf₁, Option.map_some]; rfl
  have rbx₂ : s₂.gpr .rbx = maskVal a.msb := by
    simp only [s₂, gpr_setReg_self, r]; exact sbb_self _ _
  let s₃ := (VOp.vmovq maskReg .rbx).exec s₂
  let s₄ := (ZOp.vpbroadcastq maskReg maskReg).exec s₃
  have m₄ : s₄.zmm maskReg = maskZ a.msb := bcast_mask s₂ maskReg .rbx a.msb rbx₂
  have g₄ : s₄.gpr = s₂.gpr := by simp [s₄, s₃]
  have mem₄ : s₄.mem = s.mem := by simp [s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₄ : s₄.rd = s.rd := by simp [s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₄ : s₄.wr = s.wr := by simp [s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  have r12₄ : s₄.gpr .r12 = s.gpr .r12 := by simp [g₄, s₂, s₁, gpr_setReg]
  have ea₄ : s₄.ea (rdWord v) = zAddr (s.gpr .rsi) w := by
    rw [ea_of (b := .r12) (k := v) rfl rfl rfl, r12₄, ← ea_of (s := s) (m := rdWord v) (b := .r12) (k := v) rfl rfl rfl]
    exact hea
  have inR : InRegions (s₄.rd ++ s₄.wr) (s₄.ea (rdWord v)) 64 := by
    obtain ⟨r, hr, hc⟩ := h.state.slotIn w hw
    rw [ea₄, rd₄, wr₄]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  let val := s₄.mem.readW (s₄.ea (rdWord v)) 512
  have hv : val = words s w := by simp only [val, mem₄, words, ea₄]
  let s₅ := s₄.setZ x (val.extractLsb' 0 128) (val.extractLsb' 128 128) (val.extractLsb' 256 128)
    (val.extractLsb' 384 128)
  have e₅ : exec (zload x (rdWord v)) s₄ = some s₅ := by
    simp only [zload, exec, State.load512, inR, ite_true, Option.map_some]; rfl
  let s₆ := (ZOp.zbin .vpxord x x maskReg).exec s₅
  have y₄ : ∀ y, y ≠ maskReg → s₄.zmm y = s.zmm y := by
    intro y hy
    simp only [s₄, ZOp.exec]
    rw [zmm_setZ_other _ hy]
    simp only [s₃, VOp.exec, State.zmm, State.ymm, State.setV, hy, ite_false]; rfl
  refine ⟨s₆, ?_, ?_, ?_, fun r' h1 h2 => ?_, fun y h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons]
    rw [show exec (.vop (.vmovq maskReg .rbx)) s₂ = some s₃ from rfl, runStep_some,
      runBlock_cons, show exec (.zop (.vpbroadcastq maskReg maskReg)) s₃ = some s₄ from rfl,
      runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      show exec (zbin .vpxord x x maskReg) s₅ = some s₆ from rfl, runStep_some, runBlock_nil]
  · simp [s₆, s₅, g₄, s₂, s₁, gpr_setReg, add_self_eq, a]
  · simp only [s₆, zmm_vpxord, s₅, zmm_load', ite_true, Ne.symm hx, ite_false, m₄, hv, a]
  · simp [s₆, s₅, g₄, s₂, s₁, gpr_setReg, h1, h2]
  · simp only [s₆, ZOp.exec]
    rw [zmm_setZ_other _ h1, zmm_load']
    simp only [h1, ↓reduceIte]
    exact y₄ y h2
  · simp [s₆, s₅, mem₄]
  · simp [s₆, s₅, rd₄]
  · simp [s₆, s₅, wr₄]

def inputsN (j n : Nat) : List Instr :=
  (List.range n).flatMap fun m => inputStep j (5 - m)

theorem inputCode_eq (j : Nat) : inputCode j = inputsN j 6 := rfl

theorem inputsN_succ (j n : Nat) :
    inputsN j (n + 1) = inputsN j n ++ inputStep j (5 - n) := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s)
    (hp : Ptrs ρ s) :
    ∃ s', runBlock isa (inputsN j n) s = some s' ∧ s'.gpr .rax = s.gpr .rax <<< n ∧
      (∀ m < n, s'.zmm (inReg (5 - m)) = words s (readWord ρ (eBit (inBit j (5 - m)))) ^^^
        maskZ ((s.gpr .rax).getLsbD (63 - m))) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, by simp, fun m hm => by omega_arith, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, k₁, in₁, g₁, m₁, rd₁, wr₁⟩ := ih (by omega_arith)
    have h₁ : Room s₁ := h.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) wr₁
    have hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide))
      (g₁ _ (by decide) (by decide))
    have hq := inReg_ne (5 - n) (by omega_arith)
    obtain ⟨s₂, run₂, k₂, q₂, g₂, y₂, m₂, rd₂, wr₂⟩ :=
      inputStep_run h₁ hq (w := readWord ρ (eBit (inBit j (5 - n)))) (readWord_lt ρ j hj _ (by omega_arith))
        (hp₁.ea_rd (eBit_lt j hj _ (by omega_arith)))
    refine ⟨s₂, ?_, ?_, fun m hm => ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · rw [k₂, k₁, ← BitVec.shiftLeft_add]
    · by_cases he : m = n
      · subst he
        rw [q₂, k₁, msb_shiftLeft _ (by omega_arith)]
        simp only [words, m₁, g₁ .rsi (by decide) (by decide)]
      · have hne : inReg (5 - m) ≠ inReg (5 - n) := by
          intro e; have := inReg_inj' _ (by omega_arith) _ (by omega_arith) e; omega_arith
        rw [y₂ _ hne (inReg_ne (5 - m) (by omega_arith)), in₁ m (by omega_arith)]

/-! ## Outputs -/

/-- The output bit of S-box `j` that goes into the word `lWord q = x` above `r13`. -/
def outIdxW (j x : Nat) : Option Nat := (List.range 4).find? fun i => lWord (outBit j i) == x

def outPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 63).all fun k => e.slot k ==
    some (match outIdxW j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

/-- The written half's 63 words above `r13`. -/
def wrCfg : Cfg := { base := .r13, slots := 63 }

theorem output_check : ∀ j < 8, check (vars 64) wrCfg (outputCode j) (varEnv outRegs) (outPost j) = true := by
  lit_decide

theorem outIdxW_lt (j x i : Nat) (h : outIdxW j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

/-- The output into word `x` above `rsi`, by the one above `r13`. -/
theorem outIdx_off : ∀ ρ : Role, ∀ j < 8, ∀ x < 64, outIdx ρ j x =
    if wrOff ρ ≤ x ∧ x < 63 + wrOff ρ then outIdxW j (x - wrOff ρ) else none :=
  VG.Proof.TripleDes.Bitslice.outIdx_off

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_regs : ∀ j < 8,
    ((outputCode j).all fun i => i.dst == none) = true := by
  lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (hp : Ptrs ρ s) :
    ∃ s', runBlock isa (outputCode j) s = some s' ∧
      (∀ k < 64, words s' k = match outIdx ρ j k with
        | some i => words s k ^^^ s.zmm (outReg i)
        | none => words s k) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  have hw1 : wrOff ρ ≤ 1 := by cases ρ <;> decide
  have hok : Ok wrCfg s := ⟨fun k hk => by
      have := h.state.slotIn (k + wrOff ρ) (by simp only [wrCfg] at hk; simp only [stateCfg]; omega_arith)
      simp only [wrCfg, stateCfg] at this ⊢
      rw [hp.wr, zAddr_off]; exact this, by decide⟩
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRunB outRegs .r13 (n := 63) (by decide) (output_check j hj) hok
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp (outputCode_regs j hj)
  have hg : s'.gpr = s.gpr := funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this)
  have hsub : (slotRegion wrCfg s).Sub (stateR s) := by
    simp only [slotRegion, wrCfg, stateR, hp.wr]
    exact Offset.sub_base _ (by omega_arith)
  have eW : ∀ t : State, t.gpr .r13 = t.gpr .rsi + BitVec.ofNat 64 (64 * wrOff ρ) → ∀ k, wrOff ρ ≤ k →
      words t k = wordsB .r13 t (k - wrOff ρ) := fun t ht k hk => by
    simp only [words, wordsB]
    rw [ht, zAddr_off, Nat.sub_add_cancel hk]
  refine ⟨s', hrun, fun k hk => ?_, hg, p.rd, p.wr, p.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stateR s, List.mem_singleton_self _, hsub⟩⟩
  rw [outIdx_off ρ j hj k hk]
  by_cases hin : wrOff ρ ≤ k ∧ k < 63 + wrOff ρ
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    have hk' : k - wrOff ρ < 63 := by omega_arith
    have hk64 : k - wrOff ρ < 64 := by omega_arith
    rw [eW s' (by rw [hg]; exact hp.wr) k hin.1, eW s hp.wr k hin.1]
    apply eq_of_qw; intro q hq
    have hs := p.rel.slot (k - wrOff ρ) _ hk' (hpost (k - wrOff ρ) hk') q hq
    simp only [VarRel] at hs
    have e : qw (wordsB .r13 s' (k - wrOff ρ)) q =
        qw (s'.mem.readW (zAddr (s'.gpr (⟨.r13, 63⟩ : Cfg).base) (k - wrOff ρ)) 512) q := rfl
    rw [e, hs]
    split
    · rename_i i hi
      have hi4 := outIdxW_lt j _ i hi
      rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega_arith) (by simp [varN, outRegs]; omega_arith)]
      simp only [varValsB, hk64, ite_true, show ¬ 64 + i < 64 by omega_arith, ite_false,
        Nat.add_sub_cancel_left, qw_xor, outReg]
    · rw [xorSet_two_pow _ (by simp [varN]; omega_arith)]
      simp only [varValsB, hk64, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
    show s'.mem.readW (zAddr (s'.gpr .rsi) k) 512 = s.mem.readW (zAddr (s.gpr .rsi) k) 512
    rw [show s'.gpr .rsi = s.gpr .rsi by rw [hg]]
    refine p.frame.readW (r := ⟨zAddr (s.gpr .rsi) k, 64⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, hp.wr]
    exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-! ## One S-box -/

theorem spill_ok {s : State} (h : Room s) : Ok sboxCfg s :=
  Ok.of_off (off := 0) h.scratch (by simp [scratchR, sboxCfg]) (by simp [scratchR, sboxCfg, spills])
    (by simp [scratchR])

/-- The state words are apart from the spill slots. -/
theorem words_spill {s s' : State} (h : Room s) (hsi : s'.gpr .rsi = s.gpr .rsi)
    (hf : Frame [slotRegion sboxCfg s] s.mem s'.mem) (x : Nat) (hx : x < 64) :
    words s' x = words s x := by
  simp only [words, hsi]
  refine hf.readW (r := ⟨zAddr (s.gpr .rsi) x, 64⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  refine (h.sep.sub_left ?_).sub_right (Region.sub_prefix (by simp [sboxCfg, spills]))
  exact Offset.sub_base _ (by omega_arith)

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (hp : Ptrs ρ s)
    (k : BitVec 48)
    (hkey : ∀ i < 6, (s.gpr .rax).getLsbD (58 + i) = k.getLsbD (inBit j i)) :
    ∃ s', runBlock isa (sboxStep j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧ s'.gpr .rax = s.gpr .rax <<< 6 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, in₁, g₁, m₁, rd₁, wr₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h hp
  have c₁ := g₁ .rcx (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ wr₁
  have hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) si₁
  obtain ⟨s₂, run₂, out₂, g₂, cf₂, zf₂, rd₂, wr₂, f₂⟩ := sbox_ok j hj (spill_ok h₁)
  have h₂ := h₁.congr (by rw [g₂]) (by rw [g₂]) wr₂
  obtain ⟨s₃, run₃, w₃, g₃, rd₃, wr₃, f₃⟩ := outputs_ok ρ hj h₂ (hp₁.congr (by rw [g₂]) (by rw [g₂]) (by rw [g₂]))
  have w₂ : ∀ x < 64, words s₂ x = words s x := by
    intro x hx
    rw [words_spill h₁ (by rw [g₂]) f₂ x hx]
    simp only [words, m₁, si₁]
  have hin : ∀ i < 6, s₁.zmm (inReg i) =
      words s (readWord ρ (eBit (inBit j i))) ^^^ maskZ (k.getLsbD (inBit j i)) := by
    intro i hi
    have e := in₁ (5 - i) (by omega_arith)
    rw [show 5 - (5 - i) = i by omega_arith] at e
    rw [e, show 63 - (5 - i) = 58 + i by omega_arith, hkey i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, fun r h1 h2 => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [sboxStep, inputCode_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · rw [w₃ x hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact w₂ x hx
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [w₂ x hx]
      refine congrArg (words s x ^^^ ·) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      refine congrArg (fun z => (Spec.TripleDes.sBox j z).getLsbD i) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_maskZ _ hp]
  · rw [g₃, g₂, k₁]
  · rw [g₃, g₂, g₁ r h1 h2]
  · have a : Frame [spillR s, stateR s] s.mem s₁.mem := by rw [m₁]; exact Frame.refl _ _
    have b : Frame [spillR s, stateR s] s₁.mem s₂.mem := by
      refine f₂.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨spillR s, List.mem_cons_self, ?_⟩
      simp only [slotRegion, sboxCfg, spillR, c₁]
      exact Region.sub_prefix (by simp [spills])
    have c : Frame [spillR s, stateR s] s₂.mem s₃.mem := by
      refine f₃.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨stateR s, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [stateR, g₂, si₁]
      exact fun _ h => h
    exact (a.trans b).trans c

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k == some (2 ^ swapSlot k)

theorem swap_check : check (vars 64) stateCfg swapHalves (varEnv [.xmm0, .xmm1]) swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by lit_decide

theorem swap_regs : (swapHalves.all fun i => i.dst == none) = true := by
  lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [.xmm0, .xmm1] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp swap_regs
  refine ⟨s', hrun, fun x hx => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this), p.rd, p.wr, p.frame⟩
  apply eq_of_qw; intro q hq
  have hs := p.rel.slot x _ hx (hpost x hx) q hq
  simp only [VarRel] at hs
  have e : qw (words s' x) q = qw (s'.mem.readW (zAddr (s'.gpr stateCfg.base) x) 512) q := by
    simp only [words, stateCfg]
  rw [e, hs, xorSet_two_pow _ (by simp [varN]; have := swapSlot_lt x hx; omega_arith)]
  simp only [varVals, swapSlot_lt x hx, ite_true, laneW]
  unfold swapW swapSlot
  cases partner x <;> rfl

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

end

end

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
