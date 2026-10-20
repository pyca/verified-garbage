module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.TripleDes.Bitslice.TransposeIdx
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit

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
    exact inWord_rel (laneW s q) (by omega)
  obtain ⟨s', hs', p⟩ := run (fun _ _ => lanes_sound) hok hrel he
  refine ⟨s', hs', fun q hq j hj b hb => ?_, fun r hr => p.gpr r (by simp [hr]), p.rd, p.wr, p.sp, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot j _ hj (beq_iff_eq.mp hpj) q hq
  have bits := outWord_rel (fun p hp a ha => by
    simp only [List.mem_singleton] at ha; subst ha; have := hg j hj p hp; omega) hs
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
      Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) (by rw [Nat.shiftLeft_eq]; omega)
    omega
  · omega

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
    exact h₀.slotIn (a + k) (by show a + k < 64; omega)
  slots := by show 16 * n < 2 ^ 64; omega

/-- A word outside a group's slots is unchanged. -/
theorem lane_out {m m' : Mem} {D : Addr} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨vAddr D a, 16 * n⟩] m m') {j : Nat} (hj : j < 64) (hout : j < a ∨ a + n ≤ j) (q : Nat) :
    laneAt m' D q j = laneAt m D q j := by
  simp only [laneAt]
  rw [hf.readW (r := ⟨vAddr D j, 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega) (by omega) (by omega)) (by decide)]

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

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- A group's slots are in the state words. -/
theorem frame_state {s₀ : State} {m m' : Mem} {a n : Nat} (ha : a + n ≤ 64)
    (hf : Frame [⟨vAddr (s₀.gpr .x4) a, 16 * n⟩] m m') : Frame [stateR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩

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
  have hok := ok_window (a := 8 - n) (n := 57) h₀ rfl (by omega) hs.x4 hs.keep.wr
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
      wr₃.trans (wr₁.trans hs.keep.wr), sp₃.trans hs.keep.sp, hs.keep.frame.trans (m₃ ▸ frame_state (by omega) f₁)⟩
  have rsi₃ : s₃.gpr .x4 = vAddr D (8 - n + 1) := by
    rw [si₃, hs.x4, show BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 1) from rfl]
    exact vAddr_succ D (8 - n) 1
  have cnt : s.gpr .x9 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.x9]; exact cnt8_sub n hn₁
  rw [eval_nz, c₃, cnt, cnt8_zero (n - 1) (by omega)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, rsi₃, fun q hq j hj => ?_⟩
    have c : j % 8 < 8 - 1 + 1 := by omega
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp; omega, n - 1, by omega, keep₃, by omega, by omega,
      by rw [rsi₃]; congr 1; omega, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega]

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
  have hok := ok_window (a := 8 * (8 - n)) (n := 8) h₀ rfl (by omega) hs.x4 hs.keep.wr
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
      wr₃.trans (wr₁.trans hs.keep.wr), sp₃.trans hs.keep.sp, hs.keep.frame.trans (m₃ ▸ frame_state (by omega) f₁)⟩
  have rsi₃ : s₃.gpr .x4 = vAddr D (8 * (8 - n) + 8) := by
    rw [si₃, hs.x4, show BitVec.ofNat 64 128 = BitVec.ofNat 64 (16 * 8) from rfl]
    exact vAddr_succ D (8 * (8 - n)) 8
  have cnt : s.gpr .x9 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by rw [hs.x9]; exact cnt8_sub n hn₁
  rw [eval_nz, c₃, cnt, cnt8_zero (n - 1) (by omega)]
  by_cases h1 : n = 1
  · subst h1
    left
    refine ⟨rfl, keep₃, by rw [rsi₃], fun q hq j hj => ?_⟩
    have c : j / 8 < 8 - 1 + 1 := by omega
    rw [lanes₃ q hq j hj]; simp only [c, ↓reduceIte]
  · right
    refine ⟨by simp; omega, n - 1, by omega, keep₃, by omega, by omega,
      by rw [rsi₃]; congr 1; omega, by rw [c₃, cnt], fun q hq j hj => ?_⟩
    rw [lanes₃ q hq j hj, show 8 - (n - 1) = 8 - n + 1 by omega]

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
