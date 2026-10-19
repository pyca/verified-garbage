module

public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Machine
import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.TripleDes.Bitslice.OutIdx
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Sbox
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Sbox
import VerifiedGarbage.TCB.X86_64.Target

/-!
# One S-box of an AVX2 round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the next six key bits of
`rax` as masks, broadcast and XORed with the words of `E`; its circuit;
XORing its outputs into their words) does to the state words what `step`
does, given the key bits at the top of `rax`, and shifts them out.
`swapHalves_ok`: the exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.StraightY VG.X86_64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.X86_64.BitsliceAvx2 VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW rdOff wrOff readWord_off
  writeWord_off eBit_lt outBit_lt)

theorem add_self_eq (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega

theorem add_self_carry (a : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + a.toNat) = a.msb := by
  rw [BitVec.msb_eq_decide]
  have := a.isLt
  simp only [Nat.add_one_sub_one]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

theorem sbb_self (a : BitVec 64) (c : Bool) : a - a - (BitVec.ofBool c).setWidth 64 = maskVal c := by
  cases c <;> simp [maskVal]

theorem msb_shiftLeft (R : BitVec 64) {n : Nat} (hn : n < 64) : (R <<< n).msb = R.getLsbD (63 - n) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have : ¬ 63 < n := by omega
  simp [this, show (63 : Nat) < 64 by decide]

theorem word_in {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (s.ea (word w)) 32 := by
  obtain ⟨r, hr, hc⟩ := h.state.slotIn w hw
  have e : s.ea (word w) = yAddr (s.gpr stateCfg.base) w := ea_of rfl rfl rfl
  rw [e]
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A round's pointers: `r12` at the half it reads, `r13` at the one it XORs into. -/
structure Ptrs (ρ : Role) (s : State) : Prop where
  rd : s.gpr .r12 = s.gpr .rsi + BitVec.ofNat 64 (32 * rdOff ρ)
  wr : s.gpr .r13 = s.gpr .rsi + BitVec.ofNat 64 (32 * wrOff ρ)

theorem Ptrs.congr {ρ : Role} {s s' : State} (h : Ptrs ρ s) (h12 : s'.gpr .r12 = s.gpr .r12)
    (h13 : s'.gpr .r13 = s.gpr .r13) (hsi : s'.gpr .rsi = s.gpr .rsi) : Ptrs ρ s' :=
  ⟨by rw [h12, hsi]; exact h.rd, by rw [h13, hsi]; exact h.wr⟩

theorem yAddr_off (b : Addr) (e k : Nat) : yAddr (b + BitVec.ofNat 64 (32 * e)) k = yAddr b (k + e) := by
  simp only [yAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem Ptrs.ea_rd {ρ : Role} {s : State} (h : Ptrs ρ s) {q : Nat} (hq : q < 32) :
    s.ea (rdWord (lWord q)) = yAddr (s.gpr .rsi) (readWord ρ q) := by
  rw [ea_of (b := .r12) rfl rfl rfl, h.rd, yAddr_off, readWord_off ρ q hq]

theorem ymm_load (s : State) (d r : XReg) (v : BitVec 256) :
    (s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)).ymm r =
      if r = d then v else s.ymm r := by
  rw [ymm_setV, split_eq]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ maskReg ∧ inReg i ≠ ones := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: the next key bit as a mask, XORed with state word `w`. -/
theorem inputStep_run {s : State} (h : Room s) {x : XReg} (hx : x ≠ maskReg) {v w : Nat} (hw : w < 64)
    (hea : s.ea (rdWord v) = yAddr (s.gpr .rsi) w) :
    ∃ s', runBlock isa [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx),
        .vop (.vmovq maskReg .rbx), .vop (.vpbroadcastq .l256 maskReg maskReg), vload x (rdWord v),
        vbin .vpxor x x maskReg] s = some s' ∧
      s'.gpr .rax = s.gpr .rax <<< 1 ∧ s'.ymm x = words s w ^^^ maskY (s.gpr .rax).msb ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      (∀ y, y ≠ x → y ≠ maskReg → s'.ymm y = s.ymm y) ∧
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
  let s₄ := (VOp.vpbroadcastq .l256 maskReg maskReg).exec s₃
  have m₄ : s₄.ymm maskReg = maskY a.msb := bcast_mask s₂ maskReg .rbx a.msb rbx₂
  have g₄ : s₄.gpr = s₂.gpr := by simp [s₄, s₃]
  have mem₄ : s₄.mem = s.mem := by simp [s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₄ : s₄.rd = s.rd := by simp [s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₄ : s₄.wr = s.wr := by simp [s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  have r12₄ : s₄.gpr .r12 = s.gpr .r12 := by simp [g₄, s₂, s₁, gpr_setReg]
  have ea₄ : s₄.ea (rdWord v) = yAddr (s.gpr .rsi) w := by
    rw [ea_of (b := .r12) (k := v) rfl rfl rfl, r12₄, ← ea_of (s := s) (m := rdWord v) (b := .r12) (k := v) rfl rfl rfl]; exact hea
  have inR : InRegions (s₄.rd ++ s₄.wr) (s₄.ea (rdWord v)) 32 := by
    obtain ⟨r, hr, hc⟩ := h.state.slotIn w hw
    rw [ea₄, rd₄, wr₄]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  let val := s₄.mem.readW (s₄.ea (rdWord v)) 256
  have hv : val = words s w := by simp only [val, mem₄, words, ea₄]
  let s₅ := s₄.setV .l256 x (val.extractLsb' 0 128) (val.extractLsb' 128 128)
  have e₅ : exec (vload x (rdWord v)) s₄ = some s₅ := by
    simp only [vload, exec, State.load256, inR, ite_true, Option.map_some]; rfl
  let s₆ := (VOp.vbin .vpxor .l256 x x maskReg).exec s₅
  have y₂ : ∀ y, s₂.ymm y = s.ymm y := fun y => rfl
  have y₄ : ∀ y, y ≠ maskReg → s₄.ymm y = s.ymm y := by
    intro y hy
    simp only [s₄, s₃, VOp.exec, ymm_setV, ymm_setV128, hy, ite_false]; rfl
  refine ⟨s₆, ?_, ?_, ?_, fun r' h1 h2 => ?_, fun y h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons]
    rw [show exec (.vop (.vmovq maskReg .rbx)) s₂ = some s₃ from rfl, runStep_some,
      runBlock_cons, show exec (.vop (.vpbroadcastq .l256 maskReg maskReg)) s₃ = some s₄ from rfl,
      runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      show exec (vbin .vpxor x x maskReg) s₅ = some s₆ from rfl, runStep_some, runBlock_nil]
  · simp [s₆, s₅, g₄, s₂, s₁, gpr_setReg, add_self_eq, a]
  · simp only [s₆, ymm_vpxor, s₅, ymm_load, ite_true, Ne.symm hx, ite_false, m₄, hv, a]
  · simp [s₆, s₅, g₄, s₂, s₁, gpr_setReg, h1, h2]
  · simp only [s₆, VOp.exec, ymm_setV, h1, ite_false, s₅]
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
      (∀ m < n, s'.ymm (inReg (5 - m)) = words s (readWord ρ (eBit (inBit j (5 - m)))) ^^^
        maskY ((s.gpr .rax).getLsbD (63 - m))) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧
      s'.ymm ones = s.ymm ones ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, by simp, fun m hm => by omega, fun _ _ _ => rfl, rfl, rfl, rfl,
      rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, k₁, in₁, g₁, o₁, m₁, rd₁, wr₁⟩ := ih (by omega)
    have h₁ : Room s₁ := h.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) wr₁
    have hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide))
      (g₁ _ (by decide) (by decide))
    obtain ⟨hq, ho⟩ := inReg_ne (5 - n) (by omega)
    obtain ⟨s₂, run₂, k₂, q₂, g₂, y₂, m₂, rd₂, wr₂⟩ :=
      inputStep_run h₁ hq (w := readWord ρ (eBit (inBit j (5 - n)))) (readWord_lt ρ j hj _ (by omega))
        (hp₁.ea_rd (eBit_lt j hj _ (by omega)))
    refine ⟨s₂, ?_, ?_, fun m hm => ?_, fun r h1 h2 => (g₂ r h1 h2).trans (g₁ r h1 h2),
      (y₂ _ (Ne.symm ho) (by decide)).trans o₁, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · rw [k₂, k₁, ← BitVec.shiftLeft_add]
    · by_cases he : m = n
      · subst he
        rw [q₂, k₁, msb_shiftLeft _ (by omega)]
        simp only [words, m₁, g₁ .rsi (by decide) (by decide)]
      · have hne : inReg (5 - m) ≠ inReg (5 - n) := by
          intro e; have := inReg_inj' _ (by omega) _ (by omega) e; omega
        rw [y₂ _ hne (inReg_ne (5 - m) (by omega)).1, in₁ m (by omega)]

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
    ((outputCode j).all fun i => i.dst == none && ydst i != some ones) = true := by
  lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (hp : Ptrs ρ s) :
    ∃ s', runBlock isa (outputCode j) s = some s' ∧
      (∀ k < 64, words s' k = match outIdx ρ j k with
        | some i => words s k ^^^ s.ymm (outReg i)
        | none => words s k) ∧
      s'.gpr = s.gpr ∧ s'.ymm ones = s.ymm ones ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  have hw1 : wrOff ρ ≤ 1 := by cases ρ <;> decide
  have hok : Ok wrCfg s := ⟨fun k hk => by
      have := h.state.slotIn (k + wrOff ρ) (by simp only [wrCfg] at hk; simp only [stateCfg]; omega)
      simp only [wrCfg, stateCfg] at this ⊢
      rw [hp.wr, yAddr_off]; exact this, by decide⟩
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
    exact Offset.sub_base _ (by omega)
  have eW : ∀ t : State, t.gpr .r13 = t.gpr .rsi + BitVec.ofNat 64 (32 * wrOff ρ) → ∀ k, wrOff ρ ≤ k →
      words t k = wordsB .r13 t (k - wrOff ρ) := fun t ht k hk => by
    simp only [words, wordsB]
    rw [ht, yAddr_off, Nat.sub_add_cancel hk]
  refine ⟨s', hrun, fun k hk => ?_, hg,
    p.other ones (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this), p.rd, p.wr, p.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stateR s, List.mem_singleton_self _, hsub⟩⟩
  rw [outIdx_off ρ j hj k hk]
  by_cases hin : wrOff ρ ≤ k ∧ k < 63 + wrOff ρ
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]
    have hk' : k - wrOff ρ < 63 := by omega
    have hk64 : k - wrOff ρ < 64 := by omega
    rw [eW s' (by rw [hg]; exact hp.wr) k hin.1, eW s hp.wr k hin.1]
    apply eq_of_qw; intro q hq
    have hs := p.rel.slot (k - wrOff ρ) _ hk' (hpost (k - wrOff ρ) hk') q hq
    simp only [VarRel] at hs
    have e : qw (wordsB .r13 s' (k - wrOff ρ)) q =
        qw (s'.mem.readW (yAddr (s'.gpr (⟨.r13, 63⟩ : Cfg).base) (k - wrOff ρ)) 256) q := rfl
    rw [e, hs]
    split
    · rename_i i hi
      have hi4 := outIdxW_lt j _ i hi
      rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega) (by simp [varN, outRegs]; omega)]
      simp only [varValsB, hk64, ite_true, show ¬ 64 + i < 64 by omega, ite_false,
        Nat.add_sub_cancel_left, qw_xor, outReg]
    · rw [xorSet_two_pow _ (by simp [varN]; omega)]
      simp only [varValsB, hk64, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hin)]
    show s'.mem.readW (yAddr (s'.gpr .rsi) k) 256 = s.mem.readW (yAddr (s.gpr .rsi) k) 256
    rw [show s'.gpr .rsi = s.gpr .rsi by rw [hg]]
    refine p.frame.readW (r := ⟨yAddr (s.gpr .rsi) k, 32⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, hp.wr]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-! ## One S-box -/

theorem spill_ok {s : State} (h : Room s) : Ok sboxCfg s :=
  Ok.of_off (off := 0) h.scratch (by simp [scratchR, sboxCfg]) (by simp [scratchR, sboxCfg, spills])
    (by simp [scratchR])

/-- The state words are apart from the spill slots. -/
theorem words_spill {s s' : State} (h : Room s) (hsi : s'.gpr .rsi = s.gpr .rsi)
    (hf : Frame [slotRegion sboxCfg s] s.mem s'.mem) (x : Nat) (hx : x < 64) :
    words s' x = words s x := by
  simp only [words, hsi]
  refine hf.readW (r := ⟨yAddr (s.gpr .rsi) x, 32⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  refine (h.sep.sub_left ?_).sub_right (Region.sub_prefix (by simp [sboxCfg, spills]))
  exact Offset.sub_base _ (by omega)

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (hp : Ptrs ρ s)
    (hones : s.ymm ones = BitVec.allOnes 256) (k : BitVec 48)
    (hkey : ∀ i < 6, (s.gpr .rax).getLsbD (58 + i) = k.getLsbD (inBit j i)) :
    ∃ s', runBlock isa (sboxStep j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧ s'.gpr .rax = s.gpr .rax <<< 6 ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.ymm ones = s.ymm ones ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [spillR s, stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, in₁, g₁, o₁, m₁, rd₁, wr₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h hp
  have c₁ := g₁ .rcx (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ wr₁
  have hp₁ : Ptrs ρ s₁ := hp.congr (g₁ _ (by decide) (by decide)) (g₁ _ (by decide) (by decide)) si₁
  obtain ⟨s₂, run₂, out₂, g₂, cf₂, zf₂, rd₂, wr₂, o₂, f₂⟩ := sbox_ok j hj (spill_ok h₁) (by rw [o₁, hones])
  have h₂ := h₁.congr (by rw [g₂]) (by rw [g₂]) wr₂
  obtain ⟨s₃, run₃, w₃, g₃, o₃, rd₃, wr₃, f₃⟩ := outputs_ok ρ hj h₂ (hp₁.congr (by rw [g₂]) (by rw [g₂]) (by rw [g₂]))
  have w₂ : ∀ x < 64, words s₂ x = words s x := by
    intro x hx
    rw [words_spill h₁ (by rw [g₂]) f₂ x hx]
    simp only [words, m₁, si₁]
  have hin : ∀ i < 6, s₁.ymm (inReg i) =
      words s (readWord ρ (eBit (inBit j i))) ^^^ maskY (k.getLsbD (inBit j i)) := by
    intro i hi
    have e := in₁ (5 - i) (by omega)
    rw [show 5 - (5 - i) = i by omega] at e
    rw [e, show 63 - (5 - i) = 58 + i by omega, hkey i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, fun r h1 h2 => ?_, ?_, rd₃.trans (rd₂.trans rd₁),
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
        BitVec.getLsbD_xor, getLsbD_maskY _ hp]
  · rw [g₃, g₂, k₁]
  · rw [g₃, g₂, g₁ r h1 h2]
  · rw [o₃, o₂, o₁]
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

theorem swap_regs : (swapHalves.all fun i => i.dst == none && ydst i != some ones) = true := by
  lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      s'.gpr = s.gpr ∧ s'.ymm ones = s.ymm ones ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [.xmm0, .xmm1] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp swap_regs
  refine ⟨s', hrun, fun x hx => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other ones (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this), p.rd, p.wr, p.frame⟩
  apply eq_of_qw; intro q hq
  have hs := p.rel.slot x _ hx (hpost x hx) q hq
  simp only [VarRel] at hs
  have e : qw (words s' x) q = qw (s'.mem.readW (yAddr (s'.gpr stateCfg.base) x) 256) q := by
    simp only [words, stateCfg]
  rw [e, hs, xorSet_two_pow _ (by simp [varN]; have := swapSlot_lt x hx; omega)]
  simp only [varVals, swapSlot_lt x hx, ite_true, laneW]
  unfold swapW swapSlot
  cases partner x <;> rfl

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
