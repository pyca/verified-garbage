module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Round
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables

/-! ### `TripleDes.X86_64.Bitsliced.Step`, which this module and modules that import it used -/

section

/-! ### `TripleDes.X86_64.Bitsliced.Machine`, which this module and modules that import it used -/

section

/-! ### `TripleDes.X86_64.Bitsliced.Sbox`, which only this module used -/

section

/-!
# The bitsliced S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs, and
the truth-table evaluator lifts that check to every bit position of
arbitrary 64-bit words, as for the scalar code (`../Sbox.lean`). The
circuits spill to the scratch buffer (`[rcx + 8k]`, `k < spills`) and leave
`rcx`, `rsp` and `r15` (the round key) alone.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

def sboxCfg : Cfg := { base := .rcx, slots := spills, ext := .rsp, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    check (table 64 64) sboxCfg (fun _ => none) (instrs (sboxLiteral j))
      sboxEnv (sboxPost j) = true := by
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
    (instrs (sboxLiteral j)).all (fun op => op.dst != some .r15) = true := by
  lit_decide

/-- Bit `p` of each input register, as the S-box's input. -/
def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.gpr (inReg i)).getLsbD p

theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k = (s.gpr (inReg k)).getLsbD p := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

/-- Every S-box output bit, for arbitrary input words and spill slots. Only
the spill slots change in memory, and `rcx`, `rsp` and `r15` are left alone. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ p < 64, (s'.gpr (outReg i)).getLsbD p =
        (Spec.TripleDes.sBox j (inputAt s p)).getLsbD i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r15 = s.gpr .r15 ∧ Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (TableRel p (inputAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode j).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun i hi p hp => ?_, p₀.rd, p₀.wr, p₀.base, p₀.ext, p₀.other .r15 (by
    have h := sbox_preserves j hj
    rw [codeEq] at h
    simp [h]), p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key p hp
  obtain rfl := run_unique hs'' hs'
  have h := p₁.rel.reg (outReg i) _ (hout i hi)
  simp only [TableRel, outputTable, testBit_tableOf, (inputAt s p).isLt,
    decide_true, Bool.true_and] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end


/-!
# The machine state of the bitsliced ECB code

The code keeps its state in the 128 slots of the scratch buffer (`rcx`,
`sl s j`) and in the stack frame (`rsp`). `Room` says that both are
writable and apart. Blocks that only move and XOR words between registers
and scratch slots are checked by evaluation over the variable domain
(`Bitslice.vars`): `varsRun` runs one, its variables being the scratch
slots (variable `k < 128`) and some registers (variable `128 + i`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice

/-- Scratch slot `j`. -/
def sl (s : State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .rcx) j) 64

/-- The 64 state words. -/
def words (s : State) : Nat → BitVec 64 := fun j => sl s (stSlot j)

def scratchR (s : State) : Region := ⟨s.gpr .rcx, 1024⟩
/-- The spill slots, at the start of the scratch buffer. -/
def spillR (s : State) : Region := ⟨s.gpr .rcx, 8 * spills⟩

/-- The scratch buffer is writable. -/
structure Room (s : State) : Prop where
  scratch : scratchR s ∈ s.wr

theorem Room.congr {s s' : State} (h : Room s) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hw : s'.wr = s.wr) : Room s' where
  scratch := by simp only [scratchR, hc, hw]; exact h.scratch

theorem slot_in_scratch (s : State) {j : Nat} (hj : j < 128) :
    (scratchR s).Contains (wordAddr (s.gpr .rcx) j) (64 / 8) :=
  slot_contains (s.gpr .rcx) (n := 128) hj (by decide)

/-- Writes to the spill slots alone leave the other scratch slots. -/
theorem sl_of_spill {s s' : State} (hc : s'.gpr .rcx = s.gpr .rcx)
    (hf : Frame [spillR s] s.mem s'.mem) {j : Nat} (hj : spills ≤ j) (hj' : j < 128) :
    sl s' j = sl s j := by
  simp only [sl, hc]
  refine hf.readW (r := ⟨wordAddr (s.gpr .rcx) j, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base (s.gpr .rcx) (d := 8 * j) (n := 8) (k := 8 * spills)
    (by unfold spills at hj ⊢; omega_using [hj]) (by omega_using [hj'])

theorem spill_sub (s : State) : Region.Sub (spillR s) (scratchR s) := Region.sub_prefix (by decide)

theorem spill_toScratch {s : State} {m m' : Mem} (h : Frame [spillR s] m m') :
    Frame [scratchR s] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scratchR s, List.mem_singleton_self _, spill_sub s⟩

/-! ## Loads and stores of scratch slots -/

theorem ea_at (s : State) (k : Nat) : s.ea (at_ k) = wordAddr (s.gpr .rcx) k := rfl

theorem slot_writable {s : State} (h : Room s) {k : Nat} (hk : k < 128) :
    InRegions s.wr (wordAddr (s.gpr .rcx) k) 8 :=
  ⟨scratchR s, h.scratch, slot_in_scratch s hk⟩

theorem slot_readable {s : State} (h : Room s) {k : Nat} (hk : k < 128) :
    InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .rcx) k) 8 :=
  ⟨scratchR s, List.mem_append_right _ h.scratch, slot_in_scratch s hk⟩

theorem exec_ld {s : State} (h : Room s) {k : Nat} (hk : k < 128) (r : Reg) :
    exec (ld r k) s = some (s.setReg r (sl s k)) := by
  simp only [ld, exec, readSrc, State.load64, ea_at, slot_readable h hk, ite_true,
    Option.map_some, sl]

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .rcx) k) v

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < 128) (r : Reg) :
    exec (st k r) s = some { s with mem := stMem s k (s.gpr r) } := by
  simp only [st, exec, State.store64, ea_at, slot_writable h hk, ite_true, stMem]

theorem readW_stMem (s : State) {k : Nat} (hk : k < 128) (v : BitVec 64) {j : Nat} (hj : j < 128) :
    (stMem s k v).readW (wordAddr (s.gpr .rcx) j) 64 = if j = k then v else sl s j := by
  simp only [stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj]) (by omega_using [hk]) hne) (by decide)]
    rfl

theorem stMem_frame {s : State} {k : Nat} (hk : k < 128) (v : BitVec 64) :
    Frame [scratchR s] s.mem (stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in_scratch s hk)

theorem sl_setReg (s : State) {r : Reg} (hr : r ≠ .rcx) (v : BitVec 64) (j : Nat) :
    sl (s.setReg r v) j = sl s j := by
  simp only [sl, mem_setReg, gpr_setReg_of_ne (s := s) v (Ne.symm hr)]

theorem sl_arithFlags {w : Nat} (s : State) (x : BitVec w) (c o : Bool) (j : Nat) :
    sl (arithFlags s x c o) j = sl s j := by
  simp only [sl, mem_arithFlags, gpr_arithFlags]

theorem sl_st (s : State) {k : Nat} (hk : k < 128) (v : BitVec 64) {j : Nat} (hj : j < 128) :
    sl { s with mem := stMem s k v } j = if j = k then v else sl s j :=
  readW_stMem s hk v hj

theorem exec_movImm (s : State) (d : Reg) (v : BitVec 32) :
    exec (.mov d (.imm v)) s = some (s.setReg d (v.signExtend 64)) := rfl

theorem exec_addImm (s : State) (d : Reg) (v : BitVec 32) :
    exec (.alu .add d (.imm v)) s = some ((arithFlags s (s.gpr d + v.signExtend 64)
      (decide (2 ^ 64 ≤ (s.gpr d).toNat + (v.signExtend 64).toNat))
      (addOverflow (s.gpr d) (v.signExtend 64) (s.gpr d + v.signExtend 64))).setReg d
      (s.gpr d + v.signExtend 64)) := rfl

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

theorem frame_of_spills {s s' : State} (h : Frame [slotRegion sboxCfg s] s.mem s'.mem) :
    Frame [spillR s] s.mem s'.mem := h

/-! ## Blocks over the variable domain -/

/-- Slots `[rcx + 8k]`, `k < 128`. -/
def varsCfg : Cfg := { base := .rcx, slots := 128, ext := .rsp, exts := 0 }

/-- Slot `k` is variable `k`; register `regs[i]` is variable `128 + i`. -/
def varEnv (regs : List Reg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (128 + i),
    slot := fun k => if k < 128 then some (2 ^ k) else none }

/-- The values of the variables. -/
def varVals (s : State) (regs : List Reg) (v : Nat) : BitVec 64 :=
  if v < 128 then sl s v else s.gpr (regs.getD (v - 128) .rax)

def varN (regs : List Reg) : Nat := 128 + regs.length

theorem Room.ok {s : State} (h : Room s) : Ok varsCfg s :=
  Ok.of_region h.scratch rfl (by show 8 * 128 ≤ 1024; decide) (by decide) rfl

theorem varEnv_rel {s : State} (regs : List Reg) :
    Rel (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) (varEnv regs) s where
  reg r a h := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hlt])]
    simp only [varVals, show ¬ 128 + i < 128 by omega_using [], ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h := by
    have hk' : k < 128 := hk
    simp only [varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega_using [hk'])]
    simp only [varVals, hk', ite_true, sl, varsCfg]
  ext _ _ hk := by simp [varsCfg] at hk

/-- Run a block that the variable domain accepts. -/
theorem varsRun {is : List Instr} (regs : List Reg) {post : Env Nat → Bool}
    (hchk : check (vars 64) varsCfg (fun _ => none) is (varEnv regs) post = true)
    {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) e' s s'
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨s', hs', p⟩ := run (vars_sound _ _) h.ok (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem varRel_slot {V : Nat → BitVec 64} {N : Nat} {e : Env Nat} {s : State}
    (hrel : Rel (VarRel V N) varsCfg (fun _ => none) e s) {k a : Nat} (hk : k < 128)
    (ha : e.slot k = some a) : sl s k = xorSet V a N :=
  hrel.slot k a hk ha

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end

/-!
# One S-box of a bitsliced round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the next six key bits of
`r15` as masks XORed with the words of `E`; its circuit; XORing its outputs
into their words) does to the state words what `step` does, given the key
bits at the top of `r15`, and shifts them out. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem add_self_eq (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1
  omega_using []

theorem add_self_carry (a : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + a.toNat) = a.msb := by
  rw [BitVec.msb_eq_decide]
  have := a.isLt
  simp only [Nat.add_one_sub_one]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega_using [h]

theorem sbb_self (a : BitVec 64) (c : Bool) : a - a - (BitVec.ofBool c).setWidth 64 = maskVal c := by
  cases c <;> simp [maskVal]

theorem msb_shiftLeft (R : BitVec 64) {n : Nat} (hn : n < 64) : (R <<< n).msb = R.getLsbD (63 - n) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have : ¬ 63 < n := by omega_using [hn]
  simp [this, show (63 : Nat) < 64 by decide]

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 64) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .r15 ∧ inReg i ≠ .rcx ∧ inReg i ≠ .rsp := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: the next key bit as a mask, XORed with slot `w`. -/
theorem inputStep_run {s : State} (h : Room s) {q : Reg} (hq : q ≠ .r15) (hc : q ≠ .rcx)
    {w : Nat} (hw : w < 128) :
    ∃ s', runBlock isa [.alu .add .r15 (.reg .r15), .alu .sbb q (.reg q), .alu .xor q (.mem (at_ w))] s
        = some s' ∧
      s'.gpr .r15 = s.gpr .r15 <<< 1 ∧ s'.gpr q = maskVal (s.gpr .r15).msb ^^^ sl s w ∧
      (∀ r, r ≠ q → r ≠ .r15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr .r15
  let s₁ := (arithFlags s (a + a) (decide (2 ^ 64 ≤ a.toNat + a.toNat)) (addOverflow a a (a + a))).setReg
    .r15 (a + a)
  have e₁ : exec (.alu .add .r15 (.reg .r15)) s = some s₁ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]; rfl
  have cf₁ : s₁.cf = some a.msb := by
    simp only [s₁, cf_setReg, cf_arithFlags, add_self_carry]
  let b := s₁.gpr q
  let r := b - b - (BitVec.ofBool a.msb).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (b.toNat < b.toNat + a.msb.toNat)) (subOverflow b b r)).setReg q r
  have e₂ : exec (.alu .sbb q (.reg q)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some, cf₁, Option.map_some]; rfl
  have c₂ : s₂.gpr .rcx = s.gpr .rcx := by
    simp [s₂, s₁, gpr_setReg, Ne.symm hc]
  have m₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₂ : s₂.rd = s.rd := by simp [s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₂ : s₂.wr = s.wr := by simp [s₂, s₁, wr_setReg, wr_arithFlags]
  have h₂ : Room s₂ := h.congr c₂ wr₂
  let v := sl s w
  let x := s₂.gpr q ^^^ v
  let s₃ := (arithFlags s₂ x false false).setReg q x
  have e₃ : exec (.alu .xor q (.mem (at_ w))) s₂ = some s₃ := by
    simp only [exec, execAlu, readSrc, State.load64, ea_at, slot_readable h₂ hw, ite_true,
      Option.bind_some]
    have : s₂.mem.readW (wordAddr (s₂.gpr .rcx) w) 64 = v := by simp only [m₂, c₂]; rfl
    rw [this]
  refine ⟨s₃, ?_, ?_, ?_, fun r' h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, Ne.symm hq, add_self_eq, a]
  · simp only [s₃, gpr_setReg_self, x]
    congr 1
    simp only [s₂, gpr_setReg_self, r]
    exact sbb_self _ _
  · simp [s₃, s₂, s₁, gpr_setReg, h1, h2]
  -- (By the lemmas, with their arguments: `simp` leaves the kernel to compare `s₃` with `s₂`.)
  · exact (mem_setReg (s := arithFlags s₂ x false false) q x).trans ((mem_arithFlags (s := s₂) x false false).trans m₂)
  · exact (rd_setReg (s := arithFlags s₂ x false false) q x).trans ((rd_arithFlags (s := s₂) x false false).trans rd₂)
  · exact (wr_setReg (s := arithFlags s₂ x false false) q x).trans ((wr_arithFlags (s := s₂) x false false).trans wr₂)

def inputsN (ρ : Role) (j n : Nat) : List Instr :=
  (List.range n).flatMap fun m => inputStep ρ j (5 - m)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j (5 - n) := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readSlot_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, stSlot (readWord ρ (eBit (inBit j i))) < 72 := by
  intro ρ; cases ρ <;> lit_decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s) :
    ∃ s', runBlock isa (inputsN ρ j n) s = some s' ∧ s'.gpr .r15 = s.gpr .r15 <<< n ∧
      (∀ m < n, s'.gpr (inReg (5 - m)) = maskVal ((s.gpr .r15).getLsbD (63 - m)) ^^^
        sl s (stSlot (readWord ρ (eBit (inBit j (5 - m)))))) ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, by simp, fun m hm => by omega, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, k₁, in₁, c₁, sp₁, m₁, rd₁, wr₁⟩ := ih (by omega_using [hn])
    have h₁ : Room s₁ := h.congr c₁ wr₁
    obtain ⟨hq, hc, hsp⟩ := inReg_ne (5 - n) (by omega_using [])
    obtain ⟨s₂, run₂, k₂, q₂, o₂, m₂, rd₂, wr₂⟩ :=
      inputStep_run h₁ hq hc (w := stSlot (readWord ρ (eBit (inBit j (5 - n)))))
        (by have := readSlot_lt ρ j hj (5 - n) (by omega_using []); omega_using [this])
    refine ⟨s₂, ?_, ?_, fun m hm => ?_, ?_, ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · rw [k₂, k₁, ← BitVec.shiftLeft_add]
    · by_cases he : m = n
      · subst he
        rw [q₂, k₁, msb_shiftLeft _ (by omega_using [hn])]
        simp only [sl, m₁, c₁]
      · have hne : inReg (5 - m) ≠ inReg (5 - n) := by
          intro e; have := inReg_inj' _ (by omega_using []) _ (by omega_using []) e; omega_using [hn, hm, he, this]
        rw [o₂ _ hne (inReg_ne (5 - m) (by omega_using [])).1, in₁ m (by omega_using [hm, he])]
    · rw [o₂ _ (Ne.symm hc) (by decide)]; exact c₁
    · rw [o₂ _ (Ne.symm hsp) (by decide)]; exact sp₁

/-! ## Outputs -/

/-- The output bit of S-box `j` that goes into scratch slot `k`, if any. -/
def outSlot (ρ : Role) (j k : Nat) : Option Nat :=
  if 8 ≤ k ∧ k < 72 then outIdx ρ j (k - 8) else none

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 128).all fun k => e.slot k ==
    some (match outSlot ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (128 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 64) varsCfg (fun _ => none) (outputCode ρ j) (varEnv outRegs) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_r15 : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => i.dst != some .r15) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 128, sl s' k = match outSlot ρ j k with
        | some i => sl s k ^^^ s.gpr (outReg i)
        | none => sl s k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r15 = s.gpr .r15 ∧ Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun outRegs (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, p.rd, p.wr, p.base, p.ext,
    p.other .r15 (by simp [outputCode_r15 ρ j hj]), p.frame⟩
  rw [varRel_slot p.rel hk (hpost k hk)]
  split
  · rename_i i hi
    have hi4 : i < 4 := by
      simp only [outSlot] at hi
      split at hi
      · exact outIdx_lt ρ j _ i hi
      · cases hi
    rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega_using [hk]) (by simp [varN, outRegs]; omega_using [hi4])]
    have e1 : ¬ 128 + i < 128 := by omega_using []
    simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outReg]
  · rw [xorSet_two_pow _ (by simp [varN]; omega_using [hk])]
    simp only [varVals, hk, ite_true]

/-! ## One S-box -/

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : ∀ i < 6, (s.gpr .r15).getLsbD (58 + i) = k.getLsbD (inBit j i)) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.gpr .r15 = s.gpr .r15 <<< 6 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, in₁, c₁, sp₁, m₁, rd₁, wr₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h
  have h₁ := h.congr c₁ wr₁
  have ok₁ : Ok sboxCfg s₁ :=
    Ok.of_region h₁.scratch rfl (by show 8 * spills ≤ 1024; decide) (by decide) rfl
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, c₂, sp₂, k₂, f₂⟩ := sbox_ok j hj ok₁
  have h₂ := h₁.congr c₂ wr₂
  obtain ⟨s₃, run₃, sl₃, rd₃, wr₃, c₃, sp₃, k₃, f₃⟩ := outputs_ok ρ hj h₂
  have sl₂ : ∀ x < 128, spills ≤ x → sl s₂ x = sl s x := by
    intro x hx hs
    rw [sl_of_spill c₂ (frame_of_spills f₂) hs hx]
    simp only [sl, m₁, c₁]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      maskVal (k.getLsbD (inBit j i)) ^^^ sl s (stSlot (readWord ρ (eBit (inBit j i)))) := by
    intro i hi
    have e := in₁ (5 - i) (by omega_using [])
    rw [show 5 - (5 - i) = i by omega_using [hi]] at e
    rw [e, show 63 - (5 - i) = 58 + i by omega_using [hi], hkey i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, fun x hx hl => ?_, ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), c₃.trans (c₂.trans c₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [sboxStep, inputCode_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · have hs : stSlot x < 128 := by unfold stSlot; omega_using [hx]
    have e₂ : sl s₂ (stSlot x) = words s x := sl₂ _ hs (by unfold stSlot spills; omega_using [])
    have hos : outSlot ρ j (stSlot x) = outIdx ρ j x := by
      simp only [outSlot, stSlot, show 8 ≤ 8 + x ∧ 8 + x < 72 by omega_using [hx], and_self, ite_true,
        Nat.add_sub_cancel_left]
    simp only [words]
    rw [sl₃ _ hs, hos]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact e₂
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [e₂]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_mask _ hp, words]
      rw [Bool.xor_comm]
  · rw [sl₃ x hx]
    have : outSlot ρ j x = none := by
      simp only [outSlot, show ¬ (8 ≤ x ∧ x < 72) by omega_using [hl], ite_false]
    rw [this]
    exact sl₂ x hx (by unfold spills; omega_using [hl])
  · rw [k₃, k₂, k₁]
  · have g₁ : Frame [scratchR s] s.mem s₁.mem := by rw [m₁]; exact Frame.refl _ _
    have g₂ : Frame [scratchR s] s₁.mem s₂.mem := by
      have := spill_toScratch (frame_of_spills f₂)
      rwa [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at this
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, c₂, c₁]] at f₃
    exact g₁.trans (g₂.trans f₃)

/-! ## The exchange of the halves -/

/-- The slot whose word goes into slot `k`. -/
def swapSlot (k : Nat) : Nat :=
  if 8 ≤ k ∧ k < 72 then (match partner (k - 8) with | some y => 8 + y | none => k) else k

def swapPost (e : Env Nat) : Bool :=
  (List.range 128).all fun k => e.slot k == some (2 ^ swapSlot k)

theorem swap_check :
    check (vars 64) varsCfg (fun _ => none) swapHalves (varEnv []) swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 128, swapSlot k < 128 := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 128, sl s' k = sl s (swapSlot k) := by
    intro k hk
    rw [varRel_slot p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, fun x hx hl => ?_, p.rd, p.wr, p.base, p.ext, p.frame⟩
  · simp only [words, stSlot]
    rw [key _ (by omega_using [hx])]
    simp only [swapW, swapSlot, show 8 ≤ 8 + x ∧ 8 + x < 72 by omega_using [hx], and_self, ite_true,
      Nat.add_sub_cancel_left]
    rcases partner x with _ | y <;> rfl
  · rw [key x hx]
    simp only [swapSlot, show ¬ (8 ≤ x ∧ x < 72) by omega_using [hl], ite_false]

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end

/-! ### `TripleDes.X86_64.Bitsliced.Round`, which only this module used -/

section

/-!
# A bitsliced round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
(scratch slot `keySlot`) into `r15`, advances the pointer by the step
(`stepSlot`), and does to the 64 state words what `roundW` does, with the
key's low 48 bits.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr)

/-! ## The round key -/

theorem keyLoad_ok {s : State} (h : Room s) (hkey : InRegions (s.rd ++ s.wr) (sl s keySlot) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .r15 = (s.mem.readW (sl s keySlot) 64).rotateRight 48 ∧
      sl s' keySlot = sl s keySlot + sl s stepSlot ∧
      (∀ x < 128, x ≠ keySlot → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  let kp := sl s keySlot
  let K := s.mem.readW kp 64
  let δ := sl s stepSlot
  let s₁ := s.setReg .rax kp
  obtain e₁ : exec (ld .rax keySlot) s = some s₁ := exec_ld h (by decide) .rax
  let s₂ := s₁.setReg .r15 K
  obtain e₂ : exec (.mov .r15 (.mem { base := .rax, disp := 0 })) s₁ = some s₂ := by
    obtain hea : s₁.ea { base := .rax, disp := 0 } = kp := by
      simp [State.ea, s₁, gpr_setReg]
    obtain hl : s₁.load64 kp = some K := by
      simp only [State.load64, s₁, rd_setReg, wr_setReg, mem_setReg, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  obtain h₂ : Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg]) (by simp [s₂, s₁, wr_setReg])
  obtain sl₂ : ∀ x, sl s₂ x = sl s x := by
    intro x; simp only [sl, s₂, s₁, mem_setReg, gpr_setReg]; rfl
  let s₃ := s₂.setReg .rdx δ
  obtain e₃ : exec (ld .rdx stepSlot) s₂ = some s₃ := by
    rw [exec_ld h₂ (by decide) .rdx, sl₂]
  let v := kp + δ
  let s₄ := (arithFlags s₃ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .rax v
  obtain e₄ : exec (.alu .add .rax (.reg .rdx)) s₃ = some s₄ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    obtain ha : s₃.gpr .rax = kp := by simp [s₃, s₂, s₁, gpr_setReg]
    obtain hd : s₃.gpr .rdx = δ := by simp [s₃, gpr_setReg]
    rw [ha, hd]
  obtain h₄ : Room s₄ := h₂.congr (by simp [s₄, s₃, s₂, s₁, gpr_setReg])
    (by simp [s₄, s₃, wr_setReg, wr_arithFlags])
  obtain e₅ := exec_st (r := Reg.rax) h₄ (by decide : keySlot < 128)
  let s₅ : State := { s₄ with mem := stMem s₄ keySlot (s₄.gpr .rax) }
  let s₆ := (s₅.setFlags (some ((s₅.gpr .r15).rotateRight 48).msb) none s₅.zf s₅.sf).setReg .r15
    ((s₅.gpr .r15).rotateRight 48)
  obtain e₆ : exec (.shift .ror .r15 48) s₅ = some s₆ := by
    simp only [exec, execShift]; rfl
  obtain rcx₄ : s₄.gpr .rcx = s.gpr .rcx := by simp [s₄, s₃, s₂, s₁, gpr_setReg]
  obtain mem₄ : s₄.mem = s.mem := by simp [s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  obtain rax₄ : s₄.gpr .rax = v := by simp [s₄, gpr_setReg]
  obtain sl₆ : ∀ x < 128, sl s₆ x = if x = keySlot then v else sl s x := by
    intro x hx
    simp only [sl, s₆, mem_setReg, mem_setFlags, gpr_setReg, gpr_setFlags]
    simp only [show ¬ Reg.rcx = Reg.r15 by decide, ite_false, s₅]
    rw [readW_stMem s₄ (by decide) _ hx, rax₄]
    simp only [sl, mem₄, rcx₄]
  refine ⟨s₆, ?_, ?_, ?_, fun x hx hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_nil]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_setReg, K, kp]
  · rw [sl₆ _ (by decide)]; simp; rfl
  · rw [sl₆ x hx]; simp [hne]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_setFlags, rd_arithFlags]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_setFlags, wr_arithFlags]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_setReg, gpr_setFlags]
  · simp [s₆, s₅, s₄, s₃, s₂, s₁, gpr_setReg, gpr_setFlags]
  · have f := stMem_frame (s := s₄) (by decide : keySlot < 128) (s₄.gpr .rax)
    rw [show scratchR s₄ = scratchR s by simp only [scratchR, rcx₄], mem₄] at f
    simpa [s₆, s₅, mem_setReg, mem_setFlags] using f

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
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
    (hr : s.gpr .r15 = K.rotateRight 48) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ (K.setWidth 48) n (words s) x) ∧
      (∀ x < 128, 72 ≤ x → sl s' x = sl s x) ∧ s'.gpr .r15 = K.rotateRight 48 <<< (6 * n) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ _ => rfl, by simp [hr], rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, hi₁, r₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := ih (by omega_using [hn])
    obtain h₁ := h.congr c₁ wr₁
    obtain ⟨s₂, run₂, w₂, hi₂, r₂, rd₂, wr₂, c₂, sp₂, f₂⟩ :=
      sboxStep_ok ρ (by omega_using [hn] : n < 8) h₁ (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact keyBits K (by omega_using [hn]) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, fun x hx hl => ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
      c₂.trans c₁, sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega_using [hn]) w₁ (w₁ x hx)
    · rw [hi₂ x hx hl, hi₁ x hx hl]
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega_using []]
    · rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (ρ : Role) : round ρ = keyLoad ++ stepsCode ρ 8 := rfl

theorem round_ok (ρ : Role) {s : State} (h : Room s)
    (hkey : InRegions (s.rd ++ s.wr) (sl s keySlot) 8) :
    ∃ s', runBlock isa (round ρ) s = some s' ∧
      (∀ x < 64, words s' x =
        roundW ρ ((s.mem.readW (sl s keySlot) 64).setWidth 48) (words s) x) ∧
      sl s' keySlot = sl s keySlot + sl s stepSlot ∧
      (∀ x < 128, 72 ≤ x → x ≠ keySlot → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, key₁, sl₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := keyLoad_ok h hkey
  obtain h₁ := h.congr c₁ wr₁
  obtain ⟨s₂, run₂, w₂, hi₂, -, rd₂, wr₂, c₂, sp₂, f₂⟩ := stepsCode_ok ρ _ (Nat.le_refl 8) h₁ r₁
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun x hx hl hne => ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    c₂.trans c₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact steps_congr ρ _ (Nat.le_refl 8)
      (fun y hy => sl₁ _ (by unfold stSlot; omega_using [hy]) (by unfold stSlot keySlot; omega_using [hy])) x hx
  · rw [hi₂ _ (by decide) (by decide), key₁]
  · rw [hi₂ x hx hl, sl₁ x hx hne]
  · rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
    exact f₁.trans f₂

end VG.Proof.TripleDes.X86_64.Bitsliced

end

end


/-!
# A bitsliced DES pass on the machine

A pass chooses its first key's address and the step between keys by the
pass count (`passStart`), runs eight pairs of rounds (the loop counts them in
`roundSlot`), exchanges the halves and counts the pass (`passEnd`).
`pass_ok`: it does to the state words what `swapW (pairs …)` does, with the
keys read at the addresses `a₀ + r δ`, which are apart from the scratch
buffer.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW partner)

/-- Eight readable bytes, apart from the scratch buffer. -/
structure Apart (s : State) (a : Addr) : Prop where
  read : InRegions (s.rd ++ s.wr) a 8
  scratch : (⟨a, 8⟩ : Region).Disjoint (scratchR s)

theorem Apart.congr {s s' : State} {a : Addr} (h : Apart s a) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Apart s' a where
  read := by rw [hrd, hwr]; exact h.read
  scratch := by simp only [scratchR, hc]; exact h.scratch

theorem Apart.readW {s : State} {a : Addr} (h : Apart s a) {m : Mem}
    (hf : Frame [scratchR s] s.mem m) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW (Region.contains_self a 8) (by simpa using h.scratch) (by decide)

/-! ## Counting down a slot -/

def decCode (k : Nat) : List Instr := [ld .rax k, .alu .sub .rax (.imm 1), st k .rax]

theorem decCode_ok {s : State} (h : Room s) {k : Nat} (hk : k < 128) :
    ∃ s', runBlock isa (decCode k) s = some s' ∧ sl s' k = sl s k - 1 ∧
      s'.zf = some (sl s k - 1 == 0) ∧ (∀ x < 128, x ≠ k → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  let v := sl s k
  let s₁ := s.setReg .rax v
  obtain e₁ : exec (ld .rax k) s = some s₁ := exec_ld h hk .rax
  let r := v - (1 : BitVec 32).signExtend 64
  let s₂ := (arithFlags s₁ r (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) r)).setReg .rax r
  obtain e₂ : exec (.alu .sub .rax (.imm 1)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    simp only [s₁, gpr_setReg_self]; rfl
  obtain h₂ : Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg])
    (by simp [s₂, s₁, wr_setReg, wr_arithFlags])
  obtain e₃ := exec_st (r := Reg.rax) h₂ hk
  have hr : r = v - 1 := rfl
  obtain rcx₂ : s₂.gpr .rcx = s.gpr .rcx := by simp [s₂, s₁, gpr_setReg]
  obtain mem₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  obtain sl₃ : ∀ x < 128, (stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) x) 64 =
      if x = k then v - 1 else sl s x := by
    intro x hx
    rw [readW_stMem s₂ hk _ hx]
    simp only [s₂, gpr_setReg_self, ← hr]
    rfl
  refine ⟨{ s₂ with mem := stMem s₂ k (s₂.gpr .rax) }, ?_, ?_, ?_, fun x hx hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [decCode, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · change (stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) k) 64 = _
    rw [sl₃ k hk]; simp; rfl
  · simp only [s₂, zf_setReg, zf_arithFlags]; rfl
  · change (stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) x) 64 = _
    rw [sl₃ x hx]; simp [hne]
  · simp [s₂, s₁, rd_setReg, rd_arithFlags]
  · simp [s₂, s₁, wr_setReg, wr_arithFlags]
  · exact rcx₂
  · simp [s₂, s₁, gpr_setReg]
  · have f := stMem_frame (s := s₂) hk (s₂.gpr .rax)
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, rcx₂], mem₂] at f
    exact f

/-! ## A pair of rounds -/

theorem roundW_congr {w : Nat} (ρ : Role) (k : BitVec 48) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, roundW ρ k W x = roundW ρ k W' x :=
  VG.Proof.TripleDes.Bitslice.steps_congr ρ k (Nat.le_refl 8) hW

theorem roundPair_eq : roundPair = round .ba ++ round .ab ++ decCode roundSlot := rfl

theorem roundPair_ok {s : State} (h : Room s) (h₁ : Apart s (sl s keySlot))
    (h₂ : Apart s (sl s keySlot + sl s stepSlot)) :
    ∃ s', runBlock isa roundPair s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (sl s keySlot + sl s stepSlot) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (sl s keySlot) 64).setWidth 48) (words s)) x) ∧
      sl s' keySlot = sl s keySlot + sl s stepSlot + sl s stepSlot ∧
      sl s' roundSlot = sl s roundSlot - 1 ∧ s'.zf = some (sl s roundSlot - 1 == 0) ∧
      (∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, key₁, misc₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := round_ok .ba h h₁.read
  obtain g₁ := h.congr c₁ wr₁
  obtain step₁ : sl s₁ stepSlot = sl s stepSlot := misc₁ _ (by decide) (by decide) (by decide)
  have hk₁ : sl s₁ keySlot = sl s keySlot + sl s stepSlot := key₁
  obtain a₂ : Apart s₁ (sl s₁ keySlot) := by rw [hk₁]; exact h₂.congr c₁ rd₁ wr₁
  obtain ⟨s₂, run₂, w₂, key₂, misc₂, rd₂, wr₂, c₂, sp₂, f₂⟩ := round_ok .ab g₁ a₂.read
  obtain g₂ := g₁.congr c₂ wr₂
  obtain ⟨s₃, run₃, cnt₃, zf₃, sl₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := decCode_ok g₂ (by decide : roundSlot < 128)
  obtain kread : s₁.mem.readW (sl s keySlot + sl s stepSlot) 64 =
      s.mem.readW (sl s keySlot + sl s stepSlot) 64 := h₂.readW f₁
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, ?_, fun x hx hlo hk hr => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), c₃.trans (c₂.trans c₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [roundPair_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · simp only [words]
    rw [sl₃ _ (by unfold stSlot; omega_using [hx]) (by unfold stSlot roundSlot; omega_using [hx])]
    rw [show sl s₂ (stSlot x) = words s₂ x from rfl, w₂ x hx, hk₁, kread]
    exact roundW_congr .ab _ w₁ x hx
  · rw [sl₃ keySlot (by decide) (by decide), key₂, hk₁, step₁]
  · rw [cnt₃, misc₂ _ (by decide) (by decide) (by decide), misc₁ _ (by decide) (by decide) (by decide)]
  · rw [zf₃, misc₂ _ (by decide) (by decide) (by decide), misc₁ _ (by decide) (by decide) (by decide)]
  · rw [sl₃ x hx hr, misc₂ x hx hlo hk, misc₁ x hx hlo hk]
  · rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, c₂, c₁]] at f₃
    exact f₁.trans (f₂.trans f₃)

/-! ## The loop of pairs of rounds -/

theorem cnt_sub (m : Nat) (h : 1 ≤ m) : BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  have e : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  rw [e, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h]

/-- The keys of a pass: the low 48 bits of the words at `a₀ + r δ`. -/
def keyAt (m : Mem) (a₀ δ : Addr) (r : Nat) : BitVec 48 :=
  (m.readW (a₀ + BitVec.ofNat 64 r * δ) 64).setWidth 48

theorem kptr_succ (a₀ δ : Addr) (r : Nat) :
    a₀ + BitVec.ofNat 64 r * δ + δ = a₀ + BitVec.ofNat 64 (r + 1) * δ := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul]
  simp

theorem pairs_congr {w : Nat} (key : Nat → BitVec 48) (n : Nat) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, pairs key n W x = pairs key n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ ih) x hx

structure LoopInv (s₀ : State) (m : Nat) (s : State) : Prop where
  room : Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, words s x = pairs (keyAt s₀.mem (sl s₀ keySlot) (sl s₀ stepSlot)) (8 - m) (words s₀) x
  key : sl s keySlot = sl s₀ keySlot + BitVec.ofNat 64 (2 * (8 - m)) * sl s₀ stepSlot
  cnt : sl s roundSlot = BitVec.ofNat 64 m
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s x = sl s₀ x
  frame : Frame [scratchR s₀] s₀.mem s.mem

structure LoopPost (s₀ s : State) : Prop where
  room : Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = pairs (keyAt s₀.mem (sl s₀ keySlot) (sl s₀ stepSlot)) 8 (words s₀) x
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s x = sl s₀ x
  frame : Frame [scratchR s₀] s₀.mem s.mem

theorem pairLoop_ok {s₀ : State} (hk : ∀ r < 16,
      Apart s₀ (sl s₀ keySlot + BitVec.ofNat 64 r * sl s₀ stepSlot))
    (m₀ : Nat) (s₁ : State) (hs₁ : LoopInv s₀ m₀ s₁) :
    WP isa (.loop (.block roundPair) .ne) s₁ (LoopPost s₀) := by
  refine WP.loop (M := isa) (LoopInv s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let a₀ := sl s₀ keySlot
  let δ := sl s₀ stepSlot
  obtain hδ : sl s stepSlot = δ := hs.misc _ (by decide) (by decide) (by decide) (by decide)
  obtain n16 : 2 * (8 - m) + 1 < 16 := by have := hs.pos; omega_using [this]
  obtain a₁ : Apart s (sl s keySlot) := by
    rw [hs.key]; exact (hk _ (by omega_using [n16])).congr hs.rcx hs.rd hs.wr
  obtain a₂ : Apart s (sl s keySlot + sl s stepSlot) := by
    rw [hs.key, hδ, kptr_succ]; exact (hk _ n16).congr hs.rcx hs.rd hs.wr
  obtain ⟨s', run', w', key', cnt', zf', misc', rd', wr', c', sp', f'⟩ := roundPair_ok hs.room a₁ a₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  obtain frame' : Frame [scratchR s₀] s₀.mem s'.mem := by
    have := hs.frame
    rw [show scratchR s = scratchR s₀ by simp only [scratchR, hs.rcx]] at f'
    exact this.trans f'
  obtain k1 : (s.mem.readW (sl s keySlot) 64).setWidth 48 =
      keyAt s₀.mem a₀ δ (2 * (8 - m)) := by
    rw [hs.key]; simp only [keyAt]
    rw [((hk _ (by omega_using [n16])).readW hs.frame)]
  obtain k2 : (s.mem.readW (sl s keySlot + sl s stepSlot) 64).setWidth 48 =
      keyAt s₀.mem a₀ δ (2 * (8 - m) + 1) := by
    rw [hs.key, hδ, kptr_succ]; simp only [keyAt]
    rw [((hk _ n16).readW hs.frame)]
  obtain words' : ∀ x < 64, words s' x = pairs (keyAt s₀.mem a₀ δ) (8 - m + 1) (words s₀) x := by
    intro x hx
    rw [w' x hx, k1, k2]
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ hs.words) x hx
  obtain misc'' : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s' x = sl s₀ x :=
    fun x hx hlo hk hr => (misc' x hx hlo hk hr).trans (hs.misc x hx hlo hk hr)
  obtain room' := hs.room.congr c' wr'
  obtain cntv : sl s roundSlot - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [hs.cnt]
    exact cnt_sub m hs.pos
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', c'.trans hs.rcx, sp'.trans hs.rsp, rd'.trans hs.rd, wr'.trans hs.wr,
      words', misc'', frame'⟩⟩
    show s'.zf.map (!·) = some false
    rw [zf', cntv]; rfl
  · right
    refine ⟨?_, m - 1, by omega_using [n16], ⟨room', c'.trans hs.rcx, sp'.trans hs.rsp, rd'.trans hs.rd,
      wr'.trans hs.wr, by omega_using [n16, h1], by have := hs.le; omega_using [this], ?_, ?_, ?_, misc'', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf', cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        have hm : m ≤ 8 := hs.le
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega_using [hm])] at this
        have := hs.pos
        omega_arith
      rw [this]; rfl
    · have e : 8 - (m - 1) = 8 - m + 1 := by have := hs.le; omega_using [n16, this]
      rw [e]; exact words'
    · rw [key', hs.key, hδ, kptr_succ, kptr_succ]
      congr 3
      have := hs.le; omega_using [n16, this]
    · rw [cnt', cntv]

/-! ## The start of a pass -/

/-- Point at a pass's first key (`a` past the schedule), with step `b`. -/
theorem passKeyCode_ok {s : State} (h : Room s) (a b : BitVec 32) :
    ∃ s', runBlock isa [ld .rdx schedSlot, .alu .add .rdx (.imm a), st keySlot .rdx,
        .mov .rdx (.imm b), st stepSlot .rdx] s = some s' ∧
      sl s' keySlot = sl s schedSlot + a.signExtend 64 ∧ sl s' stepSlot = b.signExtend 64 ∧
      (∀ x < 128, x ≠ keySlot → x ≠ stepSlot → sl s' x = sl s x) ∧ s'.gpr .rax = s.gpr .rax ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  let v := sl s schedSlot
  let s₁ := s.setReg .rdx v
  obtain e₁ : exec (ld .rdx schedSlot) s = some s₁ := exec_ld h (by decide) .rdx
  obtain e₂ := exec_addImm s₁ .rdx a
  let w := s₁.gpr .rdx + a.signExtend 64
  let s₂ := (arithFlags s₁ w (decide (2 ^ 64 ≤ (s₁.gpr .rdx).toNat + (a.signExtend 64).toNat))
      (addOverflow (s₁.gpr .rdx) (a.signExtend 64) w)).setReg .rdx w
  obtain h₂ : Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg]) (by simp [s₂, s₁, wr_setReg, wr_arithFlags])
  obtain e₃ := exec_st (r := Reg.rdx) h₂ (by decide : keySlot < 128)
  let s₃ : State := { s₂ with mem := stMem s₂ keySlot (s₂.gpr .rdx) }
  obtain e₄ := exec_movImm s₃ .rdx b
  let s₄ := s₃.setReg .rdx (b.signExtend 64)
  obtain h₄ : Room s₄ := h₂.congr (by simp [s₄, s₃, gpr_setReg]) (by simp [s₄, s₃, wr_setReg])
  obtain e₅ := exec_st (r := Reg.rdx) h₄ (by decide : stepSlot < 128)
  let s₅ : State := { s₄ with mem := stMem s₄ stepSlot (s₄.gpr .rdx) }
  obtain c₂ : s₂.gpr .rcx = s.gpr .rcx := by simp [s₂, s₁, gpr_setReg]
  obtain m₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  obtain sl₅ : ∀ x < 128, sl s₅ x = if x = stepSlot then b.signExtend 64 else
      if x = keySlot then v + a.signExtend 64 else sl s x := by
    intro x hx
    obtain a₅ := sl_st s₄ (by decide : stepSlot < 128) (s₄.gpr .rdx) hx
    obtain a₃ := sl_st s₂ (by decide : keySlot < 128) (s₂.gpr .rdx) hx
    change sl { s₄ with mem := stMem s₄ stepSlot (s₄.gpr .rdx) } x = _
    rw [a₅]
    simp only [s₄, sl_setReg _ (by decide : Reg.rdx ≠ .rcx), gpr_setReg_self]
    split
    · rfl
    · change sl { s₂ with mem := stMem s₂ keySlot (s₂.gpr .rdx) } x = _
      rw [a₃]
      split
      · simp [s₂, s₁, gpr_setReg, w, v]
      · simp only [sl, m₂, c₂]
  refine ⟨s₅, ?_, ?_, ?_, fun x hx a b => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · rw [sl₅ _ (by decide)]; rfl
  · rw [sl₅ _ (by decide)]; rfl
  · rw [sl₅ x hx]; simp [a, b]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  · simp [s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  · simp [s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  · have f₃ := stMem_frame (s := s₂) (by decide : keySlot < 128) (s₂.gpr .rdx)
    obtain f₅ := stMem_frame (s := s₄) (by decide : stepSlot < 128) (s₄.gpr .rdx)
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, c₂], m₂] at f₃
    rw [show scratchR s₄ = scratchR s by simp [scratchR, s₄, s₃, gpr_setReg, c₂]] at f₅
    exact f₃.trans f₅

/-- The comparison of `rax` with an immediate. -/
theorem cmp_run (s : State) (v : BitVec 32) :
    runBlock isa [.alu .cmp .rax (.imm v)] s = some (arithFlags s (s.gpr .rax - v.signExtend 64)
      (decide ((s.gpr .rax).toNat < (v.signExtend 64).toNat))
      (subOverflow (s.gpr .rax) (v.signExtend 64) (s.gpr .rax - v.signExtend 64))) := by
  rw [runBlock_cons]
  rfl

/-- What the start of a pass leaves. -/
structure StartPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  room : Room s'
  key : sl s' keySlot = sl s schedSlot + BitVec.ofNat 64 (passKey d p).1
  step : sl s' stepSlot = BitVec.ofInt 64 (passKey d p).2
  round : sl s' roundSlot = 8
  misc : ∀ x < 128, x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → sl s' x = sl s x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame [scratchR s] s.mem s'.mem

theorem passKey_imm : ∀ d : Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 →
    (BitVec.ofNat 32 (passKey d p).1).signExtend 64 = BitVec.ofNat 64 (passKey d p).1 ∧
    (BitVec.ofInt 32 (passKey d p).2).signExtend 64 = BitVec.ofInt 64 (passKey d p).2 := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

theorem passStart_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (h : Room s) (hc : sl s passSlot = BitVec.ofNat 64 p) :
    WP isa (passStart d) s (StartPost d p s) := by
  -- the code of a branch, and what follows it
  obtain branch : ∀ (s₁ : State), Room s₁ → (∀ x < 128, sl s₁ x = sl s x) → s₁.gpr .rcx = s.gpr .rcx →
      s₁.gpr .rsp = s.gpr .rsp → s₁.rd = s.rd → s₁.wr = s.wr → Frame [scratchR s] s.mem s₁.mem →
      WP isa (.block (passKeyCode d p)) s₁ (fun s₂ =>
        WP isa (.block [.mov .rax (.imm 8), st roundSlot .rax]) s₂ (StartPost d p s)) := by
    intro s₁ h₁ sl₁ c₁ sp₁ rd₁ wr₁ f₁
    obtain ⟨s₂, run₂, key₂, step₂, misc₂, -, rd₂, wr₂, c₂, sp₂, f₂⟩ :=
      passKeyCode_ok h₁ (BitVec.ofNat 32 (passKey d p).1) (BitVec.ofInt 32 (passKey d p).2)
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    obtain h₂ := h₁.congr c₂ wr₂
    obtain e₃ := exec_movImm s₂ .rax 8
    let s₃ := s₂.setReg .rax ((8 : BitVec 32).signExtend 64)
    obtain h₃ : Room s₃ := h₂.congr (by simp [s₃, gpr_setReg]) (by simp [s₃, wr_setReg])
    obtain e₄ := exec_st (r := Reg.rax) h₃ (by decide : roundSlot < 128)
    refine WP.of_runBlock ⟨{ s₃ with mem := stMem s₃ roundSlot (s₃.gpr .rax) }, ?_, ?_⟩
    · rw [runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil]
    obtain sl₄ : ∀ x < 128, sl { s₃ with mem := stMem s₃ roundSlot (s₃.gpr .rax) } x =
        if x = roundSlot then 8 else sl s₂ x := by
      intro x hx
      rw [sl_st s₃ (by decide) _ hx]
      simp only [s₃, sl_setReg _ (by decide : Reg.rax ≠ .rcx), gpr_setReg_self]
      split <;> rfl
    obtain ⟨i1, i2⟩ := passKey_imm d p hp.1 hp.2
    refine ⟨h₃.congr rfl rfl, ?_, ?_, ?_, fun x hx a b c => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sl₄ _ (by decide)]; simp only [show keySlot ≠ roundSlot by decide, ite_false]
      rw [key₂, sl₁ _ (by decide), i1]
    · rw [sl₄ _ (by decide)]; simp only [show stepSlot ≠ roundSlot by decide, ite_false]
      rw [step₂, i2]
    · rw [sl₄ _ (by decide)]; rfl
    · rw [sl₄ x hx]; simp only [c, ite_false]; rw [misc₂ x hx a b, sl₁ x hx]
    · simp [s₃, rd_setReg, rd₂, rd₁]
    · simp [s₃, wr_setReg, wr₂, wr₁]
    · simp [s₃, gpr_setReg, c₂, c₁]
    · simp [s₃, gpr_setReg, sp₂, sp₁]
    · have f := stMem_frame (s := s₃) (by decide : roundSlot < 128) (s₃.gpr .rax)
      rw [show scratchR s₃ = scratchR s by simp [scratchR, s₃, gpr_setReg, c₂, c₁]] at f
      rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
      exact f₁.trans (f₂.trans f)
  -- load the count and compare it with 3
  let s₁ := s.setReg .rax (BitVec.ofNat 64 p)
  obtain e₁ : exec (ld .rax passSlot) s = some s₁ := by rw [exec_ld h (by decide) .rax, hc]
  let t₁ := arithFlags s₁ (s₁.gpr .rax - (3 : BitVec 32).signExtend 64)
    (decide ((s₁.gpr .rax).toNat < ((3 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₁.gpr .rax) ((3 : BitVec 32).signExtend 64) (s₁.gpr .rax - (3 : BitVec 32).signExtend 64))
  obtain hrun₁ : runBlock isa [ld .rax passSlot, .alu .cmp .rax (.imm 3)] s = some t₁ := by
    rw [runBlock_cons, e₁, runStep_some, cmp_run]
  obtain ht₁ : Room t₁ := h.congr (by simp [t₁, s₁, gpr_setReg])
    (by simp [t₁, s₁, wr_setReg, wr_arithFlags])
  obtain sl₁ : ∀ x < 128, sl t₁ x = sl s x := by
    intro x _; simp only [t₁, sl_arithFlags, s₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx)]
  obtain c₁ : t₁.gpr .rcx = s.gpr .rcx := by simp [t₁, s₁, gpr_setReg]
  obtain sp₁ : t₁.gpr .rsp = s.gpr .rsp := by simp [t₁, s₁, gpr_setReg]
  obtain rd₁ : t₁.rd = s.rd := by simp [t₁, s₁, rd_setReg, rd_arithFlags]
  obtain wr₁ : t₁.wr = s.wr := by simp [t₁, s₁, wr_setReg, wr_arithFlags]
  obtain f₁ : Frame [scratchR s] s.mem t₁.mem := by
    simp only [t₁, s₁, mem_setReg, mem_arithFlags]; exact Frame.refl _ _
  obtain rax₁ : t₁.gpr .rax = BitVec.ofNat 64 p := by simp [t₁, s₁, gpr_setReg]
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, hrun₁, ?_⟩
  apply WP.seq
  obtain zf₁ : isa.eval .e t₁ = some (p == 3) := by
    show t₁.zf = _
    simp only [t₁, zf_arithFlags, s₁, gpr_setReg_self]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    have : p = 3 := by simpa using h3
    subst this
    exact branch t₁ ht₁ sl₁ c₁ sp₁ rd₁ wr₁ f₁
  · intro h3
    obtain hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := arithFlags t₁ (t₁.gpr .rax - (2 : BitVec 32).signExtend 64)
      (decide ((t₁.gpr .rax).toNat < ((2 : BitVec 32).signExtend 64).toNat))
      (subOverflow (t₁.gpr .rax) ((2 : BitVec 32).signExtend 64) (t₁.gpr .rax - (2 : BitVec 32).signExtend 64))
    refine WP.of_runBlock ⟨t₂, cmp_run t₁ 2, ?_⟩
    obtain ht₂ : Room t₂ := ht₁.congr (by simp [t₂]) (by simp [t₂, wr_arithFlags])
    obtain zf₂ : isa.eval .e t₂ = some (p == 2) := by
      show t₂.zf = _
      simp only [t₂, zf_arithFlags, rax₁]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    obtain sl₂ : ∀ x < 128, sl t₂ x = sl s x := fun x hx => by simp only [t₂, sl_arithFlags]; exact sl₁ x hx
    obtain c₂ : t₂.gpr .rcx = s.gpr .rcx := by simp only [t₂, gpr_arithFlags, c₁]
    obtain sp₂ : t₂.gpr .rsp = s.gpr .rsp := by simp only [t₂, gpr_arithFlags, sp₁]
    obtain rd₂ : t₂.rd = s.rd := by simp only [t₂, rd_arithFlags, rd₁]
    obtain wr₂ : t₂.wr = s.wr := by simp only [t₂, wr_arithFlags, wr₁]
    obtain f₂ : Frame [scratchR s] s.mem t₂.mem := by simp only [t₂, mem_arithFlags]; exact f₁
    apply WP.ite (p == 2) zf₂
    · intro h2
      have : p = 2 := by simpa using h2
      subst this
      exact branch t₂ ht₂ sl₂ c₂ sp₂ rd₂ wr₂ f₂
    · intro h2
      have : p = 1 := by have : p ≠ 2 := by simpa using h2
                         omega_using [hp, hp3, this]
      subst this
      exact branch t₂ ht₂ sl₂ c₂ sp₂ rd₂ wr₂ f₂

/-! ## A pass -/

theorem passEnd_eq : passEnd = decCode passSlot := rfl

theorem pairs_keys_congr {w : Nat} {key key' : Nat → BitVec 48} (n : Nat)
    (hk : ∀ r < 2 * n, key r = key' r) (W : Nat → BitVec w) : pairs key n W = pairs key' n W := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairs]
    rw [ih (fun r hr => hk r (by omega_using [hr])), hk (2 * n) (by omega_using []), hk (2 * n + 1) (by omega_using [])]

theorem partner_lt : ∀ k < 128, ∀ y, partner k = some y → y < 64 := by
  intro k hk y h
  obtain key : ∀ k < 128, (partner k).all (· < 64) = true := by lit_decide
  have := key k hk
  rw [h] at this
  simpa using this

theorem swapW_congr {w : Nat} {W W' : Nat → BitVec w} (hW : ∀ y < 64, W y = W' y) :
    ∀ x < 64, swapW W x = swapW W' x := by
  intro x hx
  simp only [swapW]
  rcases hp : partner x with _ | y
  · exact hW x hx
  · exact hW y (partner_lt x (by omega_using [hx]) y hp)

/-- The first key of pass `p` (counted down from 3) and its step. -/
def passA (d : Spec.TripleDes.Direction) (p : Nat) (sched : Addr) : Addr :=
  sched + BitVec.ofNat 64 (passKey d p).1
def passD (d : Spec.TripleDes.Direction) (p : Nat) : Addr := BitVec.ofInt 64 (passKey d p).2

structure PassPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  room : Room s'
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  words : ∀ x < 64, words s' x =
    swapW (pairs (keyAt s.mem (passA d p (sl s schedSlot)) (passD d p)) 8 (words s)) x
  count : sl s' passSlot = sl s passSlot - 1
  zf : s'.zf = some (sl s passSlot - 1 == 0)
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    sl s' x = sl s x
  frame : Frame [scratchR s] s.mem s'.mem

theorem pass_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (h : Room s) (hc : sl s passSlot = BitVec.ofNat 64 p)
    (hk : ∀ r < 16, Apart s (passA d p (sl s schedSlot) + BitVec.ofNat 64 r * passD d p)) :
    WP isa (pass d) s (PassPost d p s) := by
  apply WP.seq
  apply WP.mono (passStart_ok d hp h hc)
  intro s₁ p₁
  have h₁ := p₁.room
  apply WP.seq
  obtain hk₁ : ∀ r < 16, Apart s₁ (sl s₁ keySlot + BitVec.ofNat 64 r * sl s₁ stepSlot) := by
    intro r hr
    rw [p₁.key, p₁.step]; exact (hk r hr).congr p₁.rcx p₁.rd p₁.wr
  obtain inv : LoopInv s₁ 8 s₁ := by
    refine ⟨h₁, rfl, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl, ?_, ?_,
      fun _ _ _ _ _ => rfl, Frame.refl _ _⟩
    · simp
    · rw [p₁.round]; rfl
  apply WP.mono (pairLoop_ok hk₁ 8 s₁ inv)
  intro s₂ p₂
  have h₂ := p₂.room
  obtain ⟨s₃, run₃, sw₃, hi₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := swapHalves_ok h₂
  obtain h₃ := h₂.congr c₃ wr₃
  obtain ⟨s₄, run₄, cnt₄, zf₄, misc₄, rd₄, wr₄, c₄, sp₄, f₄⟩ := decCode_ok h₃ (by decide : passSlot < 128)
  refine WP.of_runBlock ⟨s₄, by rw [passEnd_eq]; exact runBlock_cat_some run₃ run₄, ?_⟩
  obtain keys : ∀ r < 16, keyAt s₁.mem (sl s₁ keySlot) (sl s₁ stepSlot) r =
      keyAt s.mem (passA d p (sl s schedSlot)) (passD d p) r := by
    intro r hr
    simp only [keyAt, p₁.key, p₁.step]
    obtain e := (hk r hr).readW p₁.frame
    simp only [passA, passD] at e
    rw [e]; rfl
  obtain state₁ : ∀ x < 64, words s₁ x = words s x := fun x hx =>
    p₁.misc _ (by unfold stSlot; omega_using [hx]) (by unfold stSlot keySlot; omega_using [hx])
      (by unfold stSlot stepSlot; omega_using [hx]) (by unfold stSlot roundSlot; omega_using [hx])
  obtain high : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → x ≠ passSlot →
      sl s₄ x = sl s₁ x := by
    intro x hx hlo hkx hrx hpx
    rw [misc₄ x hx hpx, hi₃ x hx hlo, p₂.misc x hx hlo hkx hrx]
  obtain pass₁ : sl s₁ passSlot = sl s passSlot := p₁.misc _ (by decide) (by decide) (by decide) (by decide)
  obtain pass₃ : sl s₃ passSlot = sl s passSlot := by
    rw [hi₃ _ (by decide) (by decide), p₂.misc _ (by decide) (by decide) (by decide) (by decide), pass₁]
  refine ⟨h₃.congr c₄ wr₄, c₄.trans (c₃.trans (p₂.rcx.trans p₁.rcx)),
    sp₄.trans (sp₃.trans (p₂.rsp.trans p₁.rsp)), rd₄.trans (rd₃.trans (p₂.rd.trans p₁.rd)),
    wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr)), fun x hx => ?_, ?_, ?_,
    fun x hx hlo a b c e => ?_, ?_⟩
  · simp only [words]
    rw [misc₄ _ (by unfold stSlot; omega_using [hx]) (by unfold stSlot passSlot; omega_using [hx])]
    rw [show sl s₃ (stSlot x) = words s₃ x from rfl, sw₃ x hx]
    apply swapW_congr _ x hx
    intro y hy
    rw [p₂.words y hy, pairs_keys_congr 8 (fun r hr => keys r (by omega_using [hr]))]
    exact pairs_congr _ 8 state₁ y hy
  · rw [cnt₄, pass₃]
  · rw [zf₄, pass₃]
  · rw [high x hx hlo a c e]
    exact p₁.misc x hx a b c
  · have g₃ : Frame [scratchR s] s₂.mem s₃.mem := by
      rwa [show scratchR s₂ = scratchR s by simp only [scratchR, p₂.rcx, p₁.rcx]] at f₃
    obtain g₄ : Frame [scratchR s] s₃.mem s₄.mem := by
      rwa [show scratchR s₃ = scratchR s by simp only [scratchR, c₃, p₂.rcx, p₁.rcx]] at f₄
    have g₂ := p₂.frame
    rw [show scratchR s₁ = scratchR s by simp only [scratchR, p₁.rcx]] at g₂
    exact p₁.frame.trans (g₂.trans (g₃.trans g₄))

end VG.Proof.TripleDes.X86_64.Bitsliced
