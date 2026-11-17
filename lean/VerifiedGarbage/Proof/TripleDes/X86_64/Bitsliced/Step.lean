module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables

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
