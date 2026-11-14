module

public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.X86_64.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Exec

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
