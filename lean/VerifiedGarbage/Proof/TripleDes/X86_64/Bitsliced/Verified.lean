import VerifiedGarbage.Impl.TripleDes.X86_64.Bitsliced
import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit`. -/
section

/-! # The bitsliced S-box circuits' code, as literals -/

namespace VG.Impl.TripleDes.X86_64.Bitslice

open VG.X86_64

-- The circuits' code, once, which the literals below and the functions'
-- literals (`Lit`) read rather than run the register allocator again.
materialize_table VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 8

-- The transposition, once.
materialize_value transpose

-- A pair of rounds and the exchange of the halves, once for both directions.
materialize_value roundPair
materialize_value VG.Impl.TripleDes.X86_64.Bitslice.swapHalves

def sbox0 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 0)
def sbox1 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 1)
def sbox2 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 2)
def sbox3 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 3)
def sbox4 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 4)
def sbox5 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 5)
def sbox6 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 6)
def sbox7 : Prog isa := .block (VG.Impl.TripleDes.X86_64.Bitslice.sboxCode 7)

materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox0
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox1
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox2
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox3
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox4
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox5
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox6
materialize_code VG.Impl.TripleDes.X86_64.Bitslice.sbox7

def transposeProg : Prog isa := .block transpose

materialize_code VG.Impl.TripleDes.X86_64.Bitslice.transposeProg

end VG.Impl.TripleDes.X86_64.Bitslice

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Sbox`. -/
section

/-!
# The bitsliced S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs, and
the truth-table evaluator lifts that check to every bit position of
arbitrary 64-bit words, as for the scalar code (`../Sbox.lean`). The
circuits spill to the scratch buffer (`[rcx + 8k]`, `k < spills`) and leave
`rcx`, `rsp` and `r15` (the round key) alone.
-/

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
    VG.X86_64.Straight.check (table 64 64) VG.Proof.TripleDes.X86_64.Bitsliced.sboxCfg (fun _ => none) (instrs (VG.Proof.TripleDes.X86_64.Bitsliced.sboxLiteral j))
      VG.Proof.TripleDes.X86_64.Bitsliced.sboxEnv (VG.Proof.TripleDes.X86_64.Bitsliced.sboxPost j) = true := by
  decide +kernel

theorem sboxLiteral_eq : ∀ j < 8, VG.Proof.TripleDes.X86_64.Bitsliced.sboxLiteral j = .block (sboxCode j)
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
    (instrs (VG.Proof.TripleDes.X86_64.Bitsliced.sboxLiteral j)).all (fun op => op.dst != some .r15) = true := by
  decide +kernel

/-- Bit `p` of each input register, as the S-box's input. -/
def inputAt (s : VG.X86_64.State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.gpr (inReg i)).getLsbD p

theorem inputAt_bit (s : VG.X86_64.State) (p k : Nat) (hk : k < 6) :
    (VG.Proof.TripleDes.X86_64.Bitsliced.inputAt s p).toNat.testBit k = (s.gpr (inReg k)).getLsbD p := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem inReg_inj : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- Every S-box output bit, for arbitrary input words and spill slots. Only
the spill slots change in memory, and `rcx`, `rsp` and `r15` are left alone. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : VG.X86_64.State} (hok : Ok VG.Proof.TripleDes.X86_64.Bitsliced.sboxCfg s) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ p < 64, (s'.gpr (outReg i)).getLsbD p =
        (Spec.TripleDes.sBox j (VG.Proof.TripleDes.X86_64.Bitsliced.inputAt s p)).getLsbD i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r15 = s.gpr .r15 ∧ VG.Frame [slotRegion VG.Proof.TripleDes.X86_64.Bitsliced.sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (VG.Proof.TripleDes.X86_64.Bitsliced.sboxLiteral j) = sboxCode j := by rw [VG.Proof.TripleDes.X86_64.Bitsliced.sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (VG.Proof.TripleDes.X86_64.Bitsliced.sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (TableRel p (VG.Proof.TripleDes.X86_64.Bitsliced.inputAt s p).toNat) VG.Proof.TripleDes.X86_64.Bitsliced.sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode j).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (VG.Proof.TripleDes.X86_64.Bitsliced.inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩ he
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      VG.Proof.TripleDes.X86_64.Bitsliced.inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun i hi p hp => ?_, p₀.rd, p₀.wr, p₀.base, p₀.ext, p₀.other .r15 (by
    have h := VG.Proof.TripleDes.X86_64.Bitsliced.sbox_preserves j hj
    rw [codeEq] at h
    simp [h]), p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key p hp
  obtain rfl := run_unique hs'' hs'
  have h := p₁.rel.reg (outReg i) _ (hout i hi)
  simp only [TableRel, outputTable, testBit_tableOf, (VG.Proof.TripleDes.X86_64.Bitsliced.inputAt s p).isLt,
    decide_true, Bool.true_and] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Machine`. -/
section

/-!
# The machine state of the bitsliced ECB code

The code keeps its state in the 128 slots of the scratch buffer (`rcx`,
`sl s j`) and in the stack frame (`rsp`). `Room` says that both are
writable and apart. Blocks that only move and XOR words between registers
and scratch slots are checked by evaluation over the variable domain
(`Bitslice.vars`): `varsRun` runs one, its variables being the scratch
slots (variable `k < 128`) and some registers (variable `128 + i`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice

/-- Scratch slot `j`. -/
def sl (s : VG.X86_64.State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .rcx) j) 64

/-- The 64 state words. -/
def words (s : VG.X86_64.State) : Nat → BitVec 64 := fun j => VG.Proof.TripleDes.X86_64.Bitsliced.sl s (stSlot j)

def scratchR (s : VG.X86_64.State) : Region := ⟨s.gpr .rcx, 1024⟩
/-- The spill slots, at the start of the scratch buffer. -/
def spillR (s : VG.X86_64.State) : Region := ⟨s.gpr .rcx, 8 * spills⟩

/-- The scratch buffer is writable. -/
structure Room (s : VG.X86_64.State) : Prop where
  scratch : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s ∈ s.wr

theorem Room.congr {s s' : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hw : s'.wr = s.wr) : VG.Proof.TripleDes.X86_64.Bitsliced.Room s' where
  scratch := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, hc, hw]; exact h.scratch

theorem slot_in_scratch (s : VG.X86_64.State) {j : Nat} (hj : j < 128) :
    (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s).Contains (wordAddr (s.gpr .rcx) j) (64 / 8) :=
  slot_contains (s.gpr .rcx) (n := 128) hj (by decide)

/-- Writes to the spill slots alone leave the other scratch slots. -/
theorem sl_of_spill {s s' : VG.X86_64.State} (hc : s'.gpr .rcx = s.gpr .rcx)
    (hf : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.spillR s] s.mem s'.mem) {j : Nat} (hj : spills ≤ j) (hj' : j < 128) :
    VG.Proof.TripleDes.X86_64.Bitsliced.sl s' j = VG.Proof.TripleDes.X86_64.Bitsliced.sl s j := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, hc]
  refine hf.readW (r := ⟨wordAddr (s.gpr .rcx) j, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base (s.gpr .rcx) (d := 8 * j) (n := 8) (k := 8 * spills)
    (by unfold spills at hj ⊢; omega) (by omega)

theorem spill_sub (s : VG.X86_64.State) : Region.Sub (VG.Proof.TripleDes.X86_64.Bitsliced.spillR s) (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s) := Region.sub_prefix (by decide)

theorem spill_toScratch {s : VG.X86_64.State} {m m' : Mem} (h : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.spillR s] m m') :
    VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, List.mem_singleton_self _, VG.Proof.TripleDes.X86_64.Bitsliced.spill_sub s⟩

/-! ## Loads and stores of scratch slots -/

theorem ea_at (s : VG.X86_64.State) (k : Nat) : s.ea (at_ k) = wordAddr (s.gpr .rcx) k := rfl

theorem slot_writable {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : k < 128) :
    InRegions s.wr (wordAddr (s.gpr .rcx) k) 8 :=
  ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, h.scratch, VG.Proof.TripleDes.X86_64.Bitsliced.slot_in_scratch s hk⟩

theorem slot_readable {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : k < 128) :
    InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .rcx) k) 8 :=
  ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, List.mem_append_right _ h.scratch, VG.Proof.TripleDes.X86_64.Bitsliced.slot_in_scratch s hk⟩

theorem exec_ld {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : k < 128) (r : Reg) :
    exec (ld r k) s = some (s.setReg r (VG.Proof.TripleDes.X86_64.Bitsliced.sl s k)) := by
  simp only [ld, exec, readSrc, State.load64, VG.Proof.TripleDes.X86_64.Bitsliced.ea_at, VG.Proof.TripleDes.X86_64.Bitsliced.slot_readable h hk, ite_true,
    Option.map_some, VG.Proof.TripleDes.X86_64.Bitsliced.sl]

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : VG.X86_64.State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .rcx) k) v

theorem exec_st {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : k < 128) (r : Reg) :
    exec (st k r) s = some { s with mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s k (s.gpr r) } := by
  simp only [st, exec, State.store64, VG.Proof.TripleDes.X86_64.Bitsliced.ea_at, VG.Proof.TripleDes.X86_64.Bitsliced.slot_writable h hk, ite_true, VG.Proof.TripleDes.X86_64.Bitsliced.stMem]

theorem readW_stMem (s : VG.X86_64.State) {k : Nat} (hk : k < 128) (v : BitVec 64) {j : Nat} (hj : j < 128) :
    (VG.Proof.TripleDes.X86_64.Bitsliced.stMem s k v).readW (wordAddr (s.gpr .rcx) j) 64 = if j = k then v else VG.Proof.TripleDes.X86_64.Bitsliced.sl s j := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)]
    rfl

theorem stMem_frame {s : VG.X86_64.State} {k : Nat} (hk : k < 128) (v : BitVec 64) :
    VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (VG.Proof.TripleDes.X86_64.Bitsliced.slot_in_scratch s hk)

theorem sl_setReg (s : VG.X86_64.State) {r : Reg} (hr : r ≠ .rcx) (v : BitVec 64) (j : Nat) :
    VG.Proof.TripleDes.X86_64.Bitsliced.sl (s.setReg r v) j = VG.Proof.TripleDes.X86_64.Bitsliced.sl s j := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, mem_setReg, gpr_setReg_of_ne (s := s) v (Ne.symm hr)]

theorem sl_arithFlags {w : Nat} (s : VG.X86_64.State) (x : BitVec w) (c o : Bool) (j : Nat) :
    VG.Proof.TripleDes.X86_64.Bitsliced.sl (arithFlags s x c o) j = VG.Proof.TripleDes.X86_64.Bitsliced.sl s j := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, mem_arithFlags, gpr_arithFlags]

theorem sl_setFlags (s : VG.X86_64.State) (a b c d : Option Bool) (j : Nat) :
    VG.Proof.TripleDes.X86_64.Bitsliced.sl (s.setFlags a b c d) j = VG.Proof.TripleDes.X86_64.Bitsliced.sl s j := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, mem_setFlags, gpr_setFlags]

theorem sl_st (s : VG.X86_64.State) {k : Nat} (hk : k < 128) (v : BitVec 64) {j : Nat} (hj : j < 128) :
    VG.Proof.TripleDes.X86_64.Bitsliced.sl { s with
                mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s k v } j = if j = k then v else VG.Proof.TripleDes.X86_64.Bitsliced.sl s j :=
  VG.Proof.TripleDes.X86_64.Bitsliced.readW_stMem s hk v hj

theorem exec_movMem {s : VG.X86_64.State} (d b : Reg) (k : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 k) 8) :
    exec (.mov d (.mem { base := b, disp := (k : Int) })) s =
      some (s.setReg d (s.mem.readW (s.gpr b + BitVec.ofNat 64 k) 64)) := by
  have hea : s.ea { base := b, disp := (k : Int) } = s.gpr b + BitVec.ofNat 64 k := rfl
  simp only [exec, readSrc, State.load64, hea, hr, ite_true, Option.map_some]

theorem exec_movImm (s : VG.X86_64.State) (d : Reg) (v : BitVec 32) :
    exec (.mov d (.imm v)) s = some (s.setReg d (v.signExtend 64)) := rfl

theorem exec_addImm (s : VG.X86_64.State) (d : Reg) (v : BitVec 32) :
    exec (.alu .add d (.imm v)) s = some ((arithFlags s (s.gpr d + v.signExtend 64)
      (decide (2 ^ 64 ≤ (s.gpr d).toNat + (v.signExtend 64).toNat))
      (addOverflow (s.gpr d) (v.signExtend 64) (s.gpr d + v.signExtend 64))).setReg d
      (s.gpr d + v.signExtend 64)) := rfl

theorem runBlock_cat (a b : List Instr) (s : VG.X86_64.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : VG.X86_64.State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat, h₁, Option.bind_some, h₂]

theorem frame_of_spills {s s' : VG.X86_64.State} (h : VG.Frame [slotRegion VG.Proof.TripleDes.X86_64.Bitsliced.sboxCfg s] s.mem s'.mem) :
    VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.spillR s] s.mem s'.mem := h

/-! ## Blocks over the variable domain -/

/-- Slots `[rcx + 8k]`, `k < 128`. -/
def varsCfg : Cfg := { base := .rcx, slots := 128, ext := .rsp, exts := 0 }

/-- Slot `k` is variable `k`; register `regs[i]` is variable `128 + i`. -/
def varEnv (regs : List Reg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (128 + i),
    slot := fun k => if k < 128 then some (2 ^ k) else none }

/-- The values of the variables. -/
def varVals (s : VG.X86_64.State) (regs : List Reg) (v : Nat) : BitVec 64 :=
  if v < 128 then VG.Proof.TripleDes.X86_64.Bitsliced.sl s v else s.gpr (regs.getD (v - 128) .rax)

def varN (regs : List Reg) : Nat := 128 + regs.length

theorem Room.ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) : Ok VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg s :=
  Ok.of_region h.scratch rfl (by show 8 * 128 ≤ 1024; decide) (by decide) rfl

theorem varEnv_rel {s : VG.X86_64.State} (regs : List Reg) :
    Rel (VarRel (VG.Proof.TripleDes.X86_64.Bitsliced.varVals s regs) (VG.Proof.TripleDes.X86_64.Bitsliced.varN regs)) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) (VG.Proof.TripleDes.X86_64.Bitsliced.varEnv regs) s where
  reg r a h := by
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, VG.Proof.TripleDes.X86_64.Bitsliced.varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varVals, show ¬ 128 + i < 128 by omega, ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h := by
    have hk' : k < 128 := hk
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, VG.Proof.TripleDes.X86_64.Bitsliced.varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varVals, hk', ite_true, VG.Proof.TripleDes.X86_64.Bitsliced.sl, VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg]
  ext _ _ hk := by simp [VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg] at hk

/-- Run a block that the variable domain accepts. -/
theorem varsRun {is : List Instr} (regs : List Reg) {post : Env Nat → Bool}
    (hchk : VG.X86_64.Straight.check (vars 64) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) is (VG.Proof.TripleDes.X86_64.Bitsliced.varEnv regs) post = true)
    {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (VarRel (VG.Proof.TripleDes.X86_64.Bitsliced.varVals s regs) (VG.Proof.TripleDes.X86_64.Bitsliced.varN regs)) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) e' s s'
        (fun r => (is.all fun i => i.dst != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨s', hs', p⟩ := run (vars_sound _ _) h.ok (VG.Proof.TripleDes.X86_64.Bitsliced.varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem varRel_slot {V : Nat → BitVec 64} {N : Nat} {e : Env Nat} {s : VG.X86_64.State}
    (hrel : Rel (VarRel V N) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) e s) {k a : Nat} (hk : k < 128)
    (ha : e.slot k = some a) : VG.Proof.TripleDes.X86_64.Bitsliced.sl s k = xorSet V a N :=
  hrel.slot k a hk ha

theorem varRel_reg {V : Nat → BitVec 64} {N : Nat} {e : Env Nat} {s : VG.X86_64.State}
    (hrel : Rel (VarRel V N) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) e s) {r : Reg} {a : Nat}
    (ha : e.reg r = some a) : s.gpr r = xorSet V a N :=
  hrel.reg r a ha

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Step`. -/
section

/-!
# One S-box of a bitsliced round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the next six key bits of
`r15` as masks XORed with the words of `E`; its circuit; XORing its outputs
into their words) does to the state words what `step` does, given the key
bits at the top of `r15`, and shifts them out. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

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
  omega

theorem add_self_carry (a : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + a.toNat) = a.msb := by
  rw [BitVec.msb_eq_decide]
  have := a.isLt
  simp only [Nat.add_one_sub_one]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

theorem sbb_self (a : BitVec 64) (c : Bool) : a - a - (BitVec.ofBool c).setWidth 64 = VG.Proof.TripleDes.X86_64.Bitsliced.maskVal c := by
  cases c <;> simp [VG.Proof.TripleDes.X86_64.Bitsliced.maskVal]

theorem msb_shiftLeft (R : BitVec 64) {n : Nat} (hn : n < 64) : (R <<< n).msb = R.getLsbD (63 - n) := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have : ¬ 63 < n := by omega
  simp [this, show (63 : Nat) < 64 by decide]

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 64) : (VG.Proof.TripleDes.X86_64.Bitsliced.maskVal b).getLsbD p = b := by
  cases b
  · simp [VG.Proof.TripleDes.X86_64.Bitsliced.maskVal]
  · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .r15 ∧ inReg i ≠ .rcx ∧ inReg i ≠ .rsp := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: the next key bit as a mask, XORed with slot `w`. -/
theorem inputStep_run {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {q : Reg} (hq : q ≠ .r15) (hc : q ≠ .rcx)
    {w : Nat} (hw : w < 128) :
    ∃ s', runBlock isa [.alu .add .r15 (.reg .r15), .alu .sbb q (.reg q), .alu .xor q (.mem (at_ w))] s
        = some s' ∧
      s'.gpr .r15 = s.gpr .r15 <<< 1 ∧ s'.gpr q = VG.Proof.TripleDes.X86_64.Bitsliced.maskVal (s.gpr .r15).msb ^^^ VG.Proof.TripleDes.X86_64.Bitsliced.sl s w ∧
      (∀ r, r ≠ q → r ≠ .r15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr .r15
  let s₁ := (arithFlags s (a + a) (decide (2 ^ 64 ≤ a.toNat + a.toNat)) (addOverflow a a (a + a))).setReg
    .r15 (a + a)
  have e₁ : exec (.alu .add .r15 (.reg .r15)) s = some s₁ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]; rfl
  have cf₁ : s₁.cf = some a.msb := by
    simp only [s₁, cf_setReg, cf_arithFlags, VG.Proof.TripleDes.X86_64.Bitsliced.add_self_carry]
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
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₂ := h.congr c₂ wr₂
  let v := VG.Proof.TripleDes.X86_64.Bitsliced.sl s w
  let x := s₂.gpr q ^^^ v
  let s₃ := (arithFlags s₂ x false false).setReg q x
  have e₃ : exec (.alu .xor q (.mem (at_ w))) s₂ = some s₃ := by
    simp only [exec, execAlu, readSrc, State.load64, VG.Proof.TripleDes.X86_64.Bitsliced.ea_at, VG.Proof.TripleDes.X86_64.Bitsliced.slot_readable h₂ hw, ite_true,
      Option.bind_some]
    have : s₂.mem.readW (wordAddr (s₂.gpr .rcx) w) 64 = v := by simp only [m₂, c₂]; rfl
    rw [this]
  refine ⟨s₃, ?_, ?_, ?_, fun r' h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · simp [s₃, s₂, s₁, gpr_setReg, Ne.symm hq, VG.Proof.TripleDes.X86_64.Bitsliced.add_self_eq, a]
  · simp only [s₃, gpr_setReg_self, x]
    congr 1
    simp only [s₂, gpr_setReg_self, r]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.sbb_self _ _
  · simp [s₃, s₂, s₁, gpr_setReg, h1, h2]
  · simp [s₃, mem_setReg, mem_arithFlags, m₂]
  · simp [s₃, rd_setReg, rd_arithFlags, rd₂]
  · simp [s₃, wr_setReg, wr_arithFlags, wr₂]

def inputsN (ρ : Role) (j n : Nat) : List Instr :=
  (List.range n).flatMap fun m => inputStep ρ j (5 - m)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = VG.Proof.TripleDes.X86_64.Bitsliced.inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    VG.Proof.TripleDes.X86_64.Bitsliced.inputsN ρ j (n + 1) = VG.Proof.TripleDes.X86_64.Bitsliced.inputsN ρ j n ++ inputStep ρ j (5 - n) := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readSlot_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, stSlot (readWord ρ (eBit (inBit j i))) < 72 := by
  intro ρ; cases ρ <;> lit_decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86_64.Bitsliced.inputsN ρ j n) s = some s' ∧ s'.gpr .r15 = s.gpr .r15 <<< n ∧
      (∀ m < n, s'.gpr (inReg (5 - m)) = VG.Proof.TripleDes.X86_64.Bitsliced.maskVal ((s.gpr .r15).getLsbD (63 - m)) ^^^
        VG.Proof.TripleDes.X86_64.Bitsliced.sl s (stSlot (readWord ρ (eBit (inBit j (5 - m)))))) ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, by simp, fun m hm => by omega, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, k₁, in₁, c₁, sp₁, m₁, rd₁, wr₁⟩ := ih (by omega)
    have h₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₁ := h.congr c₁ wr₁
    obtain ⟨hq, hc, hsp⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.inReg_ne (5 - n) (by omega)
    obtain ⟨s₂, run₂, k₂, q₂, o₂, m₂, rd₂, wr₂⟩ :=
      VG.Proof.TripleDes.X86_64.Bitsliced.inputStep_run h₁ hq hc (w := stSlot (readWord ρ (eBit (inBit j (5 - n)))))
        (by have := VG.Proof.TripleDes.X86_64.Bitsliced.readSlot_lt ρ j hj (5 - n) (by omega); omega)
    refine ⟨s₂, ?_, ?_, fun m hm => ?_, ?_, ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [VG.Proof.TripleDes.X86_64.Bitsliced.inputsN_succ]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₁ run₂
    · rw [k₂, k₁, ← BitVec.shiftLeft_add]
    · by_cases he : m = n
      · subst he
        rw [q₂, k₁, VG.Proof.TripleDes.X86_64.Bitsliced.msb_shiftLeft _ (by omega)]
        simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, m₁, c₁]
      · have hne : inReg (5 - m) ≠ inReg (5 - n) := by
          intro e; have := VG.Proof.TripleDes.X86_64.Bitsliced.inReg_inj' _ (by omega) _ (by omega) e; omega
        rw [o₂ _ hne (VG.Proof.TripleDes.X86_64.Bitsliced.inReg_ne (5 - m) (by omega)).1, in₁ m (by omega)]
    · rw [o₂ _ (Ne.symm hc) (by decide)]; exact c₁
    · rw [o₂ _ (Ne.symm hsp) (by decide)]; exact sp₁

/-! ## Outputs -/

/-- The output bit of S-box `j` that goes into scratch slot `k`, if any. -/
def outSlot (ρ : Role) (j k : Nat) : Option Nat :=
  if 8 ≤ k ∧ k < 72 then outIdx ρ j (k - 8) else none

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 128).all fun k => e.slot k ==
    some (match VG.Proof.TripleDes.X86_64.Bitsliced.outSlot ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (128 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    VG.X86_64.Straight.check (vars 64) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) (outputCode ρ j) (VG.Proof.TripleDes.X86_64.Bitsliced.varEnv outRegs) (VG.Proof.TripleDes.X86_64.Bitsliced.outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_r15 : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => i.dst != some .r15) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s' k = match VG.Proof.TripleDes.X86_64.Bitsliced.outSlot ρ j k with
        | some i => VG.Proof.TripleDes.X86_64.Bitsliced.sl s k ^^^ s.gpr (outReg i)
        | none => VG.Proof.TripleDes.X86_64.Bitsliced.sl s k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r15 = s.gpr .r15 ∧ VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.varsRun outRegs (VG.Proof.TripleDes.X86_64.Bitsliced.output_check ρ j hj) h
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, p.rd, p.wr, p.base, p.ext,
    p.other .r15 (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.outputCode_r15 ρ j hj]), p.frame⟩
  rw [VG.Proof.TripleDes.X86_64.Bitsliced.varRel_slot p.rel hk (hpost k hk)]
  split
  · rename_i i hi
    have hi4 : i < 4 := by
      simp only [VG.Proof.TripleDes.X86_64.Bitsliced.outSlot] at hi
      split at hi
      · exact VG.Proof.TripleDes.X86_64.Bitsliced.outIdx_lt ρ j _ i hi
      · cases hi
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.xorSet_two_pow_xor (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.varN, outRegs]; omega) (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.varN, outRegs]; omega)]
    have e1 : ¬ 128 + i < 128 := by omega
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outReg]
  · rw [xorSet_two_pow _ (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.varN]; omega)]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varVals, hk, ite_true]

/-! ## One S-box -/

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (k : BitVec 48)
    (hkey : ∀ i < 6, (s.gpr .r15).getLsbD (58 + i) = k.getLsbD (inBit j i)) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x = VG.Proof.TripleDes.Bitslice.step ρ k j (VG.Proof.TripleDes.X86_64.Bitsliced.words s) x) ∧
      (∀ x < 128, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.gpr .r15 = s.gpr .r15 <<< 6 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, in₁, c₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.inputsN_ok ρ hj (Nat.le_refl 6) h
  have h₁ := h.congr c₁ wr₁
  have ok₁ : Ok VG.Proof.TripleDes.X86_64.Bitsliced.sboxCfg s₁ :=
    Ok.of_region h₁.scratch rfl (by show 8 * spills ≤ 1024; decide) (by decide) rfl
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, c₂, sp₂, k₂, f₂⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.sbox_ok j hj ok₁
  have h₂ := h₁.congr c₂ wr₂
  obtain ⟨s₃, run₃, sl₃, rd₃, wr₃, c₃, sp₃, k₃, f₃⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.outputs_ok ρ hj h₂
  have sl₂ : ∀ x < 128, spills ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s₂ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x hx hs
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_of_spill c₂ (VG.Proof.TripleDes.X86_64.Bitsliced.frame_of_spills f₂) hs hx]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, m₁, c₁]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      VG.Proof.TripleDes.X86_64.Bitsliced.maskVal (k.getLsbD (inBit j i)) ^^^ VG.Proof.TripleDes.X86_64.Bitsliced.sl s (stSlot (readWord ρ (eBit (inBit j i)))) := by
    intro i hi
    have e := in₁ (5 - i) (by omega)
    rw [show 5 - (5 - i) = i by omega] at e
    rw [e, show 63 - (5 - i) = 58 + i by omega, hkey i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, fun x hx hl => ?_, ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), c₃.trans (c₂.trans c₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [sboxStep, VG.Proof.TripleDes.X86_64.Bitsliced.inputCode_eq]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some (VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₁ run₂) run₃
  · have hs : stSlot x < 128 := by unfold stSlot; omega
    have e₂ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₂ (stSlot x) = VG.Proof.TripleDes.X86_64.Bitsliced.words s x := sl₂ _ hs (by unfold stSlot spills; omega)
    have hos : VG.Proof.TripleDes.X86_64.Bitsliced.outSlot ρ j (stSlot x) = outIdx ρ j x := by
      simp only [VG.Proof.TripleDes.X86_64.Bitsliced.outSlot, stSlot, show 8 ≤ 8 + x ∧ 8 + x < 72 by omega, and_self, ite_true,
        Nat.add_sub_cancel_left]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words]
    rw [sl₃ _ hs, hos]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact e₂
    · have hi4 := VG.Proof.TripleDes.X86_64.Bitsliced.outIdx_lt ρ j x i hidx
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
      simp only [VG.Proof.TripleDes.X86_64.Bitsliced.inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, VG.Proof.TripleDes.X86_64.Bitsliced.getLsbD_mask _ hp, VG.Proof.TripleDes.X86_64.Bitsliced.words]
      rw [Bool.xor_comm]
  · rw [sl₃ x hx]
    have : VG.Proof.TripleDes.X86_64.Bitsliced.outSlot ρ j x = none := by
      simp only [VG.Proof.TripleDes.X86_64.Bitsliced.outSlot, show ¬ (8 ≤ x ∧ x < 72) by omega, ite_false]
    rw [this]
    exact sl₂ x hx (by unfold spills; omega)
  · rw [k₃, k₂, k₁]
  · have g₁ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s₁.mem := by rw [m₁]; exact Frame.refl _ _
    have g₂ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s₁.mem s₂.mem := by
      have := VG.Proof.TripleDes.X86_64.Bitsliced.spill_toScratch (VG.Proof.TripleDes.X86_64.Bitsliced.frame_of_spills f₂)
      rwa [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₁]] at this
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₂, c₁]] at f₃
    exact g₁.trans (g₂.trans f₃)

/-! ## The exchange of the halves -/

/-- The slot whose word goes into slot `k`. -/
def swapSlot (k : Nat) : Nat :=
  if 8 ≤ k ∧ k < 72 then (match partner (k - 8) with | some y => 8 + y | none => k) else k

def swapPost (e : Env Nat) : Bool :=
  (List.range 128).all fun k => e.slot k == some (2 ^ VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot k)

theorem swap_check :
    VG.X86_64.Straight.check (vars 64) VG.Proof.TripleDes.X86_64.Bitsliced.varsCfg (fun _ => none) VG.Impl.TripleDes.X86_64.Bitslice.swapHalves (VG.Proof.TripleDes.X86_64.Bitsliced.varEnv []) VG.Proof.TripleDes.X86_64.Bitsliced.swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 128, VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot k < 128 := by lit_decide

theorem swapHalves_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ s', runBlock isa VG.Impl.TripleDes.X86_64.Bitslice.swapHalves s = some s' ∧ (∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x = swapW (VG.Proof.TripleDes.X86_64.Bitsliced.words s) x) ∧
      (∀ x < 128, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.varsRun [] VG.Proof.TripleDes.X86_64.Bitsliced.swap_check h
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s' k = VG.Proof.TripleDes.X86_64.Bitsliced.sl s (VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot k) := by
    intro k hk
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.varRel_slot p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.varN]; exact VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot_lt k hk)]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.varVals, VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, fun x hx hl => ?_, p.rd, p.wr, p.base, p.ext, p.frame⟩
  · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words, stSlot]
    rw [key _ (by omega)]
    simp only [swapW, VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot, show 8 ≤ 8 + x ∧ 8 + x < 72 by omega, and_self, ite_true,
      Nat.add_sub_cancel_left]
    rcases partner x with _ | y <;> rfl
  · rw [key x hx]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.swapSlot, show ¬ (8 ≤ x ∧ x < 72) by omega, ite_false]

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Round`. -/
section

/-!
# A bitsliced round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
(scratch slot `keySlot`) into `r15`, advances the pointer by the step
(`stepSlot`), and does to the 64 state words what `roundW` does, with the
key's low 48 bits.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ steps_congr)

/-! ## The round key -/

theorem keyLoad_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (hkey : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) 8) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      s'.gpr .r15 = (s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) 64).rotateRight 48 ∧
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot ∧
      (∀ x < 128, x ≠ keySlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  let kp := VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot
  let K := s.mem.readW kp 64
  let δ := VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot
  let s₁ := s.setReg .rax kp
  have e₁ : exec (ld .rax keySlot) s = some s₁ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h (by decide) .rax
  let s₂ := s₁.setReg .r15 K
  have e₂ : exec (.mov .r15 (.mem { base := .rax, disp := 0 })) s₁ = some s₂ := by
    have hea : s₁.ea { base := .rax, disp := 0 } = kp := by
      simp [State.ea, s₁, gpr_setReg]
    have hl : s₁.load64 kp = some K := by
      simp only [State.load64, s₁, rd_setReg, wr_setReg, mem_setReg, hkey, ite_true, kp, K]
    simp only [exec, readSrc, hea, hl, Option.map_some]
    rfl
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg]) (by simp [s₂, s₁, wr_setReg])
  have sl₂ : ∀ x, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₂ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x; simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, s₂, s₁, mem_setReg, gpr_setReg]; rfl
  let s₃ := s₂.setReg .rdx δ
  have e₃ : exec (ld .rdx stepSlot) s₂ = some s₃ := by
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h₂ (by decide) .rdx, sl₂]
  let v := kp + δ
  let s₄ := (arithFlags s₃ v (decide (2 ^ 64 ≤ kp.toNat + δ.toNat)) (addOverflow kp δ v)).setReg .rax v
  have e₄ : exec (.alu .add .rax (.reg .rdx)) s₃ = some s₄ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    have ha : s₃.gpr .rax = kp := by simp [s₃, s₂, s₁, gpr_setReg]
    have hd : s₃.gpr .rdx = δ := by simp [s₃, gpr_setReg]
    rw [ha, hd]
  have h₄ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₄ := h₂.congr (by simp [s₄, s₃, s₂, s₁, gpr_setReg])
    (by simp [s₄, s₃, wr_setReg, wr_arithFlags])
  have e₅ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rax) h₄ (by decide : keySlot < 128)
  let s₅ : VG.X86_64.State := { s₄ with
                              mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₄ keySlot (s₄.gpr .rax) }
  let s₆ := (s₅.setFlags (some ((s₅.gpr .r15).rotateRight 48).msb) none s₅.zf s₅.sf).setReg .r15
    ((s₅.gpr .r15).rotateRight 48)
  have e₆ : exec (.shift .ror .r15 48) s₅ = some s₆ := by
    simp only [exec, execShift]; rfl
  have rcx₄ : s₄.gpr .rcx = s.gpr .rcx := by simp [s₄, s₃, s₂, s₁, gpr_setReg]
  have mem₄ : s₄.mem = s.mem := by simp [s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  have rax₄ : s₄.gpr .rax = v := by simp [s₄, gpr_setReg]
  have sl₆ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₆ x = if x = keySlot then v else VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x hx
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, s₆, mem_setReg, mem_setFlags, gpr_setReg, gpr_setFlags]
    simp only [show ¬ Reg.rcx = Reg.r15 by decide, ite_false, s₅]
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.readW_stMem s₄ (by decide) _ hx, rax₄]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, mem₄, rcx₄]
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
  · have f := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := s₄) (by decide : keySlot < 128) (s₄.gpr .rax)
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₄ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, rcx₄], mem₄] at f
    simpa [s₆, s₅, mem_setReg, mem_setFlags] using f

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode ρ (n + 1) = VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode ρ n ++ sboxStep ρ n := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- S-box `j`'s key bits are at the top of the rotated key, shifted by the
bits of the S-boxes before it. -/
theorem keyBits (K : BitVec 64) {j i : Nat} (hj : j < 8) (hi : i < 6) :
    (K.rotateRight 48 <<< (6 * j)).getLsbD (58 + i) = (K.setWidth 48).getLsbD (inBit j i) := by
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth]
  have h1 : ¬ 58 + i < 6 * j := by omega
  have h2 : ¬ 58 + i - 6 * j < 64 - 48 % 64 := by omega
  have h3 : 58 + i - 6 * j - (64 - 48 % 64) = inBit j i := by unfold inBit; omega
  have h4 : inBit j i < 48 := by unfold inBit; omega
  simp only [h1, decide_false, Bool.not_false, Bool.true_and, h2, ite_false, h3, h4, decide_true,
    Bool.true_and, show 58 + i < 64 by omega, show 58 + i - 6 * j < 64 by omega]

theorem stepsCode_ok (ρ : Role) (K : BitVec 64) {n : Nat} (hn : n ≤ 8) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s)
    (hr : s.gpr .r15 = K.rotateRight 48) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode ρ n) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x = steps ρ (K.setWidth 48) n (VG.Proof.TripleDes.X86_64.Bitsliced.words s) x) ∧
      (∀ x < 128, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.gpr .r15 = K.rotateRight 48 <<< (6 * n) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ _ => rfl, by simp [hr], rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, hi₁, r₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := ih (by omega)
    have h₁ := h.congr c₁ wr₁
    obtain ⟨s₂, run₂, w₂, hi₂, r₂, rd₂, wr₂, c₂, sp₂, f₂⟩ :=
      VG.Proof.TripleDes.X86_64.Bitsliced.sboxStep_ok ρ (by omega : n < 8) h₁ (K.setWidth 48)
        (fun i hi => by rw [r₁]; exact VG.Proof.TripleDes.X86_64.Bitsliced.keyBits K (by omega) hi)
    refine ⟨s₂, ?_, fun x hx => ?_, fun x hx hl => ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
      c₂.trans c₁, sp₂.trans sp₁, ?_⟩
    · rw [VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode_succ]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [hi₂ x hx hl, hi₁ x hx hl]
    · rw [r₂, r₁, ← BitVec.shiftLeft_add, show 6 * n + 6 = 6 * (n + 1) by omega]
    · rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (ρ : Role) : VG.Impl.TripleDes.X86_64.Bitslice.round ρ = keyLoad ++ VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode ρ 8 := rfl

theorem round_ok (ρ : Role) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s)
    (hkey : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) 8) :
    ∃ s', runBlock isa (VG.Impl.TripleDes.X86_64.Bitslice.round ρ) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x =
        roundW ρ ((s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) 64).setWidth 48) (VG.Proof.TripleDes.X86_64.Bitsliced.words s) x) ∧
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot ∧
      (∀ x < 128, 72 ≤ x → x ≠ keySlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, r₁, key₁, sl₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.keyLoad_ok h hkey
  have h₁ := h.congr c₁ wr₁
  obtain ⟨s₂, run₂, w₂, hi₂, -, rd₂, wr₂, c₂, sp₂, f₂⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.stepsCode_ok ρ _ (Nat.le_refl 8) h₁ r₁
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun x hx hl hne => ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    c₂.trans c₁, sp₂.trans sp₁, ?_⟩
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.round_eq]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact steps_congr ρ _ (Nat.le_refl 8)
      (fun y hy => sl₁ _ (by unfold stSlot; omega) (by unfold stSlot keySlot; omega)) x hx
  · rw [hi₂ _ (by decide) (by decide), key₁]
  · rw [hi₂ x hx hl, sl₁ x hx hne]
  · rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₁]] at f₂
    exact f₁.trans f₂

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass`. -/
section

/-!
# A bitsliced DES pass on the machine

A pass chooses its first key's address and the step between keys by the
pass count (`passStart`), runs eight pairs of rounds (the loop counts them in
`roundSlot`), exchanges the halves and counts the pass (`passEnd`).
`pass_ok`: it does to the state words what `swapW (pairs …)` does, with the
keys read at the addresses `a₀ + r δ`, which are apart from the scratch
buffer.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW partner)

/-- Eight readable bytes, apart from the scratch buffer. -/
structure Apart (s : VG.X86_64.State) (a : Addr) : Prop where
  read : InRegions (s.rd ++ s.wr) a 8
  scratch : (⟨a, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s)

theorem Apart.congr {s s' : VG.X86_64.State} {a : Addr} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s a) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s' a where
  read := by rw [hrd, hwr]; exact h.read
  scratch := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, hc]; exact h.scratch

theorem Apart.readW {s : VG.X86_64.State} {a : Addr} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s a) {m : Mem}
    (hf : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem m) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW (Region.contains_self a 8) (by simpa using h.scratch) (by decide)

/-! ## Counting down a slot -/

def decCode (k : Nat) : List Instr := [ld .rax k, .alu .sub .rax (.imm 1), st k .rax]

theorem decCode_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : k < 128) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.X86_64.Bitsliced.decCode k) s = some s' ∧ VG.Proof.TripleDes.X86_64.Bitsliced.sl s' k = VG.Proof.TripleDes.X86_64.Bitsliced.sl s k - 1 ∧
      s'.zf = some (VG.Proof.TripleDes.X86_64.Bitsliced.sl s k - 1 == 0) ∧ (∀ x < 128, x ≠ k → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  let v := VG.Proof.TripleDes.X86_64.Bitsliced.sl s k
  let s₁ := s.setReg .rax v
  have e₁ : exec (ld .rax k) s = some s₁ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h hk .rax
  let r := v - (1 : BitVec 32).signExtend 64
  let s₂ := (arithFlags s₁ r (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) r)).setReg .rax r
  have e₂ : exec (.alu .sub .rax (.imm 1)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    simp only [s₁, gpr_setReg_self]; rfl
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg])
    (by simp [s₂, s₁, wr_setReg, wr_arithFlags])
  have e₃ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rax) h₂ hk
  have hr : r = v - 1 := rfl
  have rcx₂ : s₂.gpr .rcx = s.gpr .rcx := by simp [s₂, s₁, gpr_setReg]
  have mem₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  have sl₃ : ∀ x < 128, (VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) x) 64 =
      if x = k then v - 1 else VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x hx
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.readW_stMem s₂ hk _ hx]
    simp only [s₂, gpr_setReg_self, ← hr]
    rfl
  refine ⟨{ s₂ with mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₂ k (s₂.gpr .rax) }, ?_, ?_, ?_, fun x hx hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.decCode, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · change (VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) k) 64 = _
    rw [sl₃ k hk]; simp; rfl
  · simp only [s₂, zf_setReg, zf_arithFlags]; rfl
  · change (VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) x) 64 = _
    rw [sl₃ x hx]; simp [hne]
  · simp [s₂, s₁, rd_setReg, rd_arithFlags]
  · simp [s₂, s₁, wr_setReg, wr_arithFlags]
  · exact rcx₂
  · simp [s₂, s₁, gpr_setReg]
  · have f := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := s₂) hk (s₂.gpr .rax)
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, rcx₂], mem₂] at f
    exact f

/-! ## A pair of rounds -/

theorem roundW_congr {w : Nat} (ρ : Role) (k : BitVec 48) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, roundW ρ k W x = roundW ρ k W' x :=
  VG.Proof.TripleDes.Bitslice.steps_congr ρ k (Nat.le_refl 8) hW

theorem roundPair_eq : roundPair = VG.Impl.TripleDes.X86_64.Bitslice.round .ba ++ VG.Impl.TripleDes.X86_64.Bitslice.round .ab ++ VG.Proof.TripleDes.X86_64.Bitsliced.decCode roundSlot := rfl

theorem roundPair_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (h₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot))
    (h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot)) :
    ∃ s', runBlock isa roundPair s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x = roundW .ab ((s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) 64).setWidth 48) (VG.Proof.TripleDes.X86_64.Bitsliced.words s)) x) ∧
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot ∧
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' roundSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s roundSlot - 1 ∧ s'.zf = some (VG.Proof.TripleDes.X86_64.Bitsliced.sl s roundSlot - 1 == 0) ∧
      (∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, key₁, misc₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.round_ok .ba h h₁.read
  have g₁ := h.congr c₁ wr₁
  have step₁ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ stepSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot := misc₁ _ (by decide) (by decide) (by decide)
  have hk₁ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot := key₁
  have a₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s₁ (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ keySlot) := by rw [hk₁]; exact h₂.congr c₁ rd₁ wr₁
  obtain ⟨s₂, run₂, w₂, key₂, misc₂, rd₂, wr₂, c₂, sp₂, f₂⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.round_ok .ab g₁ a₂.read
  have g₂ := g₁.congr c₂ wr₂
  obtain ⟨s₃, run₃, cnt₃, zf₃, sl₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.decCode_ok g₂ (by decide : roundSlot < 128)
  have kread : s₁.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot) 64 =
      s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot) 64 := h₂.readW f₁
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, ?_, fun x hx hlo hk hr => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), c₃.trans (c₂.trans c₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.roundPair_eq]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some (VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₁ run₂) run₃
  · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words]
    rw [sl₃ _ (by unfold stSlot; omega) (by unfold stSlot roundSlot; omega)]
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.sl s₂ (stSlot x) = VG.Proof.TripleDes.X86_64.Bitsliced.words s₂ x from rfl, w₂ x hx, hk₁, kread]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ab _ w₁ x hx
  · rw [sl₃ keySlot (by decide) (by decide), key₂, hk₁, step₁]
  · rw [cnt₃, misc₂ _ (by decide) (by decide) (by decide), misc₁ _ (by decide) (by decide) (by decide)]
  · rw [zf₃, misc₂ _ (by decide) (by decide) (by decide), misc₁ _ (by decide) (by decide) (by decide)]
  · rw [sl₃ x hx hr, misc₂ x hx hlo hk, misc₁ x hx hlo hk]
  · rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₁]] at f₂
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₂, c₁]] at f₃
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
    exact VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ab _ (VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ba _ ih) x hx

structure LoopInv (s₀ : VG.X86_64.State) (m : Nat) (s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s x = pairs (VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ keySlot) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ stepSlot)) (8 - m) (VG.Proof.TripleDes.X86_64.Bitsliced.words s₀) x
  key : VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ keySlot + BitVec.ofNat 64 (2 * (8 - m)) * VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ stepSlot
  cnt : VG.Proof.TripleDes.X86_64.Bitsliced.sl s roundSlot = BitVec.ofNat 64 m
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀] s₀.mem s.mem

structure LoopPost (s₀ s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s x = pairs (VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ keySlot) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ stepSlot)) 8 (VG.Proof.TripleDes.X86_64.Bitsliced.words s₀) x
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀] s₀.mem s.mem

theorem pairLoop_ok {s₀ : VG.X86_64.State} (hk : ∀ r < 16,
      VG.Proof.TripleDes.X86_64.Bitsliced.Apart s₀ (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ keySlot + BitVec.ofNat 64 r * VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ stepSlot))
    (m₀ : Nat) (s₁ : VG.X86_64.State) (hs₁ : VG.Proof.TripleDes.X86_64.Bitsliced.LoopInv s₀ m₀ s₁) :
    WP isa (.loop (.block roundPair) .ne) s₁ (VG.Proof.TripleDes.X86_64.Bitsliced.LoopPost s₀) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.X86_64.Bitsliced.LoopInv s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let a₀ := VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ keySlot
  let δ := VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ stepSlot
  have hδ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot = δ := hs.misc _ (by decide) (by decide) (by decide) (by decide)
  have n16 : 2 * (8 - m) + 1 < 16 := by have := hs.pos; omega
  have a₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) := by
    rw [hs.key]; exact (hk _ (by omega)).congr hs.rcx hs.rd hs.wr
  have a₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot) := by
    rw [hs.key, hδ, VG.Proof.TripleDes.X86_64.Bitsliced.kptr_succ]; exact (hk _ n16).congr hs.rcx hs.rd hs.wr
  obtain ⟨s', run', w', key', cnt', zf', misc', rd', wr', c', sp', f'⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.roundPair_ok hs.room a₁ a₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  have frame' : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀] s₀.mem s'.mem := by
    have := hs.frame
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀ by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, hs.rcx]] at f'
    exact this.trans f'
  have k1 : (s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot) 64).setWidth 48 =
      VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s₀.mem a₀ δ (2 * (8 - m)) := by
    rw [hs.key]; simp only [VG.Proof.TripleDes.X86_64.Bitsliced.keyAt]
    rw [((hk _ (by omega)).readW hs.frame)]
  have k2 : (s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.sl s keySlot + VG.Proof.TripleDes.X86_64.Bitsliced.sl s stepSlot) 64).setWidth 48 =
      VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s₀.mem a₀ δ (2 * (8 - m) + 1) := by
    rw [hs.key, hδ, VG.Proof.TripleDes.X86_64.Bitsliced.kptr_succ]; simp only [VG.Proof.TripleDes.X86_64.Bitsliced.keyAt]
    rw [((hk _ n16).readW hs.frame)]
  have words' : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x = pairs (VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s₀.mem a₀ δ) (8 - m + 1) (VG.Proof.TripleDes.X86_64.Bitsliced.words s₀) x := by
    intro x hx
    rw [w' x hx, k1, k2]
    simp only [pairs]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ab _ (VG.Proof.TripleDes.X86_64.Bitsliced.roundW_congr .ba _ hs.words) x hx
  have misc'' : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x :=
    fun x hx hlo hk hr => (misc' x hx hlo hk hr).trans (hs.misc x hx hlo hk hr)
  have room' := hs.room.congr c' wr'
  have cntv : VG.Proof.TripleDes.X86_64.Bitsliced.sl s roundSlot - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [hs.cnt]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.cnt_sub m hs.pos
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', c'.trans hs.rcx, sp'.trans hs.rsp, rd'.trans hs.rd, wr'.trans hs.wr,
      words', misc'', frame'⟩⟩
    show s'.zf.map (!·) = some false
    rw [zf', cntv]; rfl
  · right
    refine ⟨?_, m - 1, by omega, ⟨room', c'.trans hs.rcx, sp'.trans hs.rsp, rd'.trans hs.rd,
      wr'.trans hs.wr, by omega, by have := hs.le; omega, ?_, ?_, ?_, misc'', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf', cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        have hm : m ≤ 8 := hs.le
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega)] at this
        have := hs.pos
        omega
      rw [this]; rfl
    · have e : 8 - (m - 1) = 8 - m + 1 := by have := hs.le; omega
      rw [e]; exact words'
    · rw [key', hs.key, hδ, VG.Proof.TripleDes.X86_64.Bitsliced.kptr_succ, VG.Proof.TripleDes.X86_64.Bitsliced.kptr_succ]
      congr 3
      have := hs.le; omega
    · rw [cnt', cntv]

/-! ## The start of a pass -/

/-- Point at a pass's first key (`a` past the schedule), with step `b`. -/
theorem passKeyCode_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (a b : BitVec 32) :
    ∃ s', runBlock isa [ld .rdx schedSlot, .alu .add .rdx (.imm a), st keySlot .rdx,
        .mov .rdx (.imm b), st stepSlot .rdx] s = some s' ∧
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot + a.signExtend 64 ∧ VG.Proof.TripleDes.X86_64.Bitsliced.sl s' stepSlot = b.signExtend 64 ∧
      (∀ x < 128, x ≠ keySlot → x ≠ stepSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.gpr .rax = s.gpr .rax ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  let v := VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot
  let s₁ := s.setReg .rdx v
  have e₁ : exec (ld .rdx schedSlot) s = some s₁ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h (by decide) .rdx
  have e₂ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_addImm s₁ .rdx a
  let w := s₁.gpr .rdx + a.signExtend 64
  let s₂ := (arithFlags s₁ w (decide (2 ^ 64 ≤ (s₁.gpr .rdx).toNat + (a.signExtend 64).toNat))
      (addOverflow (s₁.gpr .rdx) (a.signExtend 64) w)).setReg .rdx w
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg]) (by simp [s₂, s₁, wr_setReg, wr_arithFlags])
  have e₃ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rdx) h₂ (by decide : keySlot < 128)
  let s₃ : VG.X86_64.State := { s₂ with
                              mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₂ keySlot (s₂.gpr .rdx) }
  have e₄ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_movImm s₃ .rdx b
  let s₄ := s₃.setReg .rdx (b.signExtend 64)
  have h₄ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₄ := h₂.congr (by simp [s₄, s₃, gpr_setReg]) (by simp [s₄, s₃, wr_setReg])
  have e₅ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rdx) h₄ (by decide : stepSlot < 128)
  let s₅ : VG.X86_64.State := { s₄ with
                              mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₄ stepSlot (s₄.gpr .rdx) }
  have c₂ : s₂.gpr .rcx = s.gpr .rcx := by simp [s₂, s₁, gpr_setReg]
  have m₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  have sl₅ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₅ x = if x = stepSlot then b.signExtend 64 else
      if x = keySlot then v + a.signExtend 64 else VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x hx
    have a₅ := VG.Proof.TripleDes.X86_64.Bitsliced.sl_st s₄ (by decide : stepSlot < 128) (s₄.gpr .rdx) hx
    have a₃ := VG.Proof.TripleDes.X86_64.Bitsliced.sl_st s₂ (by decide : keySlot < 128) (s₂.gpr .rdx) hx
    change VG.Proof.TripleDes.X86_64.Bitsliced.sl { s₄ with
                        mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₄ stepSlot (s₄.gpr .rdx) } x = _
    rw [a₅]
    simp only [s₄, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rdx ≠ .rcx), gpr_setReg_self]
    split
    · rfl
    · change VG.Proof.TripleDes.X86_64.Bitsliced.sl { s₂ with
                          mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₂ keySlot (s₂.gpr .rdx) } x = _
      rw [a₃]
      split
      · simp [s₂, s₁, gpr_setReg, w, v]
      · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, m₂, c₂]
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
  · have f₃ := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := s₂) (by decide : keySlot < 128) (s₂.gpr .rdx)
    have f₅ := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := s₄) (by decide : stepSlot < 128) (s₄.gpr .rdx)
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₂], m₂] at f₃
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₄ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, s₄, s₃, gpr_setReg, c₂]] at f₅
    exact f₃.trans f₅

/-- The comparison of `rax` with an immediate. -/
theorem cmp_run (s : VG.X86_64.State) (v : BitVec 32) :
    runBlock isa [.alu .cmp .rax (.imm v)] s = some (arithFlags s (s.gpr .rax - v.signExtend 64)
      (decide ((s.gpr .rax).toNat < (v.signExtend 64).toNat))
      (subOverflow (s.gpr .rax) (v.signExtend 64) (s.gpr .rax - v.signExtend 64))) := by
  rw [runBlock_cons]
  rfl

/-- What the start of a pass leaves. -/
structure StartPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s'
  key : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' keySlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot + BitVec.ofNat 64 (passKey d p).1
  step : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' stepSlot = BitVec.ofInt 64 (passKey d p).2
  round : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' roundSlot = 8
  misc : ∀ x < 128, x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem

theorem passKey_imm : ∀ d : Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 →
    (BitVec.ofNat 32 (passKey d p).1).signExtend 64 = BitVec.ofNat 64 (passKey d p).1 ∧
    (BitVec.ofInt 32 (passKey d p).2).signExtend 64 = BitVec.ofInt 64 (passKey d p).2 := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

theorem passStart_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : VG.X86_64.State}
    (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (hc : VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot = BitVec.ofNat 64 p) :
    WP isa (VG.Impl.TripleDes.X86_64.Bitslice.passStart d) s (VG.Proof.TripleDes.X86_64.Bitsliced.StartPost d p s) := by
  -- the code of a branch, and what follows it
  have branch : ∀ (s₁ : VG.X86_64.State), VG.Proof.TripleDes.X86_64.Bitsliced.Room s₁ → (∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) → s₁.gpr .rcx = s.gpr .rcx →
      s₁.gpr .rsp = s.gpr .rsp → s₁.rd = s.rd → s₁.wr = s.wr → VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s₁.mem →
      WP isa (.block (passKeyCode d p)) s₁ (fun s₂ =>
        WP isa (.block [.mov .rax (.imm 8), st roundSlot .rax]) s₂ (VG.Proof.TripleDes.X86_64.Bitsliced.StartPost d p s)) := by
    intro s₁ h₁ sl₁ c₁ sp₁ rd₁ wr₁ f₁
    obtain ⟨s₂, run₂, key₂, step₂, misc₂, -, rd₂, wr₂, c₂, sp₂, f₂⟩ :=
      VG.Proof.TripleDes.X86_64.Bitsliced.passKeyCode_ok h₁ (BitVec.ofNat 32 (passKey d p).1) (BitVec.ofInt 32 (passKey d p).2)
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    have h₂ := h₁.congr c₂ wr₂
    have e₃ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_movImm s₂ .rax 8
    let s₃ := s₂.setReg .rax ((8 : BitVec 32).signExtend 64)
    have h₃ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₃ := h₂.congr (by simp [s₃, gpr_setReg]) (by simp [s₃, wr_setReg])
    have e₄ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rax) h₃ (by decide : roundSlot < 128)
    refine WP.of_runBlock ⟨{ s₃ with mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₃ roundSlot (s₃.gpr .rax) }, ?_, ?_⟩
    · rw [runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil]
    have sl₄ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl { s₃ with
                                       mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s₃ roundSlot (s₃.gpr .rax) } x =
        if x = roundSlot then 8 else VG.Proof.TripleDes.X86_64.Bitsliced.sl s₂ x := by
      intro x hx
      rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st s₃ (by decide) _ hx]
      simp only [s₃, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx), gpr_setReg_self]
      split <;> rfl
    obtain ⟨i1, i2⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.passKey_imm d p hp.1 hp.2
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
    · have f := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := s₃) (by decide : roundSlot < 128) (s₃.gpr .rax)
      rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₃ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, s₃, gpr_setReg, c₂, c₁]] at f
      rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₁]] at f₂
      exact f₁.trans (f₂.trans f)
  -- load the count and compare it with 3
  let s₁ := s.setReg .rax (BitVec.ofNat 64 p)
  have e₁ : exec (ld .rax passSlot) s = some s₁ := by rw [VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h (by decide) .rax, hc]
  let t₁ := arithFlags s₁ (s₁.gpr .rax - (3 : BitVec 32).signExtend 64)
    (decide ((s₁.gpr .rax).toNat < ((3 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₁.gpr .rax) ((3 : BitVec 32).signExtend 64) (s₁.gpr .rax - (3 : BitVec 32).signExtend 64))
  have hrun₁ : runBlock isa [ld .rax passSlot, .alu .cmp .rax (.imm 3)] s = some t₁ := by
    rw [runBlock_cons, e₁, runStep_some, VG.Proof.TripleDes.X86_64.Bitsliced.cmp_run]
  have ht₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₁ := h.congr (by simp [t₁, s₁, gpr_setReg])
    (by simp [t₁, s₁, wr_setReg, wr_arithFlags])
  have sl₁ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl t₁ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x _; simp only [t₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags, s₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx)]
  have c₁ : t₁.gpr .rcx = s.gpr .rcx := by simp [t₁, s₁, gpr_setReg]
  have sp₁ : t₁.gpr .rsp = s.gpr .rsp := by simp [t₁, s₁, gpr_setReg]
  have rd₁ : t₁.rd = s.rd := by simp [t₁, s₁, rd_setReg, rd_arithFlags]
  have wr₁ : t₁.wr = s.wr := by simp [t₁, s₁, wr_setReg, wr_arithFlags]
  have f₁ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem t₁.mem := by
    simp only [t₁, s₁, mem_setReg, mem_arithFlags]; exact Frame.refl _ _
  have rax₁ : t₁.gpr .rax = BitVec.ofNat 64 p := by simp [t₁, s₁, gpr_setReg]
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, hrun₁, ?_⟩
  apply WP.seq
  have zf₁ : isa.eval .e t₁ = some (p == 3) := by
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
    have hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := arithFlags t₁ (t₁.gpr .rax - (2 : BitVec 32).signExtend 64)
      (decide ((t₁.gpr .rax).toNat < ((2 : BitVec 32).signExtend 64).toNat))
      (subOverflow (t₁.gpr .rax) ((2 : BitVec 32).signExtend 64) (t₁.gpr .rax - (2 : BitVec 32).signExtend 64))
    refine WP.of_runBlock ⟨t₂, VG.Proof.TripleDes.X86_64.Bitsliced.cmp_run t₁ 2, ?_⟩
    have ht₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₂ := ht₁.congr (by simp [t₂]) (by simp [t₂, wr_arithFlags])
    have zf₂ : isa.eval .e t₂ = some (p == 2) := by
      show t₂.zf = _
      simp only [t₂, zf_arithFlags, rax₁]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    have sl₂ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl t₂ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := fun x hx => by simp only [t₂, VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags]; exact sl₁ x hx
    have c₂ : t₂.gpr .rcx = s.gpr .rcx := by simp only [t₂, gpr_arithFlags, c₁]
    have sp₂ : t₂.gpr .rsp = s.gpr .rsp := by simp only [t₂, gpr_arithFlags, sp₁]
    have rd₂ : t₂.rd = s.rd := by simp only [t₂, rd_arithFlags, rd₁]
    have wr₂ : t₂.wr = s.wr := by simp only [t₂, wr_arithFlags, wr₁]
    have f₂ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem t₂.mem := by simp only [t₂, mem_arithFlags]; exact f₁
    apply WP.ite (p == 2) zf₂
    · intro h2
      have : p = 2 := by simpa using h2
      subst this
      exact branch t₂ ht₂ sl₂ c₂ sp₂ rd₂ wr₂ f₂
    · intro h2
      have : p = 1 := by have : p ≠ 2 := by simpa using h2
                         omega
      subst this
      exact branch t₂ ht₂ sl₂ c₂ sp₂ rd₂ wr₂ f₂

/-! ## A pass -/

theorem passEnd_eq : passEnd = VG.Proof.TripleDes.X86_64.Bitsliced.decCode passSlot := rfl

theorem pairs_keys_congr {w : Nat} {key key' : Nat → BitVec 48} (n : Nat)
    (hk : ∀ r < 2 * n, key r = key' r) (W : Nat → BitVec w) : pairs key n W = pairs key' n W := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairs]
    rw [ih (fun r hr => hk r (by omega)), hk (2 * n) (by omega), hk (2 * n + 1) (by omega)]

theorem partner_lt : ∀ k < 128, ∀ y, partner k = some y → y < 64 := by
  intro k hk y h
  have key : ∀ k < 128, (partner k).all (· < 64) = true := by lit_decide
  have := key k hk
  rw [h] at this
  simpa using this

theorem swapW_congr {w : Nat} {W W' : Nat → BitVec w} (hW : ∀ y < 64, W y = W' y) :
    ∀ x < 64, swapW W x = swapW W' x := by
  intro x hx
  simp only [swapW]
  rcases hp : partner x with _ | y
  · exact hW x hx
  · exact hW y (VG.Proof.TripleDes.X86_64.Bitsliced.partner_lt x (by omega) y hp)

/-- The first key of pass `p` (counted down from 3) and its step. -/
def passA (d : Spec.TripleDes.Direction) (p : Nat) (sched : Addr) : Addr :=
  sched + BitVec.ofNat 64 (passKey d p).1
def passD (d : Spec.TripleDes.Direction) (p : Nat) : Addr := BitVec.ofInt 64 (passKey d p).2

structure PassPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s'
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x =
    swapW (pairs (VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot)) (VG.Proof.TripleDes.X86_64.Bitsliced.passD d p)) 8 (VG.Proof.TripleDes.X86_64.Bitsliced.words s)) x
  count : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' passSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot - 1
  zf : s'.zf = some (VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot - 1 == 0)
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem

theorem pass_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : VG.X86_64.State}
    (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (hc : VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot = BitVec.ofNat 64 p)
    (hk : ∀ r < 16, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot) + BitVec.ofNat 64 r * VG.Proof.TripleDes.X86_64.Bitsliced.passD d p)) :
    WP isa (VG.Impl.TripleDes.X86_64.Bitslice.pass d) s (VG.Proof.TripleDes.X86_64.Bitsliced.PassPost d p s) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.passStart_ok d hp h hc)
  intro s₁ p₁
  have h₁ := p₁.room
  apply WP.seq
  have hk₁ : ∀ r < 16, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s₁ (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ keySlot + BitVec.ofNat 64 r * VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ stepSlot) := by
    intro r hr
    rw [p₁.key, p₁.step]; exact (hk r hr).congr p₁.rcx p₁.rd p₁.wr
  have inv : VG.Proof.TripleDes.X86_64.Bitsliced.LoopInv s₁ 8 s₁ := by
    refine ⟨h₁, rfl, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl, ?_, ?_,
      fun _ _ _ _ _ => rfl, Frame.refl _ _⟩
    · simp
    · rw [p₁.round]; rfl
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.pairLoop_ok hk₁ 8 s₁ inv)
  intro s₂ p₂
  have h₂ := p₂.room
  obtain ⟨s₃, run₃, sw₃, hi₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.swapHalves_ok h₂
  have h₃ := h₂.congr c₃ wr₃
  obtain ⟨s₄, run₄, cnt₄, zf₄, misc₄, rd₄, wr₄, c₄, sp₄, f₄⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.decCode_ok h₃ (by decide : passSlot < 128)
  refine WP.of_runBlock ⟨s₄, by rw [VG.Proof.TripleDes.X86_64.Bitsliced.passEnd_eq]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₃ run₄, ?_⟩
  have keys : ∀ r < 16, VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s₁.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ keySlot) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ stepSlot) r =
      VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot)) (VG.Proof.TripleDes.X86_64.Bitsliced.passD d p) r := by
    intro r hr
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.keyAt, p₁.key, p₁.step]
    have e := (hk r hr).readW p₁.frame
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.passA, VG.Proof.TripleDes.X86_64.Bitsliced.passD] at e
    rw [e]; rfl
  have state₁ : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s₁ x = VG.Proof.TripleDes.X86_64.Bitsliced.words s x := fun x hx =>
    p₁.misc _ (by unfold stSlot; omega) (by unfold stSlot keySlot; omega)
      (by unfold stSlot stepSlot; omega) (by unfold stSlot roundSlot; omega)
  have high : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → x ≠ passSlot →
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s₄ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ x := by
    intro x hx hlo hkx hrx hpx
    rw [misc₄ x hx hpx, hi₃ x hx hlo, p₂.misc x hx hlo hkx hrx]
  have pass₁ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ passSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot := p₁.misc _ (by decide) (by decide) (by decide) (by decide)
  have pass₃ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ passSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot := by
    rw [hi₃ _ (by decide) (by decide), p₂.misc _ (by decide) (by decide) (by decide) (by decide), pass₁]
  refine ⟨h₃.congr c₄ wr₄, c₄.trans (c₃.trans (p₂.rcx.trans p₁.rcx)),
    sp₄.trans (sp₃.trans (p₂.rsp.trans p₁.rsp)), rd₄.trans (rd₃.trans (p₂.rd.trans p₁.rd)),
    wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr)), fun x hx => ?_, ?_, ?_,
    fun x hx hlo a b c e => ?_, ?_⟩
  · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words]
    rw [misc₄ _ (by unfold stSlot; omega) (by unfold stSlot passSlot; omega)]
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ (stSlot x) = VG.Proof.TripleDes.X86_64.Bitsliced.words s₃ x from rfl, sw₃ x hx]
    apply VG.Proof.TripleDes.X86_64.Bitsliced.swapW_congr _ x hx
    intro y hy
    rw [p₂.words y hy, VG.Proof.TripleDes.X86_64.Bitsliced.pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.pairs_congr _ 8 state₁ y hy
  · rw [cnt₄, pass₃]
  · rw [zf₄, pass₃]
  · rw [high x hx hlo a c e]
    exact p₁.misc x hx a b c
  · have g₃ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s₂.mem s₃.mem := by
      rwa [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, p₂.rcx, p₁.rcx]] at f₃
    have g₄ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s₃.mem s₄.mem := by
      rwa [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₃ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₃, p₂.rcx, p₁.rcx]] at f₄
    have g₂ := p₂.frame
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, p₁.rcx]] at g₂
    exact p₁.frame.trans (g₂.trans (g₃.trans g₄))

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Keys`. -/
section

/-!
# The keys of the three passes

Pass `p` (counted down from 3) reads the round keys at `passA d p S + r δ`:
these are the round keys, in DES's order for the pass's direction, of the
component of the schedule `S` that TDEA uses in that pass (`passComp`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes (roundKey componentSchedule_readW)

/-- The component of the schedule and the direction of pass `p`. -/
def passComp : VG.Spec.TripleDes.Direction → Nat → Nat × VG.Spec.TripleDes.Direction
  | .encrypt, 3 => (0, .encrypt)
  | .encrypt, 2 => (1, .decrypt)
  | .encrypt, _ => (2, .encrypt)
  | .decrypt, 3 => (2, .decrypt)
  | .decrypt, 2 => (1, .encrypt)
  | .decrypt, _ => (0, .decrypt)

/-- The schedule word that is round `r`'s key of pass `p`. -/
def passIdx (d : VG.Spec.TripleDes.Direction) (p r : Nat) : Nat :=
  16 * (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).1 + if (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).2 = .encrypt then r else 15 - r

theorem passIdx_lt : ∀ d : VG.Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 → ∀ r < 16, VG.Proof.TripleDes.X86_64.Bitsliced.passIdx d p r < 48 := by
  intro d p h1 h3 r hr
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | (simp [VG.Proof.TripleDes.X86_64.Bitsliced.passIdx, VG.Proof.TripleDes.X86_64.Bitsliced.passComp]; omega)

theorem passAddr_eq : ∀ d : VG.Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 → ∀ r < 16,
    BitVec.ofNat 64 (passKey d p).1 + BitVec.ofNat 64 r * BitVec.ofInt 64 (passKey d p).2 =
      BitVec.ofNat 64 (8 * VG.Proof.TripleDes.X86_64.Bitsliced.passIdx d p r) := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

theorem keyAt_pass (m : Mem) (S : Addr) (d : VG.Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat}
    (hr : r < 16) :
    VG.Proof.TripleDes.X86_64.Bitsliced.keyAt m (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p S) (VG.Proof.TripleDes.X86_64.Bitsliced.passD d p) r =
      roundKey (componentSchedule (VG.Spec.TripleDes.scheduleAt m S) (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).1) (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).2 r := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.keyAt, VG.Proof.TripleDes.X86_64.Bitsliced.passA, VG.Proof.TripleDes.X86_64.Bitsliced.passD, roundKey]
  have hc : (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).1 < 3 := by
    cases d <;> (rcases hp with ⟨h1, h3⟩; rcases p with _ | _ | _ | _ | p) <;> first | omega | decide
  have hi : (if (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).2 = .encrypt then r else 15 - r) < 16 := by split <;> omega
  rw [componentSchedule_readW m S _ _ hc hi, BitVec.add_assoc, VG.Proof.TripleDes.X86_64.Bitsliced.passAddr_eq d p hp.1 hp.2 r hr]
  rfl

/-- The key words of the passes are apart from the scratch buffer. -/
theorem passKeys_apart {s : VG.X86_64.State} {S : Addr} (hS : ∀ i < 48, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (S + BitVec.ofNat 64 (8 * i)))
    (d : VG.Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat} (hr : r < 16) :
    VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p S + BitVec.ofNat 64 r * VG.Proof.TripleDes.X86_64.Bitsliced.passD d p) := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.passA, VG.Proof.TripleDes.X86_64.Bitsliced.passD]
  rw [BitVec.add_assoc, VG.Proof.TripleDes.X86_64.Bitsliced.passAddr_eq d p hp.1 hp.2 r hr]
  exact hS _ (VG.Proof.TripleDes.X86_64.Bitsliced.passIdx_lt d p hp.1 hp.2 r hr)

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Passes`. -/
section

/-!
# The three passes

The loop of passes, counted down from 3 in `passSlot`, does to the state
words what three DES passes (`passW`) do, with the components and
directions of TDEA (`passComp`), in every lane.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (passW pairs swapW)

/-- The first `n` passes, with the schedule `K`. -/
def chain {w : Nat} (d : VG.Spec.TripleDes.Direction) (K : VG.Spec.TripleDes.Schedule) : Nat → (Nat → BitVec w) → Nat → BitVec w
  | 0, W => W
  | n + 1, W => passW (componentSchedule K (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d (3 - n)).1) (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d (3 - n)).2 (VG.Proof.TripleDes.X86_64.Bitsliced.chain d K n W)

theorem chain_congr {w : Nat} (d : VG.Spec.TripleDes.Direction) (K : VG.Spec.TripleDes.Schedule) (n : Nat) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.chain d K n W x = VG.Proof.TripleDes.X86_64.Bitsliced.chain d K n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.chain, passW]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.swapW_congr (VG.Proof.TripleDes.X86_64.Bitsliced.pairs_congr _ 8 ih) x hx

structure PassesInv (d : VG.Spec.TripleDes.Direction) (s₀ : VG.X86_64.State) (p : Nat) (s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ p
  le : p ≤ 3
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s x = VG.Proof.TripleDes.X86_64.Bitsliced.chain d (VG.Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot)) (3 - p) (VG.Proof.TripleDes.X86_64.Bitsliced.words s₀) x
  count : VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot = BitVec.ofNat 64 p
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    VG.Proof.TripleDes.X86_64.Bitsliced.sl s x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀] s₀.mem s.mem

structure PassesPost (d : VG.Spec.TripleDes.Direction) (s₀ s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s x = VG.Proof.TripleDes.X86_64.Bitsliced.chain d (VG.Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot)) 3 (VG.Proof.TripleDes.X86_64.Bitsliced.words s₀) x
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    VG.Proof.TripleDes.X86_64.Bitsliced.sl s x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀] s₀.mem s.mem

theorem passes_ok (d : VG.Spec.TripleDes.Direction) {s₀ : VG.X86_64.State}
    (hS : ∀ i < 48, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s₀ (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot + BitVec.ofNat 64 (8 * i)))
    (p₀ : Nat) (s₁ : VG.X86_64.State) (hs₁ : VG.Proof.TripleDes.X86_64.Bitsliced.PassesInv d s₀ p₀ s₁) :
    WP isa (.loop (VG.Impl.TripleDes.X86_64.Bitslice.pass d) .ne) s₁ (VG.Proof.TripleDes.X86_64.Bitsliced.PassesPost d s₀) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.X86_64.Bitsliced.PassesInv d s₀) ?_ p₀ s₁ hs₁
  intro p s hs
  let S := VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot
  have hS' : VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot = S := hs.misc _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hp : 1 ≤ p ∧ p ≤ 3 := ⟨hs.pos, hs.le⟩
  have hk : ∀ r < 16, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot) + BitVec.ofNat 64 r * VG.Proof.TripleDes.X86_64.Bitsliced.passD d p) := by
    intro r hr
    rw [hS']
    exact (VG.Proof.TripleDes.X86_64.Bitsliced.passKeys_apart hS d hp hr).congr hs.rcx hs.rd hs.wr
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.pass_ok d hp hs.room hs.count hk)
  intro s' q
  have keys : ∀ r < 16, VG.Proof.TripleDes.X86_64.Bitsliced.keyAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.passA d p (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot)) (VG.Proof.TripleDes.X86_64.Bitsliced.passD d p) r =
      VG.Proof.TripleDes.roundKey (componentSchedule (VG.Spec.TripleDes.scheduleAt s₀.mem S) (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).1)
        (VG.Proof.TripleDes.X86_64.Bitsliced.passComp d p).2 r := by
    intro r hr
    have e := (VG.Proof.TripleDes.X86_64.Bitsliced.passKeys_apart hS d hp hr).readW hs.frame
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.keyAt, hS']
    rw [e, ← VG.Proof.TripleDes.X86_64.Bitsliced.keyAt_pass s₀.mem S d hp hr]; rfl
  have words' : ∀ x < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' x = VG.Proof.TripleDes.X86_64.Bitsliced.chain d (VG.Spec.TripleDes.scheduleAt s₀.mem S) (3 - p + 1) (VG.Proof.TripleDes.X86_64.Bitsliced.words s₀) x := by
    intro x hx
    rw [q.words x hx, VG.Proof.TripleDes.X86_64.Bitsliced.pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.chain, show 3 - (3 - p) = p by omega]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.swapW_congr (VG.Proof.TripleDes.X86_64.Bitsliced.pairs_congr _ 8 hs.words) x hx
  have misc' : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x := fun x hx a b c d e => (q.misc x hx a b c d e).trans (hs.misc x hx a b c d e)
  have frame' : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀] s₀.mem s'.mem := by
    have := q.frame
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀ by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, hs.rcx]] at this
    exact hs.frame.trans this
  have cntv : VG.Proof.TripleDes.X86_64.Bitsliced.sl s passSlot - 1 = BitVec.ofNat 64 (p - 1) := by rw [hs.count]; exact VG.Proof.TripleDes.X86_64.Bitsliced.cnt_sub p hs.pos
  by_cases h1 : p = 1
  · subst h1
    left
    refine ⟨?_, q.room, q.rcx.trans hs.rcx, q.rsp.trans hs.rsp, q.rd.trans hs.rd, q.wr.trans hs.wr,
      words', misc', frame'⟩
    show s'.zf.map (!·) = some false
    rw [q.zf, cntv]; rfl
  · right
    refine ⟨?_, p - 1, by omega, ⟨q.room, q.rcx.trans hs.rcx, q.rsp.trans hs.rsp, q.rd.trans hs.rd,
      q.wr.trans hs.wr, by omega, by omega, ?_, ?_, misc', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [q.zf, cntv]
      have : (BitVec.ofNat 64 (p - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [this]; rfl
    · rw [show 3 - (p - 1) = 3 - p + 1 by omega]; exact words'
    · rw [q.count, cntv]

/-- Three passes, in every lane: TDEA between IP and FP. -/
theorem chain_lane {w : Nat} (d : VG.Spec.TripleDes.Direction) (K : VG.Spec.TripleDes.Schedule) (W : Nat → BitVec w) {b : Nat}
    (hb : b < w) :
    VG.Proof.TripleDes.Bitslice.ipLane (VG.Proof.TripleDes.X86_64.Bitsliced.chain d K 3 W) b =
      match d with
      | .encrypt => VG.Proof.TripleDes.desCore (componentSchedule K 2) .encrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .decrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 0) .encrypt
              (VG.Proof.TripleDes.Bitslice.ipLane W b)))
      | .decrypt => VG.Proof.TripleDes.desCore (componentSchedule K 0) .decrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .encrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 2) .decrypt
              (VG.Proof.TripleDes.Bitslice.ipLane W b))) := by
  cases d <;> simp only [VG.Proof.TripleDes.X86_64.Bitsliced.chain, VG.Proof.TripleDes.Bitslice.pass_lane _ _ _ hb] <;> rfl

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Copy`. -/
section

/-!
# Copying words

`copy_ok`: the loop of `copyBody src dst` copies `n ≥ 1` words from `A` (in
`src`) to `B` (in `dst`), where the two areas do not overlap, and changes
nothing else in memory. `src` and `dst` are `rsi` and `rdi`, in either
order; `rdx` counts the words left.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice

/-- Word `i` from `p`. -/
abbrev wAt (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

structure CopyPre (A B : Addr) (n : Nat) (s : VG.X86_64.State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A i) 8
  write : ∀ i < n, InRegions s.wr (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : VG.Proof.TripleDes.X86_64.Bitsliced.wAt p i + 8 = VG.Proof.TripleDes.X86_64.Bitsliced.wAt p (i + 1) := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.wAt, BitVec.add_assoc]
  congr 1
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

structure CopyInv (src dst : Reg) (A B : Addr) (n : Nat) (s₀ : VG.X86_64.State) (i : Nat) (s : VG.X86_64.State) : Prop where
  le : i < n
  src : s.gpr src = VG.Proof.TripleDes.X86_64.Bitsliced.wAt A i
  dst : s.gpr dst = VG.Proof.TripleDes.X86_64.Bitsliced.wAt B i
  cnt : s.gpr .rdx = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B j) 64 = s₀.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A j) 64
  frame : VG.Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rdx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

structure CopyPost (src dst : Reg) (A B : Addr) (n : Nat) (s₀ s : VG.X86_64.State) : Prop where
  src : s.gpr src = VG.Proof.TripleDes.X86_64.Bitsliced.wAt A n
  dst : s.gpr dst = VG.Proof.TripleDes.X86_64.Bitsliced.wAt B n
  copied : ∀ j < n, s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B j) 64 = s₀.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A j) 64
  frame : VG.Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rdx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (VG.Proof.TripleDes.X86_64.Bitsliced.wAt p i) 8 :=
  Offset.contains_base p (by omega) (by omega)

theorem copy_ok {src dst : Reg} (hsd : (src = .rsi ∧ dst = .rdi) ∨ (src = .rdi ∧ dst = .rsi))
    {A B : Addr} {n : Nat} {s₀ : VG.X86_64.State} (hpre : VG.Proof.TripleDes.X86_64.Bitsliced.CopyPre A B n s₀) (s : VG.X86_64.State) (i : Nat)
    (hs : VG.Proof.TripleDes.X86_64.Bitsliced.CopyInv src dst A B n s₀ i s) :
    WP isa (.loop (.block (copyBody src dst)) .ne) s (VG.Proof.TripleDes.X86_64.Bitsliced.CopyPost src dst A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => VG.Proof.TripleDes.X86_64.Bitsliced.CopyInv src dst A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega]; exact hs, by omega⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  have hsrc : src ≠ .rax ∧ src ≠ .rdx := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hdst : dst ≠ .rax ∧ dst ≠ .rdx := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hsd' : src ≠ dst := by rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  -- mov rax, [src]
  let v := s₀.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A j) 64
  have hv : s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A j) 64 = v :=
    inv.frame.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  let s₁ := s.setReg .rax v
  have e₁ : exec (.mov .rax (.mem { base := src, disp := 0 })) s = some s₁ := by
    have hea : s.ea { base := src, disp := 0 } = VG.Proof.TripleDes.X86_64.Bitsliced.wAt A j := by
      show s.gpr src + BitVec.ofInt 64 0 = _
      rw [inv.src]; simp; rfl
    have hr : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A j) 8 := by rw [inv.rd, inv.wr]; exact hpre.read j hj
    simp only [exec, readSrc, State.load64, hea, hr, ite_true, hv, Option.map_some]
    rfl
  -- store [dst], rax
  have hea₂ : s₁.ea { base := dst, disp := 0 } = VG.Proof.TripleDes.X86_64.Bitsliced.wAt B j := by
    show s₁.gpr dst + BitVec.ofInt 64 0 = _
    simp only [s₁, gpr_setReg_of_ne (s := s) v hdst.1, inv.dst]; simp; rfl
  have hw : InRegions s₁.wr (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B j) 8 := by
    simp only [s₁, wr_setReg, inv.wr]; exact hpre.write j hj
  let s₂ : VG.X86_64.State := { s₁ with
                              mem := s₁.mem.writeW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B j) v }
  have e₂ : exec (.store { base := dst, disp := 0 } .rax) s₁ = some s₂ := by
    simp only [exec, State.store64, hea₂, hw, ite_true, s₁, gpr_setReg_self]
    rfl
  -- add rsi, 8; add rdi, 8; sub rdx, 1
  have e₃ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_addImm s₂ .rsi 8
  let s₃ := (arithFlags s₂ (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (s₂.gpr .rsi).toNat + ((8 : BitVec 32).signExtend 64).toNat))
      (addOverflow (s₂.gpr .rsi) ((8 : BitVec 32).signExtend 64)
        (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64))).setReg .rsi
      (s₂.gpr .rsi + (8 : BitVec 32).signExtend 64)
  have e₄ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_addImm s₃ .rdi 8
  let s₄ := (arithFlags s₃ (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (s₃.gpr .rdi).toNat + ((8 : BitVec 32).signExtend 64).toNat))
      (addOverflow (s₃.gpr .rdi) ((8 : BitVec 32).signExtend 64)
        (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64))).setReg .rdi
      (s₃.gpr .rdi + (8 : BitVec 32).signExtend 64)
  let c := s₄.gpr .rdx
  let r := c - (1 : BitVec 32).signExtend 64
  let s₅ := (arithFlags s₄ r (decide (c.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow c ((1 : BitVec 32).signExtend 64) r)).setReg .rdx r
  have e₅ : exec (.alu .sub .rdx (.imm 1)) s₄ = some s₅ := rfl
  have run : runBlock isa (copyBody src dst) s = some s₅ := by
    rw [copyBody, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  -- the facts about s₅
  have g₅ : ∀ x, x ≠ .rsi → x ≠ .rdi → x ≠ .rdx → x ≠ .rax → s₅.gpr x = s.gpr x := by
    intro x h1 h2 h3 h4
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg, h1, h2, h3, h4]
  have rsi₅ : s₅.gpr .rsi = s.gpr .rsi + 8 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  have rdi₅ : s₅.gpr .rdi = s.gpr .rdi + 8 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  have rdx₅ : s₅.gpr .rdx = s.gpr .rdx - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg, r, c]
  have mem₅ : s₅.mem = s.mem.writeW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B j) v := by
    simp [s₅, s₄, s₃, s₂, s₁, mem_setReg, mem_arithFlags]
  have rd₅ : s₅.rd = s.rd := by simp [s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  have wr₅ : s₅.wr = s.wr := by simp [s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  have zf₅ : s₅.zf = some (s.gpr .rdx - 1 == 0) := by
    simp only [s₅, zf_setReg, zf_arithFlags, r, c]
    simp [s₄, s₃, s₂, s₁, gpr_setReg]
  have src₅ : s₅.gpr src = VG.Proof.TripleDes.X86_64.Bitsliced.wAt A (j + 1) := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rsi₅, inv.src, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_succ]
    · rw [rdi₅, inv.src, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_succ]
  have dst₅ : s₅.gpr dst = VG.Proof.TripleDes.X86_64.Bitsliced.wAt B (j + 1) := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [rdi₅, inv.dst, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_succ]
    · rw [rsi₅, inv.dst, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_succ]
  have copied₅ : ∀ x < j + 1, s₅.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt B x) 64 = s₀.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)]
      exact inv.copied x (by omega)
  have frame₅ : VG.Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (VG.Proof.TripleDes.X86_64.Bitsliced.wAt_in hj hpre.fitA)
  have regs₅ : ∀ x, x ≠ .rax → x ≠ .rsi → x ≠ .rdi → x ≠ .rdx → s₅.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => (g₅ x h2 h3 h4 h1).trans (inv.regs x h1 h2 h3 h4)
  have cntv : s.gpr .rdx - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [inv.cnt, show n - j = m by omega]
    exact VG.Proof.TripleDes.X86_64.Bitsliced.cnt_sub m (by omega)
  by_cases h1 : m = 1
  · left
    refine ⟨?_, ?_⟩
    · show s₅.zf.map (!·) = some false
      rw [zf₅, cntv, h1]; rfl
    · refine ⟨?_, ?_, ?_, frame₅, regs₅, rd₅.trans inv.rd, wr₅.trans inv.wr⟩
      · rw [src₅]; congr 1; omega
      · rw [dst₅]; congr 1; omega
      · intro x hx; exact copied₅ x (by omega)
  · right
    refine ⟨?_, m - 1, by omega, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, rd₅.trans inv.rd,
      wr₅.trans inv.wr⟩, by omega⟩
    · show s₅.zf.map (!·) = some true
      rw [zf₅, cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by have := hpre.fitA; omega)] at this
        omega
      rw [this]; rfl
    · omega
    · rw [src₅]; congr 1; omega
    · rw [dst₅]; congr 1; omega
    · rw [rdx₅, cntv]; congr 1; omega
    · intro x hx; exact copied₅ x (by omega)

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Transpose`. -/
section

/-!
# The transposition of the state, by evaluation

The transposition only moves and XORs bits of the 64 state words (slots
0–63), and masks them with constants: the lane domain evaluates it on
words of atoms (bit `t` of word `i` is atom `64 i + t`), and the check
that bit `p` of word `j` is then atom `64 p + j` proves that it transposes
any 64 words (`transpose_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64.Bitslice
open VG.Proof.TripleDes.Bitslice (transposeW)

/-- The spill slots and the state words. -/
def stateCfg : Cfg := { base := .rcx, slots := 72, ext := .rsp, exts := 0 }

def transEnv : Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if 8 ≤ k ∧ k < 72 then some (inWord (k - 8)) else none }

def transPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot (stSlot j) == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    VG.X86_64.Straight.check (lanes 64 12) VG.Proof.TripleDes.X86_64.Bitsliced.stateCfg (fun _ => none) (instrs transposeProg.lit) VG.Proof.TripleDes.X86_64.Bitsliced.transEnv VG.Proof.TripleDes.X86_64.Bitsliced.transPost = true := by
  decide +kernel

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

/-- The spill slots and the state words (slots 0–71). -/
def stateR (s : VG.X86_64.State) : Region := ⟨s.gpr .rcx, 576⟩

theorem transpose_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' j = transposeW (VG.Proof.TripleDes.X86_64.Bitsliced.words s) j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.stateR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.TripleDes.X86_64.Bitsliced.transpose_check
  rw [VG.Proof.TripleDes.X86_64.Bitsliced.transpose_code] at he
  have hok : Ok VG.Proof.TripleDes.X86_64.Bitsliced.stateCfg s :=
    Ok.of_region h.scratch rfl (by show 8 * 72 ≤ 1024; decide) (by decide) rfl
  have hrel : Rel (LaneRel 12 (assign (VG.Proof.TripleDes.X86_64.Bitsliced.words s) (2 ^ 12))) VG.Proof.TripleDes.X86_64.Bitsliced.stateCfg (fun _ => none) VG.Proof.TripleDes.X86_64.Bitsliced.transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl => ?_), (fun _ _ hj => ?_)⟩
    swap
    · exact absurd hj (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.stateCfg])
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.transEnv] at hsl
    split at hsl
    · rename_i hk
      simp only [Option.some.injEq] at hsl
      subst hsl
      have e : VG.Proof.TripleDes.X86_64.Bitsliced.sl s j = VG.Proof.TripleDes.X86_64.Bitsliced.words s (j - 8) := by
        simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words, stSlot]; rw [show 8 + (j - 8) = j by omega]
      show LaneRel 12 _ _ (s.mem.readW (wordAddr (s.gpr .rcx) j) 64)
      rw [show s.mem.readW (wordAddr (s.gpr .rcx) j) 64 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s j from rfl, e]
      exact inWord_rel (VG.Proof.TripleDes.X86_64.Bitsliced.words s) (by omega)
    · cases hsl
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, p.base, p.ext, p.frame⟩
  have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  have hs := p.rel.slot (stSlot j) _ (by unfold stSlot; show 8 + j < 72; omega) (beq_iff_eq.mp hpj)
  have bits := outWord_rel (fun q hq a ha => by simp at ha; omega) hs
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hsj : VG.Proof.TripleDes.X86_64.Bitsliced.words s' j = s'.mem.readW (wordAddr (s'.gpr stateCfg.base) (stSlot j)) 64 := rfl
  rw [hsj, bits b hb]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
    decide_true, Bool.true_and]
  exact VG.Bitslice.bitOf_word (VG.Proof.TripleDes.X86_64.Bitsliced.words s) b j hj

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.BatchIO`. -/
section

/-!
# The start and end of a batch

The batch's size (`batchSize`), the copies of its blocks into and out of
the state words (`copyIn`, `copyOut`), counting the passes
(`passesStart`), and the advance of the data pointer and the count of
blocks left (`batchEnd`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice

/-! ## Storing registers in scratch slots -/

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < 128)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => st p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, VG.Proof.TripleDes.X86_64.Bitsliced.sl s' p.1 = s.gpr p.2) ∧ (∀ x < 128, (∀ p ∈ l, p.1 ≠ x) → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := p.2) h hp
    let s₁ : VG.X86_64.State := { s with
                               mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem s p.1 (s.gpr p.2) }
    have h₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₁ := h.congr rfl rfl
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', zf', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', zf', (VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)),
          VG.Proof.TripleDes.X86_64.Bitsliced.sl_st s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)),
        VG.Proof.TripleDes.X86_64.Bitsliced.sl_st s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-! ## The batch's size -/

theorem batchSize_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    WP isa batchSize s (fun s' => VG.Proof.TripleDes.X86_64.Bitsliced.sl s' batchSlot = BitVec.ofNat 64 (min (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat 64) ∧
      (∀ x < 128, x ≠ batchSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem) := by
  let m := VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot
  let s₁ := s.setReg .rax m
  have e₁ : exec (ld .rax leftSlot) s = some s₁ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h (by decide) .rax
  let t₁ := arithFlags s₁ (s₁.gpr .rax - (64 : BitVec 32).signExtend 64)
    (decide ((s₁.gpr .rax).toNat < ((64 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₁.gpr .rax) ((64 : BitVec 32).signExtend 64) (s₁.gpr .rax - (64 : BitVec 32).signExtend 64))
  have run₁ : runBlock isa [ld .rax leftSlot, .alu .cmp .rax (.imm 64)] s = some t₁ := by
    rw [runBlock_cons, e₁, runStep_some, VG.Proof.TripleDes.X86_64.Bitsliced.cmp_run]
  have rax₁ : t₁.gpr .rax = m := by simp [t₁, s₁, gpr_setReg]
  have cf₁ : t₁.cf = some (decide (m.toNat < 64)) := by
    simp only [t₁, cf_arithFlags, s₁, gpr_setReg_self]; rfl
  have ht₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₁ := h.congr (by simp [t₁, s₁, gpr_setReg]) (by simp [t₁, s₁, wr_setReg, wr_arithFlags])
  -- the value of `rax` after the branch, and the rest
  have finish : ∀ t : VG.X86_64.State, VG.Proof.TripleDes.X86_64.Bitsliced.Room t → t.gpr .rax = BitVec.ofNat 64 (min m.toNat 64) →
      (∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl t x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) → t.gpr .rcx = s.gpr .rcx → t.gpr .rsp = s.gpr .rsp →
      t.rd = s.rd → t.wr = s.wr → VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem t.mem →
      WP isa (.block [st batchSlot .rax]) t (fun s' =>
        VG.Proof.TripleDes.X86_64.Bitsliced.sl s' batchSlot = BitVec.ofNat 64 (min (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat 64) ∧
        (∀ x < 128, x ≠ batchSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
        s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem) := by
    intro t ht hrax hsl hc hsp hrd hwr hf
    have e := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rax) ht (by decide : batchSlot < 128)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_⟩
    refine ⟨?_, fun x hx hne => ?_, hc, hsp, hrd, hwr, ?_⟩
    · rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st t (by decide) _ (by decide)]; simp [hrax, m]
    · rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st t (by decide) _ hx]; simp [hne, hsl x hx]
    · have f := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := t) (by decide : batchSlot < 128) (t.gpr .rax)
      rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR t = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, hc]] at f
      exact hf.trans f
  have sl₁ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl t₁ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x _; simp only [t₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags, s₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx)]
  have c₁ : t₁.gpr .rcx = s.gpr .rcx := by simp [t₁, s₁, gpr_setReg]
  have sp₁ : t₁.gpr .rsp = s.gpr .rsp := by simp [t₁, s₁, gpr_setReg]
  have rd₁ : t₁.rd = s.rd := by simp [t₁, s₁, rd_setReg, rd_arithFlags]
  have wr₁ : t₁.wr = s.wr := by simp [t₁, s₁, wr_setReg, wr_arithFlags]
  have f₁ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem t₁.mem := by
    simp only [t₁, s₁, mem_setReg, mem_arithFlags]; exact Frame.refl _ _
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  apply WP.seq
  apply WP.ite (decide (m.toNat < 64)) cf₁
  · intro hlt
    apply WP.block_nil
    refine finish t₁ ht₁ ?_ sl₁ c₁ sp₁ rd₁ wr₁ f₁
    rw [rax₁]
    have : m.toNat < 64 := by simpa using hlt
    rw [Nat.min_eq_left (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro hge
    have : ¬ m.toNat < 64 := by simpa using hge
    have e := VG.Proof.TripleDes.X86_64.Bitsliced.exec_movImm t₁ .rax 64
    let t₂ := t₁.setReg .rax ((64 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨t₂, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_⟩
    refine finish t₂ (ht₁.congr (by simp [t₂, gpr_setReg]) (by simp [t₂, wr_setReg])) ?_
      (fun x hx => by simp only [t₂, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx)]; exact sl₁ x hx)
      (by simp [t₂, gpr_setReg, c₁]) (by simp [t₂, gpr_setReg, sp₁]) (by simp [t₂, rd_setReg, rd₁])
      (by simp [t₂, wr_setReg, wr₁]) (by simp only [t₂, mem_setReg]; exact f₁)
    rw [Nat.min_eq_right (by omega)]
    simp [t₂, gpr_setReg]

/-! ## Copying the batch in and out -/

/-- The state words' area. -/
abbrev stateA (s : VG.X86_64.State) : Addr := VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rcx) 8

theorem wAt_stateA (c : Addr) (j : Nat) : VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.wAt c 8) j = wordAddr c (stSlot j) := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.wAt, wordAddr, stSlot, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

/-- What the prologue of the copies leaves: the public words in `r8`–`r11`,
the data pointer in `rsi`, the state's in `rdi`, the count in `rdx`. -/
structure KeepPost (s t : VG.X86_64.State) : Prop where
  r8 : t.gpr .r8 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot
  r9 : t.gpr .r9 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot
  r10 : t.gpr .r10 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot
  r11 : t.gpr .r11 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s batchSlot
  rsi : t.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot
  rdi : t.gpr .rdi = VG.Proof.TripleDes.X86_64.Bitsliced.stateA s
  rdx : t.gpr .rdx = VG.Proof.TripleDes.X86_64.Bitsliced.sl s batchSlot
  rcx : t.gpr .rcx = s.gpr .rcx
  rsp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem keep_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ t, runBlock isa (keepIn ++ [VG.Impl.TripleDes.X86_64.Bitslice.rr .rsi .r9, VG.Impl.TripleDes.X86_64.Bitslice.rr .rdi .rcx, .alu .add .rdi (.imm 64), VG.Impl.TripleDes.X86_64.Bitslice.rr .rdx .r11]) s
      = some t ∧ VG.Proof.TripleDes.X86_64.Bitsliced.KeepPost s t := by
  let t₁ := s.setReg .r8 (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot)
  let t₂ := t₁.setReg .r9 (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot)
  let t₃ := t₂.setReg .r10 (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot)
  let t₄ := t₃.setReg .r11 (VG.Proof.TripleDes.X86_64.Bitsliced.sl s batchSlot)
  let t₅ := t₄.setReg .rsi (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot)
  let t₆ := t₅.setReg .rdi (s.gpr .rcx)
  have e₁ : exec (ld .r8 schedSlot) s = some t₁ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h (by decide) .r8
  have h₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₁ := h.congr (by simp [t₁, gpr_setReg]) (by simp [t₁, wr_setReg])
  have e₂ : exec (ld .r9 dataSlot) t₁ = some t₂ := by
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h₁ (by decide) .r9, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide)]
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₂ := h₁.congr (by simp [t₂, gpr_setReg]) (by simp [t₂, wr_setReg])
  have e₃ : exec (ld .r10 leftSlot) t₂ = some t₃ := by
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h₂ (by decide) .r10, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide), VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide)]
  have h₃ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₃ := h₂.congr (by simp [t₃, gpr_setReg]) (by simp [t₃, wr_setReg])
  have e₄ : exec (ld .r11 batchSlot) t₃ = some t₄ := by
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h₃ (by decide) .r11, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide), VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide),
      VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide)]
  have e₅ : exec (VG.Impl.TripleDes.X86_64.Bitslice.rr .rsi .r9) t₄ = some t₅ := by
    simp only [VG.Impl.TripleDes.X86_64.Bitslice.rr, exec, readSrc, Option.map_some, t₅]
    simp [t₄, t₃, t₂, gpr_setReg]
  have e₆ : exec (VG.Impl.TripleDes.X86_64.Bitslice.rr .rdi .rcx) t₅ = some t₆ := by
    simp only [VG.Impl.TripleDes.X86_64.Bitslice.rr, exec, readSrc, Option.map_some, t₆]
    simp [t₅, t₄, t₃, t₂, t₁, gpr_setReg]
  have e₇ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_addImm t₆ .rdi 64
  let t₇ := (arithFlags t₆ (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64)
      (decide (2 ^ 64 ≤ (t₆.gpr .rdi).toNat + ((64 : BitVec 32).signExtend 64).toNat))
      (addOverflow (t₆.gpr .rdi) ((64 : BitVec 32).signExtend 64)
        (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64))).setReg .rdi
      (t₆.gpr .rdi + (64 : BitVec 32).signExtend 64)
  let t₈ := t₇.setReg .rdx (t₇.gpr .r11)
  have e₈ : exec (VG.Impl.TripleDes.X86_64.Bitslice.rr .rdx .r11) t₇ = some t₈ := rfl
  refine ⟨t₈, ?_, ?_⟩
  · simp only [keepIn, List.cons_append, List.nil_append]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons,
      e₆, runStep_some, runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
        mem_arithFlags, rd_arithFlags, wr_arithFlags, VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt]

theorem wAt_zero (p : Addr) : VG.Proof.TripleDes.X86_64.Bitsliced.wAt p 0 = p := by simp [VG.Proof.TripleDes.X86_64.Bitsliced.wAt]

/-- The data words of the batch: readable and writable, apart from the scratch buffer. -/
structure DataOk (s : VG.X86_64.State) (D : Addr) (k : Nat) : Prop where
  read : ∀ i < k, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D i) 8
  write : ∀ i < k, InRegions s.wr (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D i) 8
  sep : (⟨D, 8 * k⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s)
  fit : 8 * k < 2 ^ 64

theorem state_in (s : VG.X86_64.State) {k : Nat} (hk : k ≤ 64) :
    Region.Sub ⟨VG.Proof.TripleDes.X86_64.Bitsliced.stateA s, 8 * k⟩ (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s) := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt, VG.Proof.TripleDes.X86_64.Bitsliced.scratchR]
  exact Offset.sub_base _ (by omega)

theorem copyIn_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : VG.Proof.TripleDes.X86_64.Bitsliced.sl s batchSlot = BitVec.ofNat 64 k)
    (h1 : 1 ≤ k) (h64 : k ≤ 64) (hd : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k) :
    WP isa copyIn s (fun s' => (∀ j < k, VG.Proof.TripleDes.X86_64.Bitsliced.words s' j = s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) j) 64) ∧
      (∀ x < 128, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem) := by
  obtain ⟨t, run, kp⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.keep_ok h
  apply WP.seq
  refine WP.of_runBlock ⟨t, run, ?_⟩
  apply WP.seq
  have pre : VG.Proof.TripleDes.X86_64.Bitsliced.CopyPre (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) (VG.Proof.TripleDes.X86_64.Bitsliced.stateA s) k t := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hd.fit⟩
    · rw [kp.rd, kp.wr]; exact hd.read i hi
    · rw [kp.wr, VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_stateA]
      exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, h.scratch, VG.Proof.TripleDes.X86_64.Bitsliced.slot_in_scratch s (by unfold stSlot; omega)⟩
    · exact (hd.sep.sub_right (VG.Proof.TripleDes.X86_64.Bitsliced.state_in s h64))
  have inv : VG.Proof.TripleDes.X86_64.Bitsliced.CopyInv .rsi .rdi (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) (VG.Proof.TripleDes.X86_64.Bitsliced.stateA s) k t 0 t := by
    refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [kp.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_zero]
    · rw [kp.rdi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_zero]
    · rw [kp.rdx, hk]; simp
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.copy_ok (Or.inl ⟨rfl, rfl⟩) pre t 0 inv)
  intro u pu
  have hu : VG.Proof.TripleDes.X86_64.Bitsliced.Room u := h.congr (by rw [pu.regs _ (by decide) (by decide) (by decide) (by decide), kp.rcx])
    (by rw [pu.wr, kp.wr])
  have r8 := pu.regs .r8 (by decide) (by decide) (by decide) (by decide)
  have r9 := pu.regs .r9 (by decide) (by decide) (by decide) (by decide)
  have r10 := pu.regs .r10 (by decide) (by decide) (by decide) (by decide)
  have r11 := pu.regs .r11 (by decide) (by decide) (by decide) (by decide)
  have rcx := pu.regs .rcx (by decide) (by decide) (by decide) (by decide)
  have rsp := pu.regs .rsp (by decide) (by decide) (by decide) (by decide)
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.stores_ok hu
    [(schedSlot, .r8), (dataSlot, .r9), (leftSlot, .r10), (batchSlot, .r11)] (by decide) (by decide)
  refine WP.of_runBlock ⟨v, runv, ?_⟩
  have ufr : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem u.mem := by
    rw [← kp.mem]
    exact pu.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, List.mem_singleton_self _, VG.Proof.TripleDes.X86_64.Bitsliced.state_in s h64⟩
  have slu : ∀ x < 128, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl u x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x hx hl
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, rcx, kp.rcx]
    rw [← kp.mem]
    refine pu.frame.readW (r := ⟨wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt, wordAddr]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have wu : ∀ j < k, VG.Proof.TripleDes.X86_64.Bitsliced.words u j = s.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) j) 64 := by
    intro j hj
    have e := pu.copied j hj
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_stateA, kp.mem] at e
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words, VG.Proof.TripleDes.X86_64.Bitsliced.sl, rcx, kp.rcx]
    exact e
  have notIn : ∀ x, x ≠ schedSlot → x ≠ dataSlot → x ≠ leftSlot → x ≠ batchSlot →
      ∀ p ∈ [(schedSlot, Reg.r8), (dataSlot, .r9), (leftSlot, .r10), (batchSlot, .r11)], p.1 ≠ x := by
    intro x a b c d p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> [exact Ne.symm a; exact Ne.symm b;
      exact Ne.symm c; exact Ne.symm d]
  have cu : u.gpr .rcx = s.gpr .rcx := rcx.trans kp.rcx
  refine ⟨fun j hj => ?_, fun x hx hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words]
    rw [keepv _ (by unfold stSlot; omega) (notIn _ (by unfold stSlot schedSlot; omega)
      (by unfold stSlot dataSlot; omega) (by unfold stSlot leftSlot; omega)
      (by unfold stSlot batchSlot; omega))]
    exact wu j hj
  · by_cases a : x = schedSlot
    · subst a; rw [setv (schedSlot, .r8) (by simp), r8, kp.r8]
    by_cases b : x = dataSlot
    · subst b; rw [setv (dataSlot, .r9) (by simp), r9, kp.r9]
    by_cases c : x = leftSlot
    · subst c; rw [setv (leftSlot, .r10) (by simp), r10, kp.r10]
    by_cases d : x = batchSlot
    · subst d; rw [setv (batchSlot, .r11) (by simp), r11, kp.r11]
    rw [keepv x hx (notIn x a b c d), slu x hx hl]
  · rw [gv, cu]
  · rw [gv, rsp, kp.rsp]
  · rw [rdv, pu.rd, kp.rd]
  · rw [wrv, pu.wr, kp.wr]
  · rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR u = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, cu]] at fv
    exact ufr.trans fv

structure OutPost (s : VG.X86_64.State) (k : Nat) (s' : VG.X86_64.State) : Prop where
  data : ∀ j < k, s'.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) j) 64 = VG.Proof.TripleDes.X86_64.Bitsliced.words s j
  slots : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x
  r8 : s'.gpr .r8 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot
  r10 : s'.gpr .r10 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot
  r11 : s'.gpr .r11 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s batchSlot
  rsi : s'.gpr .rsi = VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : VG.Frame [⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot, 8 * k⟩] s.mem s'.mem

theorem copyOut_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) {k : Nat} (hk : VG.Proof.TripleDes.X86_64.Bitsliced.sl s batchSlot = BitVec.ofNat 64 k)
    (h1 : 1 ≤ k) (h64 : k ≤ 64) (hd : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k) :
    WP isa copyOut s (VG.Proof.TripleDes.X86_64.Bitsliced.OutPost s k) := by
  obtain ⟨t, run, kp⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.keep_ok h
  apply WP.seq
  refine WP.of_runBlock ⟨t, run, ?_⟩
  have pre : VG.Proof.TripleDes.X86_64.Bitsliced.CopyPre (VG.Proof.TripleDes.X86_64.Bitsliced.stateA s) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k t := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, hd.fit⟩
    · rw [kp.rd, kp.wr, VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_stateA]
      exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, List.mem_append_right _ h.scratch, VG.Proof.TripleDes.X86_64.Bitsliced.slot_in_scratch s (by unfold stSlot; omega)⟩
    · rw [kp.wr]; exact hd.write i hi
    · exact (hd.sep.sub_right (VG.Proof.TripleDes.X86_64.Bitsliced.state_in s h64)).symm
  have inv : VG.Proof.TripleDes.X86_64.Bitsliced.CopyInv .rdi .rsi (VG.Proof.TripleDes.X86_64.Bitsliced.stateA s) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k t 0 t := by
    refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩
    · rw [kp.rdi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_zero]
    · rw [kp.rsi, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_zero]
    · rw [kp.rdx, hk]; simp
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.copy_ok (Or.inr ⟨rfl, rfl⟩) pre t 0 inv)
  intro u pu
  have rcx := pu.regs .rcx (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun j hj => ?_, fun x hx => ?_, ?_, ?_, ?_, pu.dst, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pu.copied j hj, kp.mem, VG.Proof.TripleDes.X86_64.Bitsliced.stateA, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_stateA]; rfl
  · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, rcx, kp.rcx]
    rw [← kp.mem]
    refine pu.frame.readW (r := ⟨wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sep.sub_right (Offset.sub_base (s.gpr .rcx) (d := 8 * x) (n := 8) (k := 1024)
      (by omega))).symm
  · rw [pu.regs .r8 (by decide) (by decide) (by decide) (by decide), kp.r8]
  · rw [pu.regs .r10 (by decide) (by decide) (by decide) (by decide), kp.r10]
  · rw [pu.regs .r11 (by decide) (by decide) (by decide) (by decide), kp.r11]
  · rw [rcx, kp.rcx]
  · rw [pu.regs .rsp (by decide) (by decide) (by decide) (by decide), kp.rsp]
  · rw [pu.rd, kp.rd]
  · rw [pu.wr, kp.wr]
  · rw [← kp.mem]; exact pu.frame

/-! ## The end of a batch -/

theorem batchEnd_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ s', runBlock isa batchEnd s = some s' ∧ VG.Proof.TripleDes.X86_64.Bitsliced.sl s' schedSlot = s.gpr .r8 ∧
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s' dataSlot = s.gpr .rsi ∧ VG.Proof.TripleDes.X86_64.Bitsliced.sl s' leftSlot = s.gpr .r10 - s.gpr .r11 ∧
      s'.zf = some (s.gpr .r10 - s.gpr .r11 == 0) ∧
      (∀ x < 128, x ≠ schedSlot → x ≠ dataSlot → x ≠ leftSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ :=
    VG.Proof.TripleDes.X86_64.Bitsliced.stores_ok h [(schedSlot, .r8), (dataSlot, .rsi)] (by decide) (by decide)
  have hv : VG.Proof.TripleDes.X86_64.Bitsliced.Room v := h.congr (by rw [gv]) wrv
  let d := s.gpr .r10 - s.gpr .r11
  let v₁ := v.setReg .rax (v.gpr .r10)
  have e₁ : exec (VG.Impl.TripleDes.X86_64.Bitslice.rr .rax .r10) v = some v₁ := rfl
  let v₂ := (arithFlags v₁ (v₁.gpr .rax - v₁.gpr .r11) (decide ((v₁.gpr .rax).toNat < (v₁.gpr .r11).toNat))
    (subOverflow (v₁.gpr .rax) (v₁.gpr .r11) (v₁.gpr .rax - v₁.gpr .r11))).setReg .rax
    (v₁.gpr .rax - v₁.gpr .r11)
  have e₂ : exec (.alu .sub .rax (.reg .r11)) v₁ = some v₂ := rfl
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room v₂ := hv.congr (by simp [v₂, v₁, gpr_setReg]) (by simp [v₂, v₁, wr_setReg, wr_arithFlags])
  have e₃ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rax) h₂ (by decide : leftSlot < 128)
  have rax₂ : v₂.gpr .rax = d := by simp [v₂, v₁, gpr_setReg, gv, d]
  refine ⟨{ v₂ with mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem v₂ leftSlot (v₂.gpr .rax) }, ?_, ?_, ?_, ?_, ?_, fun x hx a b c => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · show runBlock isa ([st schedSlot .r8, st dataSlot .rsi] ++
      ([VG.Impl.TripleDes.X86_64.Bitslice.rr .rax .r10, .alu .sub .rax (.reg .r11), st leftSlot .rax] : List Instr)) s = _
    exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some runv (by
      rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
        runStep_some, runBlock_nil])
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st v₂ (by decide) _ (by decide)]
    simp only [show schedSlot ≠ leftSlot by decide, ite_false, v₂, v₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx),
      VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags]
    rw [setv (schedSlot, .r8) (by simp)]
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st v₂ (by decide) _ (by decide)]
    simp only [show dataSlot ≠ leftSlot by decide, ite_false, v₂, v₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx),
      VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags]
    rw [setv (dataSlot, .rsi) (by simp)]
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st v₂ (by decide) _ (by decide)]; simp only [ite_true, rax₂, d]
  · simp [v₂, v₁, gpr_setReg, gv]
  · rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st v₂ (by decide) _ hx]
    simp only [c, ite_false, v₂, v₁, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide : Reg.rax ≠ .rcx), VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags]
    exact keepv x hx (by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only <;> [exact Ne.symm a; exact Ne.symm b])
  · simp [v₂, v₁, gpr_setReg, gv]
  · simp [v₂, v₁, gpr_setReg, gv]
  · simp [v₂, v₁, rd_setReg, rd_arithFlags, rdv]
  · simp [v₂, v₁, wr_setReg, wr_arithFlags, wrv]
  · have f := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := v₂) (by decide : leftSlot < 128) (v₂.gpr .rax)
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR v₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s by simp [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, v₂, v₁, gpr_setReg, gv]] at f
    have m₂ : v₂.mem = v.mem := by simp [v₂, v₁, mem_setReg, mem_arithFlags]
    rw [m₂] at f
    exact fv.trans f

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Bytes`. -/
section

/-!
# Blocks as little-endian words

A block's little-endian word holds bit `i` of the block (big-endian, as
`decodeBlock` reads it) at bit `i ^^^ 56`: the byte order is reversed.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

theorem getLsbD_bswap64 (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (bswap64 x).getLsbD p = x.getLsbD (p ^^^ 56) := by
  rw [xor56_eq p hp]
  have hj : p % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [bswap64, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem xor56_lt {p : Nat} (hp : p < 64) : p ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hp (by decide)

theorem xor56_xor56' (a : Nat) : a ^^^ 56 ^^^ 56 = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The little-endian word of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [decodeBlock_readW, VG.Proof.TripleDes.X86_64.Bitsliced.getLsbD_bswap64 _ (VG.Proof.TripleDes.X86_64.Bitsliced.xor56_lt hj), VG.Proof.TripleDes.X86_64.Bitsliced.xor56_xor56']

/-- A word whose bits are those of `x` at `j ^^^ 56` is the little-endian word of
the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    VG.Spec.TripleDes.blockAt m p = VG.Spec.TripleDes.encodeBlock x := by
  have hw : m.readW p 64 = bswap64 x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [h j hj, VG.Proof.TripleDes.X86_64.Bitsliced.getLsbD_bswap64 _ hj]
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, VG.Spec.TripleDes.encodeBlock, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m p (n := 8) hi]
  have e : (m.read p 8) = m.readW p 64 := by simp only [Mem.readW]; rfl
  rw [e, hw]
  exact bswap64_byte x i hi

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Batch`. -/
section

/-!
# A batch

A batch of `k = min(n, 64)` blocks is copied into the state words,
transposed (lane `b` is then IP of block `b`), put through the three
passes, transposed back and copied out: each block becomes its TDEA
encryption or decryption (`batch_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW)

/-- What ECB does to one block. -/
def blockOut (K : VG.Spec.TripleDes.Schedule) : VG.Spec.TripleDes.Direction → VG.Spec.TripleDes.Block → VG.Spec.TripleDes.Block
  | .encrypt => VG.Spec.TripleDes.encryptBlock K
  | .decrypt => VG.Spec.TripleDes.decryptBlock K

theorem ipLane_congr {w : Nat} {W W' : Nat → BitVec w} (hW : ∀ x < 64, W x = W' x) (b : Nat) :
    ipLane W b = ipLane W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht, VG.Proof.TripleDes.Bitslice.ipLane_bit _ _ ht,
    hW _ (VG.Proof.TripleDes.Bitslice.ipWord_lt t ht)]

/-! ## The data words -/

theorem DataOk.congr {s s' : VG.X86_64.State} {D : Addr} {k : Nat} (h : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s D k)
    (hc : s'.gpr .rcx = s.gpr .rcx) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s' D k where
  read := by rw [hrd, hwr]; exact h.read
  write := by rw [hwr]; exact h.write
  sep := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, hc]; exact h.sep
  fit := h.fit

theorem DataOk.mono {s : VG.X86_64.State} {D : Addr} {k n : Nat} (h : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s D n) (hk : k ≤ n) :
    VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s D k where
  read i hi := h.read i (by omega)
  write i hi := h.write i (by omega)
  sep := h.sep.sub_left (Region.sub_prefix (by omega))
  fit := by have := h.fit; omega

theorem word_sub {D : Addr} {b k : Nat} (hb : b < k) :
    Region.Sub ⟨VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b, 8⟩ ⟨D, 8 * k⟩ :=
  Offset.sub_base D (by omega)

/-- A data word of the batch is unchanged by writes to the scratch buffer. -/
theorem DataOk.readW {s : VG.X86_64.State} {D : Addr} {k : Nat} (h : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s D k) {b : Nat} (hb : b < k)
    {m m' : Mem} (hf : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] m m') : m'.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) 64 = m.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) 64 :=
  hf.readW (r := ⟨VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.sep.sub_left (VG.Proof.TripleDes.X86_64.Bitsliced.word_sub hb))
    (by decide)

/-! ## Transposing -/

theorem state_toScratch {s : VG.X86_64.State} {m m' : Mem} (h : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.stateR s] m m') :
    VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem transpose_ok' {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧ (∀ j < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s' j = transposeW (VG.Proof.TripleDes.X86_64.Bitsliced.words s) j) ∧
      (∀ x < 128, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧ VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s'.mem := by
  obtain ⟨s', run, w, rd, wr, c, sp, f⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.transpose_ok h
  refine ⟨s', run, w, fun x hx hl => ?_, rd, wr, c, sp, VG.Proof.TripleDes.X86_64.Bitsliced.state_toScratch f⟩
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.sl, c]
  refine f.readW (r := ⟨Straight.wordAddr (s.gpr .rcx) x, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base (s.gpr .rcx) (d := 8 * x) (n := 8) (k := 576) (by omega) (by omega)

/-! ## The batch -/

/-- What a batch needs: the scratch buffer, a block left, the batch's data
words, and the schedule's words, readable and apart from the scratch buffer. -/
structure BatchPre (s : VG.X86_64.State) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s
  pos : 1 ≤ (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat
  data : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) (min (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat 64)
  sched : ∀ i < 48, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot + BitVec.ofNat 64 (8 * i))
  schedSep : (⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot, 384⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s)

structure BatchPost (d : VG.Spec.TripleDes.Direction) (s : VG.X86_64.State) (k : Nat) (s' : VG.X86_64.State) : Prop where
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  out : ∀ b < k, VG.Spec.TripleDes.blockAt s'.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot)) d (VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) b))
  data : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' dataSlot = VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k
  left : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' leftSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot - BitVec.ofNat 64 k
  zf : s'.zf = some (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot - BitVec.ofNat 64 k == 0)
  sched : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' schedSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot
  saved : ∀ x < 78, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, ⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot, 8 * k⟩] s.mem s'.mem

/-- The result of a block, from the three passes between IP and FP. -/
theorem blockOut_cores (K : VG.Spec.TripleDes.Schedule) (d : VG.Spec.TripleDes.Direction) (B : VG.Spec.TripleDes.Block) :
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut K d B = VG.Spec.TripleDes.encodeBlock (permute fp (match d with
      | .encrypt => VG.Proof.TripleDes.desCore (componentSchedule K 2) .encrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .decrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 0) .encrypt (permute ip (VG.Spec.TripleDes.decodeBlock B))))
      | .decrypt => VG.Proof.TripleDes.desCore (componentSchedule K 0) .decrypt
          (VG.Proof.TripleDes.desCore (componentSchedule K 1) .encrypt
            (VG.Proof.TripleDes.desCore (componentSchedule K 2) .decrypt
              (permute ip (VG.Spec.TripleDes.decodeBlock B)))))) := by
  cases d
  · exact VG.Proof.TripleDes.encryptBlock_eq_cores K B
  · exact VG.Proof.TripleDes.decryptBlock_eq_cores K B

theorem frame_into {rs : List Region} {m m' : Mem} {r : Region} (h : VG.Frame [r] m m') (hr : r ∈ rs) :
    VG.Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : VG.Spec.TripleDes.Direction) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.BatchPre s) :
    WP isa (batch d) s (VG.Proof.TripleDes.X86_64.Bitsliced.BatchPost d s (min (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat 64)) := by
  have hpos := h.pos
  generalize hk : min (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat 64 = k
  have hk1 : 1 ≤ k := by omega
  have hk64 : k ≤ 64 := by omega
  have hdata : VG.Proof.TripleDes.X86_64.Bitsliced.DataOk s (VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot) k := hk ▸ h.data
  let D := VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot
  let S := VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot
  let L : List Region := [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, ⟨D, 8 * k⟩]
  have inL : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s ∈ L := List.mem_cons_self
  have dL : (⟨D, 8 * k⟩ : Region) ∈ L := List.mem_cons_of_mem _ List.mem_cons_self
  rw [batch]
  -- the batch's size
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.batchSize_ok h.room)
  rintro s₁ ⟨bs₁, sl₁, c₁, sp₁, rd₁, wr₁, f₁⟩
  rw [hk] at bs₁
  have h₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₁ := h.room.congr c₁ wr₁
  have D₁ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ dataSlot = D := sl₁ _ (by decide) (by decide)
  -- the copy in
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.copyIn_ok h₁ bs₁ hk1 hk64 (by rw [D₁]; exact hdata.congr c₁ rd₁ wr₁))
  rintro s₂ ⟨w₂, sl₂, c₂, sp₂, rd₂, wr₂, f₂⟩
  have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₂ := h₁.congr c₂ wr₂
  -- the transposition, and the count of passes
  apply WP.seq
  obtain ⟨t₃, run₃, w₃, sl₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.transpose_ok' h₂
  have ht₃ : VG.Proof.TripleDes.X86_64.Bitsliced.Room t₃ := h₂.congr c₃ wr₃
  let u₃ := t₃.setReg .rax ((3 : BitVec 32).signExtend 64)
  have hu₃ : VG.Proof.TripleDes.X86_64.Bitsliced.Room u₃ := ht₃.congr (by simp [u₃, gpr_setReg]) (by simp [u₃, wr_setReg])
  have e₃ := VG.Proof.TripleDes.X86_64.Bitsliced.exec_st (r := Reg.rax) hu₃ (by decide : passSlot < 128)
  let s₃ : VG.X86_64.State := { u₃ with
                              mem := VG.Proof.TripleDes.X86_64.Bitsliced.stMem u₃ passSlot (u₃.gpr .rax) }
  refine WP.of_runBlock ⟨s₃, VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some run₃ (by
    rw [passesStart, runBlock_cons, VG.Proof.TripleDes.X86_64.Bitsliced.exec_movImm, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil]), ?_⟩
  have uc₃ : u₃.gpr .rcx = t₃.gpr .rcx := by simp [u₃, gpr_setReg]
  have c₃' : s₃.gpr .rcx = s₂.gpr .rcx := uc₃.trans c₃
  have slu₃ : ∀ x < 128, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ x = if x = passSlot then (3 : BitVec 32).signExtend 64 else VG.Proof.TripleDes.X86_64.Bitsliced.sl t₃ x := by
    intro x hx
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.sl_st u₃ (by decide) _ hx, VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg _ (by decide)]
    simp [u₃, gpr_setReg]
  have h₃ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₃ := hu₃.congr rfl rfl
  have rd₃' : s₃.rd = s₂.rd := by simp [s₃, u₃, rd_setReg, rd₃]
  have wr₃' : s₃.wr = s₂.wr := by simp [s₃, u₃, wr_setReg, wr₃]
  have sp₃' : s₃.gpr .rsp = s₂.gpr .rsp := by simp [s₃, u₃, gpr_setReg, sp₃]
  have f₃' : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂] s₂.mem s₃.mem := by
    have f := VG.Proof.TripleDes.X86_64.Bitsliced.stMem_frame (s := u₃) (by decide : passSlot < 128) (u₃.gpr .rax)
    rw [show VG.Proof.TripleDes.X86_64.Bitsliced.scratchR u₃ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, uc₃, c₃]] at f
    exact f₃.trans (by simpa only [u₃, mem_setReg] using f)
  have words₃ : ∀ j < 64, VG.Proof.TripleDes.X86_64.Bitsliced.words s₃ j = transposeW (VG.Proof.TripleDes.X86_64.Bitsliced.words s₂) j := by
    intro j hj
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words]
    have hp : stSlot j ≠ passSlot := by unfold stSlot passSlot; omega
    rw [slu₃ _ (by unfold stSlot; omega)]
    simp only [hp, ↓reduceIte]
    exact w₃ j hj
  have misc₃ : ∀ x < 128, 72 ≤ x → x ≠ passSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₂ x := by
    intro x hx hl hp
    rw [slu₃ x hx]
    simp only [hp, ↓reduceIte]
    exact sl₃ x hx hl
  -- slots of the batch's start that the passes keep
  have keep₃ : ∀ x < 128, 72 ≤ x → x ≠ batchSlot → x ≠ passSlot → VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s x := by
    intro x hx hl hb hp
    rw [misc₃ x hx hl hp, sl₂ x hx hl, sl₁ x hx hb]
  have S₃ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ schedSlot = S := keep₃ _ (by decide) (by decide) (by decide) (by decide)
  have cs₃ : s₃.gpr .rcx = s.gpr .rcx := c₃'.trans (c₂.trans c₁)
  have rds₃ : s₃.rd = s.rd := rd₃'.trans (rd₂.trans rd₁)
  have wrs₃ : s₃.wr = s.wr := wr₃'.trans (wr₂.trans wr₁)
  have scr₁ : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₁]
  have scr₂ : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₂ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, c₂, c₁]
  have fs₃ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s₃.mem := by
    rw [scr₁] at f₂; rw [scr₂] at f₃'
    exact (f₁.trans f₂).trans f₃'
  -- the passes
  apply WP.seq
  have hS₃ : ∀ i < 48, VG.Proof.TripleDes.X86_64.Bitsliced.Apart s₃ (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ schedSlot + BitVec.ofNat 64 (8 * i)) := by
    intro i hi; rw [S₃]; exact (h.sched i hi).congr cs₃ rds₃ wrs₃
  have inv₃ : VG.Proof.TripleDes.X86_64.Bitsliced.PassesInv d s₃ 3 s₃ :=
    ⟨h₃, rfl, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl,
      by rw [slu₃ _ (by decide)]; rfl, fun _ _ _ _ _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.passes_ok d hS₃ 3 s₃ inv₃)
  intro s₄ q₄
  have h₄ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₄ := q₄.room
  -- the transposition back
  apply WP.seq
  obtain ⟨s₅, run₅, w₅, sl₅, rd₅, wr₅, c₅, sp₅, f₅⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.transpose_ok' h₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have h₅ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₅ := h₄.congr c₅ wr₅
  have cs₅ : s₅.gpr .rcx = s.gpr .rcx := c₅.trans (q₄.rcx.trans cs₃)
  have rds₅ : s₅.rd = s.rd := rd₅.trans (q₄.rd.trans rds₃)
  have wrs₅ : s₅.wr = s.wr := wr₅.trans (q₄.wr.trans wrs₃)
  have keep₅ : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
      VG.Proof.TripleDes.X86_64.Bitsliced.sl s₅ x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ x := fun x hx hl a b c e => (sl₅ x hx hl).trans (q₄.misc x hx hl a b c e)
  have D₅ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₅ dataSlot = D := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide)]
  have B₅ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₅ batchSlot = BitVec.ofNat 64 k := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      misc₃ _ (by decide) (by decide) (by decide), sl₂ _ (by decide) (by decide), bs₁]
  -- the copy out
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.copyOut_ok h₅ B₅ hk1 hk64 (by rw [D₅]; exact hdata.congr cs₅ rds₅ wrs₅))
  intro s₆ o₆
  have h₆ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₆ := h₅.congr o₆.rcx o₆.wr
  -- the end
  obtain ⟨s₇, run₇, sch₇, dat₇, left₇, zf₇, oth₇, c₇, sp₇, rd₇, wr₇, f₇⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.batchEnd_ok h₆
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have cs₆ : s₆.gpr .rcx = s.gpr .rcx := o₆.rcx.trans cs₅
  have L₅ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₅ leftSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot := by
    rw [keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide)]
  have diff : s₆.gpr .r10 - s₆.gpr .r11 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot - BitVec.ofNat 64 k := by
    rw [o₆.r10, o₆.r11, L₅, B₅]
  -- the whole frame
  have frame : VG.Frame L s.mem s₇.mem := by
    have a : VG.Frame L s.mem s₃.mem := VG.Proof.TripleDes.X86_64.Bitsliced.frame_into fs₃ inL
    have b : VG.Frame L s₃.mem s₄.mem := by
      have := q₄.frame; simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, cs₃] at this; exact VG.Proof.TripleDes.X86_64.Bitsliced.frame_into this inL
    have c : VG.Frame L s₄.mem s₅.mem := by
      have := f₅; simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, q₄.rcx, cs₃] at this; exact VG.Proof.TripleDes.X86_64.Bitsliced.frame_into this inL
    have e : VG.Frame L s₅.mem s₆.mem := by
      have := o₆.frame; rw [D₅] at this; exact VG.Proof.TripleDes.X86_64.Bitsliced.frame_into this dL
    have g : VG.Frame L s₆.mem s₇.mem := by
      have := f₇; simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, cs₆] at this; exact VG.Proof.TripleDes.X86_64.Bitsliced.frame_into this inL
    exact (((a.trans b).trans c).trans e).trans g
  refine ⟨c₇.trans cs₆, sp₇.trans (o₆.rsp.trans (sp₅.trans (q₄.rsp.trans (sp₃'.trans
    (sp₂.trans sp₁))))), rd₇.trans (o₆.rd.trans rds₅), wr₇.trans (o₆.wr.trans wrs₅), ?_,
    by rw [dat₇, o₆.rsi, D₅], by rw [left₇, diff], by rw [zf₇, diff],
    by rw [sch₇, o₆.r8, keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      S₃],
    fun x hx hl => ?_, frame⟩
  · -- every block of the batch
    intro b hb
    have hb64 : b < 64 := by omega
    let K₃ := VG.Spec.TripleDes.scheduleAt s₃.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₃ schedSlot)
    have K₃eq : K₃ = VG.Spec.TripleDes.scheduleAt s.mem S := by
      simp only [K₃, S₃]
      exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S fs₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.schedSep)
    -- lane `b` after the first transposition: IP of the block
    have lane₃ : ipLane (VG.Proof.TripleDes.X86_64.Bitsliced.words s₃) b = permute ip (VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b))) := by
      rw [VG.Proof.TripleDes.X86_64.Bitsliced.ipLane_congr words₃ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb64 fun j hj => ?_
      simp only [VG.Proof.TripleDes.X86_64.Bitsliced.words] at w₂ ⊢
      rw [w₂ b hb, D₁, hdata.readW hb f₁]
      exact VG.Proof.TripleDes.X86_64.Bitsliced.readW_bit s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) hj
    -- the block's word at the end
    have word₇ : s₇.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) 64 = transposeW (VG.Proof.TripleDes.X86_64.Bitsliced.words s₄) b := by
      have e₇ : s₇.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) 64 = s₆.mem.readW (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) 64 := by
        have := (hdata.congr cs₆ (o₆.rd.trans rds₅) (o₆.wr.trans wrs₅)).readW hb f₇
        exact this
      rw [e₇, ← D₅, o₆.data b hb, w₅ b hb64]
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.blockOut_cores, ← K₃eq]
    apply VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_of_readW
    intro j hj
    rw [word₇, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj, VG.Proof.TripleDes.X86_64.Bitsliced.ipLane_congr q₄.words b,
      VG.Proof.TripleDes.X86_64.Bitsliced.chain_lane d _ _ hb64, lane₃]
  · have ne : ∀ y, 78 ≤ y → x ≠ y := fun y hy e => by omega
    rw [oth₇ x (by omega) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)), o₆.slots x (by omega),
      keep₅ x (by omega) hl (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide)),
      keep₃ x (by omega) hl (ne _ (by decide)) (ne _ (by decide))]

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit`. -/
section

namespace VG

materialize_code Impl.TripleDes.X86_64.Bitslice.encrypt
materialize_code Impl.TripleDes.X86_64.Bitslice.decrypt

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.ConstantTime`. -/
section

/-!
# Constant time

The pointers, the count of blocks and the stack pointer are public; so is
everything the function computes from them (the batches' sizes, the counts
of passes and rounds, the addresses of the round keys), which it keeps in
public slots of the scratch buffer.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64

def ecbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [0, 1024], bases := [(.rcx, 1, 0)] }

/-! The analyses of the function, as summaries, which the wider batches'
analyses use for the code they end with. -/

taint_summary encSum : taintS VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint Impl.TripleDes.X86_64.Bitslice.encrypt
taint_summary decSum : taintS VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint Impl.TripleDes.X86_64.Bitslice.decrypt

theorem encrypt_constantTime (pre : VG.X86_64.State → Prop) (pub : VG.X86_64.State → VG.X86_64.State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.Bitslice.encrypt :=
  let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk encSum (by decide +kernel)
  VG.Taint.constantTime (A := taintS) VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint hagree h

theorem decrypt_constantTime (pre : VG.X86_64.State → Prop) (pub : VG.X86_64.State → VG.X86_64.State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint s t) :
    ConstantTime isa pre pub Impl.TripleDes.X86_64.Bitslice.decrypt :=
  let ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk decSum (by decide +kernel)
  VG.Taint.constantTime (A := taintS) VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint hagree h

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Ecb`. -/
section

/-!
# The function

After saving the callee-saved registers and its arguments in the scratch
buffer, the function runs batches of up to 64 blocks until none are left
(`loop_ok`), then restores the registers (`ecb_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes

/-! ## Memory -/

theorem wAt_wAt (D : Addr) (a i : Nat) : VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D a) i = VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (a + i) := by
  simp only [VG.Proof.TripleDes.X86_64.Bitsliced.wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : VG.Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : VG.Spec.TripleDes.blockAt m' p = VG.Spec.TripleDes.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem toNat_ofNat_of_le {m n : Nat} (hm : m ≤ n) (hn : 8 * n ≤ 2 ^ 64) :
    (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in: the
data's `n` blocks at `sl s₀ dataSlot` and the schedule at
`sl s₀ schedSlot`, apart from each other and the scratch buffer. -/
structure BatchesEnv (s₀ : VG.X86_64.State) (n : Nat) : Prop where
  room : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₀
  dataIn : ∀ i < n, InRegions s₀.wr (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot) i) 8
  dataSep : (⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot, 8 * n⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀)
  fit : 8 * n ≤ 2 ^ 64
  keyRead : ∀ i < 48, InRegions (s₀.rd ++ s₀.wr) (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot + BitVec.ofNat 64 (8 * i)) 8
  keySep : (⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot, 384⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀)
  keyData : (⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot, 384⟩ : Region).Disjoint ⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot, 8 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : VG.Spec.TripleDes.Direction) (s₀ : VG.X86_64.State) (n m : Nat) (s : VG.X86_64.State) : Prop where
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ n
  left : VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot = BitVec.ofNat 64 m
  data : VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot = VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot) (n - m)
  sched : VG.Proof.TripleDes.X86_64.Bitsliced.sl s schedSlot = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot
  saved : ∀ x < 78, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x
  done : ∀ b < n - m, VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot)) d (VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot) b))
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, ⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot, 8 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : VG.Spec.TripleDes.Direction) (s₀ : VG.X86_64.State) (n : Nat) (s : VG.X86_64.State) : Prop where
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ x < 78, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x
  done : ∀ b < n, VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot)) d (VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot) b))
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, ⟨VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot, 8 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : VG.Spec.TripleDes.Direction} {s₀ : VG.X86_64.State} {n m : Nat} (E : VG.Proof.TripleDes.X86_64.Bitsliced.BatchesEnv s₀ n) {s : VG.X86_64.State}
    (h : VG.Proof.TripleDes.X86_64.Bitsliced.BatchesInv d s₀ n m s) : VG.Proof.TripleDes.X86_64.Bitsliced.BatchPre s := by
  have hp := h.pos
  have hl := h.le
  have hm : (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat = m := by rw [h.left]; exact VG.Proof.TripleDes.X86_64.Bitsliced.toNat_ofNat_of_le h.le E.fit
  have scr : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀ := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, h.rcx]
  refine ⟨E.room.congr h.rcx h.wr, by omega, ?_, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rw [hm, h.data]
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega⟩
    · rw [VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt, h.rd, h.wr]
      obtain ⟨r, hr, hc⟩ := E.dataIn (n - m + i) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt, h.wr]; exact E.dataIn (n - m + i) (by omega)
    · rw [scr]
      exact E.dataSep.sub_left (Offset.sub_base _ (by omega))
  · rw [h.sched, h.rd, h.wr]; exact E.keyRead i hi
  · rw [h.sched, scr]; exact E.keySep.sub_left (Offset.sub_base _ (by omega))
  · rw [h.sched, scr]; exact E.keySep

theorem loop_ok (d : VG.Spec.TripleDes.Direction) {s₀ : VG.X86_64.State} {n : Nat} (E : VG.Proof.TripleDes.X86_64.Bitsliced.BatchesEnv s₀ n) (m : Nat) (s : VG.X86_64.State)
    (hs : VG.Proof.TripleDes.X86_64.Bitsliced.BatchesInv d s₀ n m s) : WP isa (.loop (batch d) .ne) s (VG.Proof.TripleDes.X86_64.Bitsliced.BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.X86_64.Bitsliced.BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.batch_ok d (h.batchPre E))
  intro s' q
  have hm : (VG.Proof.TripleDes.X86_64.Bitsliced.sl s leftSlot).toNat = m := by rw [h.left]; exact VG.Proof.TripleDes.X86_64.Bitsliced.toNat_ofNat_of_le h.le E.fit
  rw [hm] at q
  generalize hk : min m 64 = k at q
  have hk1 : 1 ≤ k := by have := h.pos; omega
  have hkm : k ≤ m := by omega
  let D := VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot
  let S := VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot
  have hD : VG.Proof.TripleDes.X86_64.Bitsliced.sl s dataSlot = VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (n - m) := h.data
  obtain ⟨qrcx, qrsp, qrd, qwr, qout, qdata, qleft, qzf, qsched, qsaved, qframe⟩ := q
  rw [hD, h.sched] at qout
  rw [hD] at qframe qdata
  have scr : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀ := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, h.rcx]
  -- the memory written so far
  have frame' : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, ⟨D, 8 * (n - (m - k))⟩] s₀.mem s'.mem := by
    have f₁ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, ⟨D, 8 * (n - (m - k))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega)⟩
    have f₂ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, ⟨D, 8 * (n - (m - k))⟩] s.mem s'.mem := qframe.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀, List.mem_cons_self, by rw [scr]; exact fun _ h => h⟩
      · exact ⟨⟨D, 8 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Offset.sub_base _ (by omega)⟩
    exact f₁.trans f₂
  have done' : ∀ b < n - (m - k), VG.Spec.TripleDes.blockAt s'.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) =
      VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem S) d (VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b)) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame qframe fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [scr]; exact E.dataSep.sub_left (Offset.sub_base _ (by omega))
      · simp only [VG.Proof.TripleDes.X86_64.Bitsliced.wAt]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := qout j (by omega)
      rw [VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt] at e
      rw [e]
      have hK : VG.Spec.TripleDes.scheduleAt s.mem S = VG.Spec.TripleDes.scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.keySep
          · exact E.keyData.sub_right (Region.sub_prefix (by omega))
      have hB : VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (n - m + j)) = VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D (n - m + j)) :=
        VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact E.dataSep.sub_left (Offset.sub_base _ (by omega))
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB]
  have left' : VG.Proof.TripleDes.X86_64.Bitsliced.sl s' leftSlot = BitVec.ofNat 64 (m - k) := by
    rw [qleft, h.left, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have zf' : s'.zf = some (BitVec.ofNat 64 (m - k) == 0) := by
    rw [qzf, h.left, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have saved' : ∀ x < 78, 72 ≤ x → VG.Proof.TripleDes.X86_64.Bitsliced.sl s' x = VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ x := fun x hx hl =>
    (qsaved x hx hl).trans (h.saved x hx hl)
  have rcx' := qrcx.trans h.rcx
  have rsp' := qrsp.trans h.rsp
  have rd' := qrd.trans h.rd
  have wr' := qwr.trans h.wr
  by_cases hend : m ≤ 64
  · have hkm' : k = m := by omega
    left
    refine ⟨?_, rcx', rsp', rd', wr', saved', ?_, ?_⟩
    · show s'.zf.map (!·) = some false
      rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk64 : k = 64 := by omega
    right
    refine ⟨?_, m - k, by omega, ⟨rcx', rsp', rd', wr', by omega, by omega, left', ?_,
      by rw [qsched, h.sched], saved', done', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf']
      have : (BitVec.ofNat 64 (m - k) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [VG.Proof.TripleDes.X86_64.Bitsliced.toNat_ofNat_of_le (show m - k ≤ n by have := h.le; omega) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega
      rw [this]; rfl
    · rw [qdata, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_wAt]; congr 1; omega

/-! ## Setting up and restoring -/

def setupStores : List (Nat × Reg) :=
  [(72, .rbx), (73, .rbp), (74, .r12), (75, .r13), (76, .r14), (77, .r15),
   (schedSlot, .rdi), (dataSlot, .rsi), (leftSlot, .rdx)]

theorem setup_eq :
    setup = setupStores.map (fun p => st p.1 p.2) ++ ([.alu .cmp .rdx (.imm 0)] : List Instr) := rfl

theorem restore_eq : VG.Impl.TripleDes.X86_64.Bitslice.restore = savedRegs.map (fun p => ld p.1 p.2) := rfl

/-- A block of loads of distinct registers, other than `rcx`, from scratch slots. -/
theorem loads_ok {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.Room s) (l : List (Reg × Nat)) (hl : ∀ p ∈ l, p.2 < 128 ∧ p.1 ≠ .rcx)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => ld p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧
      (∀ p ∈ l, s'.gpr p.1 = VG.Proof.TripleDes.X86_64.Bitsliced.sl s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, (fun _ h => by cases h), fun _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := VG.Proof.TripleDes.X86_64.Bitsliced.exec_ld h hp.1 p.1
    let s₁ := s.setReg p.1 (VG.Proof.TripleDes.X86_64.Bitsliced.sl s p.2)
    have c₁ : s₁.gpr .rcx = s.gpr .rcx := gpr_setReg_of_ne (s := s) _ (Ne.symm hp.2)
    have h₁ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₁ := h.congr c₁ (by simp [s₁, wr_setReg])
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₁ j = VG.Proof.TripleDes.X86_64.Bitsliced.sl s j := VG.Proof.TripleDes.X86_64.Bitsliced.sl_setReg s hp.2 _
    refine ⟨s', ?_, by rw [m']; simp [s₁, mem_setReg], fun q hq => ?_, fun r hr => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_setReg]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_setReg_of_ne (s := s) _ (Ne.symm (hr p List.mem_cons_self))]

/-! ## The function -/

/-- What the function needs: the scratch buffer and the data writable, the
schedule readable, apart from each other and the return address. -/
structure EcbPre (s : VG.X86_64.State) : Prop where
  scratch : (⟨s.gpr .rcx, 1024⟩ : Region) ∈ s.wr
  dataIn : ∀ i < (s.gpr .rdx).toNat, InRegions s.wr (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) i) 8
  keyIn : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * i)) 8
  keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩
  retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

/-- `EcbPre` from the regions of the contract. -/
theorem EcbPre.of_regions {s : VG.X86_64.State} (hrd : s.rd = [⟨s.gpr .rdi, 384⟩])
    (hwr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩])
    (keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64) : VG.Proof.TripleDes.X86_64.Bitsliced.EcbPre s where
  scratch := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  dataIn i hi := by
    rw [hwr]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
  keyIn i hi := by
    rw [hrd]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
  keyData := keyData
  keyBuf := keyBuf
  dataBuf := dataBuf
  retData := retData
  retBuf := retBuf
  fit := fit

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers and the return address are kept, and
only the scratch buffer and the data change. -/
structure EcbPost (d : VG.Spec.TripleDes.Direction) (s s' : VG.X86_64.State) : Prop where
  gpr : gprPreserved s s'
  done : ∀ b < (s.gpr .rdx).toNat, VG.Spec.TripleDes.blockAt s'.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b) =
    VG.Proof.TripleDes.X86_64.Bitsliced.blockOut (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d (VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt (s.gpr .rsi) b))
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩] s.mem s'.mem

theorem ecb_blocks (K : VG.Spec.TripleDes.Schedule) (d : VG.Spec.TripleDes.Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, VG.Spec.TripleDes.blockAt m' (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) = VG.Proof.TripleDes.X86_64.Bitsliced.blockOut K d (VG.Spec.TripleDes.blockAt m (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b))) :
    VG.Spec.TripleDes.blocksAt m' D n = Spec.TripleDes.ecb K d (VG.Spec.TripleDes.blocksAt m D n) := by
  simp only [VG.Spec.TripleDes.blocksAt, Spec.TripleDes.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  exact h b (List.mem_range.mp hb)

theorem ecb_ok (d : VG.Spec.TripleDes.Direction) {s : VG.X86_64.State} (h : VG.Proof.TripleDes.X86_64.Bitsliced.EcbPre s) : WP isa (ecb d) s (VG.Proof.TripleDes.X86_64.Bitsliced.EcbPost d s) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  have hroom : VG.Proof.TripleDes.X86_64.Bitsliced.Room s := ⟨h.scratch⟩
  rw [Impl.TripleDes.X86_64.Bitslice.ecb]
  -- the setup
  apply WP.seq
  obtain ⟨v, runv, gv, rdv, wrv, -, fv, setv, keepv⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.stores_ok hroom VG.Proof.TripleDes.X86_64.Bitsliced.setupStores (by decide) (by decide)
  let s₀ := arithFlags v (v.gpr .rdx - (0 : BitVec 32).signExtend 64)
    (decide ((v.gpr .rdx).toNat < ((0 : BitVec 32).signExtend 64).toNat))
    (subOverflow (v.gpr .rdx) ((0 : BitVec 32).signExtend 64) (v.gpr .rdx - (0 : BitVec 32).signExtend 64))
  have e₀ : exec (.alu .cmp .rdx (.imm 0)) v = some s₀ := rfl
  refine WP.of_runBlock ⟨s₀, by
    rw [VG.Proof.TripleDes.X86_64.Bitsliced.setup_eq]; exact VG.Proof.TripleDes.X86_64.Bitsliced.runBlock_cat_some runv (by rw [runBlock_cons, e₀, runStep_some, runBlock_nil]), ?_⟩
  have g₀ : s₀.gpr = s.gpr := by simp only [s₀, gpr_arithFlags, gv]
  have rd₀ : s₀.rd = s.rd := by simp only [s₀, rd_arithFlags, rdv]
  have wr₀ : s₀.wr = s.wr := by simp only [s₀, wr_arithFlags, wrv]
  have mem₀ : s₀.mem = v.mem := by simp only [s₀, mem_arithFlags]
  have sl₀ : ∀ j, VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ j = VG.Proof.TripleDes.X86_64.Bitsliced.sl v j := fun j => VG.Proof.TripleDes.X86_64.Bitsliced.sl_arithFlags _ _ _ _ j
  have f₀ : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s] s.mem s₀.mem := by rw [mem₀]; exact fv
  have scr₀ : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₀ = VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s := by simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, g₀]
  have D₀ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ dataSlot = D := by rw [sl₀, setv (dataSlot, .rsi) (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.setupStores])]
  have S₀ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ schedSlot = S := by rw [sl₀, setv (schedSlot, .rdi) (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.setupStores])]
  have L₀ : VG.Proof.TripleDes.X86_64.Bitsliced.sl s₀ leftSlot = s.gpr .rdx := by rw [sl₀, setv (leftSlot, .rdx) (by simp [VG.Proof.TripleDes.X86_64.Bitsliced.setupStores])]
  have zf₀ : s₀.zf = some (s.gpr .rdx == 0) := by
    simp only [s₀, zf_arithFlags, gv]
    rw [show s.gpr .rdx - BitVec.signExtend 64 (0 : BitVec 32) = s.gpr .rdx by simp]
  have hn : 8 * n ≤ 2 ^ 64 := by have := h.fit; omega
  -- the schedule and the data blocks are as on entry
  have K₀ : VG.Spec.TripleDes.scheduleAt s₀.mem S = VG.Spec.TripleDes.scheduleAt s.mem S :=
    VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₀ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  have B₀ : ∀ b < n, VG.Spec.TripleDes.blockAt s₀.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) = VG.Spec.TripleDes.blockAt s.mem (VG.Proof.TripleDes.X86_64.Bitsliced.wAt D b) := fun b hb =>
    VG.Proof.TripleDes.X86_64.Bitsliced.blockAt_frame f₀ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.dataBuf.sub_left (Offset.sub_base _ (by omega))
  -- after the loop (or none), the registers restored
  have finish : ∀ s₂ : VG.X86_64.State, VG.Proof.TripleDes.X86_64.Bitsliced.BatchesPost d s₀ n s₂ → WP isa (.block VG.Impl.TripleDes.X86_64.Bitslice.restore) s₂ (VG.Proof.TripleDes.X86_64.Bitsliced.EcbPost d s) := by
    intro s₂ p
    have h₂ : VG.Proof.TripleDes.X86_64.Bitsliced.Room s₂ := (hroom.congr (by rw [p.rcx, g₀]) (by rw [p.wr, wr₀]))
    obtain ⟨s', run', m', set', keep'⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.loads_ok h₂ VG.Impl.TripleDes.X86_64.Bitslice.savedRegs (by decide) (by decide)
    refine WP.of_runBlock ⟨s', by rw [VG.Proof.TripleDes.X86_64.Bitsliced.restore_eq]; exact run', ?_⟩
    have frame : VG.Frame [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s, ⟨D, 8 * n⟩] s.mem s'.mem := by
      rw [m']
      have := p.frame
      rw [scr₀, D₀] at this
      exact (f₀.mono (by simp)).trans this
    refine ⟨⟨fun r hr => ?_, ?_⟩, fun b hb => ?_, frame⟩
    · have saved : ∀ q ∈ VG.Impl.TripleDes.X86_64.Bitslice.savedRegs, s'.gpr q.1 = s.gpr q.1 := by
        intro q hq
        rw [set' q hq, p.saved q.2 (by revert hq q; decide) (by revert hq q; decide), sl₀]
        refine (setv (q.2, q.1) ?_).trans rfl
        revert hq q; decide
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact saved (.rbx, 72) (by decide)
      · exact saved (.rbp, 73) (by decide)
      · rw [keep' .rsp (by decide), p.rsp, g₀]
      · exact saved (.r12, 74) (by decide)
      · exact saved (.r13, 75) (by decide)
      · exact saved (.r14, 76) (by decide)
      · exact saved (.r15, 77) (by decide)
    · refine frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.retBuf
      · exact h.retData
    · have e := p.done b hb
      rw [D₀, S₀, K₀, B₀ b hb, ← m'] at e
      exact e
  apply WP.seq
  apply WP.ite (s.gpr .rdx == 0) zf₀
  · intro hz
    apply WP.block_nil
    have hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₀ ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun b hb => by omega, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    have hn1 : 1 ≤ n := by
      have : s.gpr .rdx ≠ 0 := by simpa using hz
      have : (s.gpr .rdx).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega
    have E : VG.Proof.TripleDes.X86_64.Bitsliced.BatchesEnv s₀ n := by
      refine ⟨hroom.congr (by rw [g₀]) wr₀, fun i hi => ?_, ?_, hn, fun i hi => ?_, ?_, ?_⟩
      · rw [wr₀, D₀]; exact h.dataIn i hi
      · rw [D₀, scr₀]; exact h.dataBuf
      · rw [rd₀, wr₀, S₀]; exact h.keyIn i hi
      · rw [S₀, scr₀]; exact h.keyBuf
      · rw [S₀, D₀]; exact h.keyData
    have I : VG.Proof.TripleDes.X86_64.Bitsliced.BatchesInv d s₀ n n s₀ := by
      refine ⟨rfl, rfl, rfl, rfl, hn1, Nat.le_refl _, ?_, ?_, rfl, fun _ _ _ => rfl,
        fun b hb => by omega, by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [L₀]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, VG.Proof.TripleDes.X86_64.Bitsliced.wAt_zero]
    exact WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.loop_ok d E n s₀ I) finish

end VG.Proof.TripleDes.X86_64.Bitsliced

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified`. -/
section

/-! # The bitsliced ECB functions meet their contracts -/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 384⟩
    let data : Region := ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 1024⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub := VG.Proof.TripleDes.X86_64.PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecbTaint_wf (d : Spec.TripleDes.Direction) (s : VG.X86_64.State) (hs : (VG.Proof.TripleDes.X86_64.Bitsliced.contract d).pre s) :
    Taint.Wf VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, _, _, fit⟩ := hs
  refine ⟨?_, ?_⟩
  · intro _
    rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 8 * (s.gpr .rdx).toNat; omega)
        (List.Forall₂.cons (by change 1024 ≤ 1024; decide) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64; omega
      · change 1024 ≤ 2 ^ 64; decide
  · intro p hp
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbTaint_agree (d : Spec.TripleDes.Direction) (s t : VG.X86_64.State)
    (hs : (VG.Proof.TripleDes.X86_64.Bitsliced.contract d).pre s) (ht : (VG.Proof.TripleDes.X86_64.Bitsliced.contract d).pre t)
    (hp : (VG.Proof.TripleDes.X86_64.Bitsliced.contract d).pub s t) : X86_64.Taint.Agree VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint s t := by
  refine ⟨?_, ?_, VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint_wf d s hs, VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint_wf d t ht, ?_, ?_, ?_⟩
  · constructor
    · intro r hr
      exact hp r (by simpa only [VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint, RegSet.mem_ofList] using hr)
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, hp .rsi (by decide), hp .rdx (by decide), hp .rcx (by decide)]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint, RegSet.not_mem_empty] at hr

def satState : VG.X86_64.State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_correct (s : VG.X86_64.State) (hs : (VG.Proof.TripleDes.X86_64.Bitsliced.contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.Bitslice.encrypt s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.TripleDes.X86_64.Bitsliced.contract .encrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, hp⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.ecb_ok .encrypt (EcbPre.of_regions rd wr kd kb db rdt rb fit)
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.Bitslice.encrypt) (by lit_decide) he hp.gpr,
    VG.Proof.TripleDes.X86_64.Bitsliced.ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem decrypt_correct (s : VG.X86_64.State) (hs : (VG.Proof.TripleDes.X86_64.Bitsliced.contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.Bitslice.decrypt s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.TripleDes.X86_64.Bitsliced.contract .decrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, hp⟩ := VG.Proof.TripleDes.X86_64.Bitsliced.ecb_ok .decrypt (EcbPre.of_regions rd wr kd kb db rdt rb fit)
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.Bitslice.decrypt) (by lit_decide) he hp.gpr,
    VG.Proof.TripleDes.X86_64.Bitsliced.ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem publicRegs_five (s₁ s₂ : VG.X86_64.State) : VG.Proof.TripleDes.X86_64.PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [VG.Proof.TripleDes.X86_64.PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.X86_64.Bitslice.encrypt
    (Proof.TripleDes.ecbEncryptScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.Bitsliced.encrypt_correct
    (VG.Proof.TripleDes.X86_64.Bitsliced.encrypt_constantTime _ _ (VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint_agree .encrypt)) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, VG.Proof.TripleDes.X86_64.Bitsliced.contract, VG.Proof.TripleDes.X86_64.Bitsliced.publicRegs_five] [satState] using VG.Proof.TripleDes.X86_64.Bitsliced.satState

theorem decrypt_verified : Verified target Impl.TripleDes.X86_64.Bitslice.decrypt
    (Proof.TripleDes.ecbDecryptScratchContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.Bitsliced.decrypt_correct
    (VG.Proof.TripleDes.X86_64.Bitsliced.decrypt_constantTime _ _ (VG.Proof.TripleDes.X86_64.Bitsliced.ecbTaint_agree .decrypt)) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, VG.Proof.TripleDes.X86_64.Bitsliced.contract, VG.Proof.TripleDes.X86_64.Bitsliced.publicRegs_five] [satState] using VG.Proof.TripleDes.X86_64.Bitsliced.satState

end VG.Proof.TripleDes.X86_64.Bitsliced

end
