import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.TripleDes.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit`. -/
section

/-! # The AdvSIMD S-box circuits' and transposition's code, and the circuits' output registers, as literals -/

namespace VG.Impl.TripleDes.AArch64.BitsliceNeon

open VG.AArch64

-- The circuits' code and output registers, once, which the literals below,
-- `outRegsTable` and the functions' literals (`Lit`) read rather than run the
-- register allocator again.
materialize_table sboxCompiled 8

-- The transposition, once.
materialize_value transpose

-- Pairs of rounds and the exchange of the halves, once.
materialize_value roundPairEncrypt := roundPair .encrypt
materialize_value roundPairDecrypt := roundPair .decrypt
materialize_value VG.Impl.TripleDes.AArch64.BitsliceNeon.swapHalves

def sbox0 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 0)
def sbox1 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 1)
def sbox2 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 2)
def sbox3 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 3)
def sbox4 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 4)
def sbox5 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 5)
def sbox6 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 6)
def sbox7 : Prog isa := .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode 7)

materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox0
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox1
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox2
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox3
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox4
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox5
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox6
materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.sbox7

def transposeProg : Prog isa := .block transpose

materialize_code VG.Impl.TripleDes.AArch64.BitsliceNeon.transposeProg

end VG.Impl.TripleDes.AArch64.BitsliceNeon

namespace VG

materialize_value Impl.TripleDes.AArch64.BitsliceNeon.outRegsTable

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Machine`. -/
section

/-!
# The AdvSIMD machine state of a batch

The 64 state words are the 16-byte slots at `x4` (`words`), in a writable
region (`Room`). Code that only moves and XORs whole words (the S-box
outputs, the exchange of the halves) is checked on the variable domain,
doubleword lane by doubleword lane (`varsRun`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.AArch64.BitsliceNeon

/-- The state words. -/
def stateCfg : VG.AArch64.StraightV.Cfg := { base := .x4, slots := 64 }

/-- State word `j`. -/
def words (s : VG.AArch64.State) (j : Nat) : BitVec 128 := s.mem.readW (vAddr (s.gpr .x4) j) 128

/-- Doubleword lane `q` of the state words. -/
def laneW (s : VG.AArch64.State) (q : Nat) : Nat → BitVec 64 := fun j => vdword (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s j) q

/-- The state words' area. -/
def stateR (s : VG.AArch64.State) : Region := ⟨s.gpr .x4, 1024⟩

/-- What a batch's code needs of the machine: the state words writable. -/
abbrev Room (s : VG.AArch64.State) : Prop := VG.AArch64.StraightV.Ok VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg s

theorem room_congr {s s' : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hb : s'.gpr .x4 = s.gpr .x4) (hw : s'.wr = s.wr) :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s' := h.congr hb hw

theorem runBlock_cat (a b : List Instr) (s : VG.AArch64.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : VG.AArch64.State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat, h₁, Option.bind_some, h₂]

theorem eq_of_vdword {x y : BitVec 128} (h : ∀ q < 2, vdword x q = vdword y q) : x = y :=
  vec64_ext (h 0 (by decide)) (h 1 (by decide))

/-! ## Words as XORs of variables -/

/-- Slot `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List VReg) : VG.AArch64.StraightV.Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables, in doubleword lane `q`. -/
def varVals (s : VG.AArch64.State) (regs : List VReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s q v else vdword (s.v (regs.getD (v - 64) .v0)) q

def varN (regs : List VReg) : Nat := 64 + regs.length

theorem varEnv_rel {s : VG.AArch64.State} (regs : List VReg) :
    VG.AArch64.StraightV.Rel (fun q => VarRel (VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals s regs q) (VG.Proof.TripleDes.AArch64.BitslicedNeon.varN regs)) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg (VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv regs) s where
  reg r a h q hq := by
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, VG.Proof.TripleDes.AArch64.BitslicedNeon.varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h q hq := by
    have hk' : k < 64 := hk
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, VG.Proof.TripleDes.AArch64.BitslicedNeon.varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals, hk', ite_true, VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW, VG.Proof.TripleDes.AArch64.BitslicedNeon.words, VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg]
  gc _ _ h := by cases h

/-- Run a block that the variable domain accepts on the state words. -/
theorem varsRun {is : List Instr} (regs : List VReg) {post : VG.AArch64.StraightV.Env Nat → Bool}
    (hchk : VG.AArch64.StraightV.check (vars 64) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg is (VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv regs) post = true) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      VG.AArch64.StraightV.Post (fun q => VarRel (VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals s regs q) (VG.Proof.TripleDes.AArch64.BitslicedNeon.varN regs)) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg e' s s'
        (fun r => (is.all fun i => vdstOf i != some r) = false)
        (fun r => (is.all fun i => dstOf i != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := VG.AArch64.StraightV.of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := VG.AArch64.StraightV.run (fun q _ => vars_sound _ _) h (VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-- The all-zero or all-one word. -/
def maskX (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

theorem getLsbD_maskX (b : Bool) {P : Nat} (hP : P < 128) : (VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX b).getLsbD P = b := by
  cases b
  · simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX]
  · simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX, ite_true, BitVec.getLsbD_allOnes, hP, decide_true]

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Sbox`. -/
section

/-!
# The AdvSIMD S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs once,
and the doubleword-lane evaluator (`StraightV`) with the truth-table domain
lifts that check to every bit position of every doubleword of arbitrary
128-bit words. The circuits use only vector registers, and neither the key
nor the zero register.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.Bitslice VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

/-- No slots: the circuits access no memory. -/
def sboxCfg : VG.AArch64.StraightV.Cfg := { base := .x4, slots := 0 }

def sboxEnv : VG.AArch64.StraightV.Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : VG.AArch64.StraightV.Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg j i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    VG.AArch64.StraightV.check (table 64 64) VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxCfg (instrs (VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxLiteral j)) VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxEnv (VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxPost j) = true := by
  lit_decide

theorem sboxLiteral_eq : ∀ j < 8, VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxLiteral j = .block (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j)
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
    (instrs (VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxLiteral j)).all (fun op => vdstOf op != some keyReg && vdstOf op != some zeroReg &&
      dstOf op == none) = true := by
  decide +kernel

/-- Bit `P` of each input register, as the S-box's input. -/
def inputAt (s : VG.AArch64.State) (P : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.v (inReg i)).getLsbD P

theorem inputAt_bit (s : VG.AArch64.State) (P k : Nat) (hk : k < 6) :
    (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt s P).toNat.testBit k = (s.v (inReg k)).getLsbD P := by
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxOk (s : VG.AArch64.State) : VG.AArch64.StraightV.Ok VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxCfg s := ⟨fun _ h => absurd h (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxCfg]), by decide⟩

/-- Every S-box output bit, for arbitrary input words. Memory, the
general-purpose registers and the key and zero registers do not change. -/
theorem sbox_ok (j : Nat) (hj : j < 8) (s : VG.AArch64.State) :
    ∃ s', runBlock isa (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ P < 128, (s'.v (outReg j i)).getLsbD P =
        (Spec.TripleDes.sBox j (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt s P)).getLsbD i) ∧
      s'.gpr = s.gpr ∧ s'.c = s.c ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.v keyReg = s.v keyReg ∧ s'.v zeroReg = s.v zeroReg ∧ s'.mem = s.mem := by
  have codeEq : instrs (VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxLiteral j) = VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j := by rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := VG.AArch64.StraightV.of_check _ _ (VG.Proof.TripleDes.AArch64.BitslicedNeon.sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg j i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j) s = some s' ∧
      VG.AArch64.StraightV.Post (fun q => TableRel p (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt s (64 * q + p)).toNat) VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxCfg e' s s'
        (fun r => ((VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j).all fun op => vdstOf op != some r) = false)
        (fun r => ((VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j).all fun op => dstOf op != some r) = false) := by
    intro p hp
    refine VG.AArch64.StraightV.run (fun q _ => table_sound hp (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt s (64 * q + p)).isLt) (VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxOk s)
      ⟨fun r a h q hq => ?_, (fun _ _ hk _ => absurd hk (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxCfg])), (fun _ _ h => by cases h)⟩ he
    have hc := (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt s (64 * q + p)).isLt
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt_bit s _ k hk6, getLsbD_vdword _ hp]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  have pres := VG.Proof.TripleDes.AArch64.BitslicedNeon.sbox_preserves j hj
  rw [codeEq] at pres
  have pres' := List.all_eq_true.mp pres
  have noV : ∀ r, (r = keyReg ∨ r = zeroReg) →
      ¬ ((VG.Impl.TripleDes.AArch64.BitsliceNeon.sboxCode j).all fun op => vdstOf op != some r) = false := by
    intro r hr
    simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h
    have := pres' op hop
    rcases hr with rfl | rfl <;> simp [h] at this
  have frame0 : s'.mem = s.mem := by
    funext a
    exact p₀.frame a (by simp [VG.AArch64.StraightV.slotRegion, VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxCfg, Region.Contains])
  refine ⟨s', hs', fun i hi P hP => ?_, funext fun r => p₀.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h
      have := pres' op hop
      simp [h] at this),
    p₀.carry, p₀.sp, p₀.rd, p₀.wr, p₀.other _ (noV _ (Or.inl rfl)), p₀.other _ (noV _ (Or.inr rfl)),
    frame0⟩
  obtain ⟨s'', hs'', p₁⟩ := key (P % 64) (Nat.mod_lt _ (by decide))
  rw [hs'] at hs''
  cases hs''
  have h := p₁.rel.reg (outReg j i) _ (hout i hi) (P / 64) (by omega)
  have eP : 64 * (P / 64) + P % 64 = P := Nat.div_add_mod P 64
  simp only [TableRel, outputTable, testBit_tableOf, (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt s _).isLt,
    decide_true, Bool.true_and, eP, getLsbD_vdword _ (Nat.mod_lt _ (by decide) : P % 64 < 64)] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Step`. -/
section

/-!
# One S-box of an AdvSIMD round, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, each the key bit of the
broadcast round key in `v30` as a mask, XORed with the word of `E`; its
circuit; XORing its outputs into their words) does to the state words what
`step` does with the round key's low 48 bits. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

theorem word_in {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (vAddr (s.gpr .x4) w) 16 := by
  obtain ⟨r, hr, hc⟩ := h.slotIn w hw
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem exec_vop (s : VG.AArch64.State) (op : VOp) :
    exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

/-- `0 - ((K <<< (63 - b)) >>> 63)`: bit `b` of `K` as a mask. -/
theorem bitMask (K : BitVec 64) {b : Nat} (hb : b < 64) :
    0 - ((K <<< (63 - b)) >>> 63) = if K.getLsbD b then BitVec.allOnes 64 else 0 := by
  have h : (K <<< (63 - b)) >>> 63 = if K.getLsbD b then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.add_zero, show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
        show ¬ (63 < 63 - b) by omega, decide_false, Bool.not_false, show 63 - (63 - b) = b by omega]
      split <;> simp_all
    · simp only [show ¬ (63 + i < 64) by omega, decide_false, Bool.false_and]
      split <;> simp [BitVec.getLsbD_one, h0]
  rw [h]
  split <;> simp

theorem vdword_maskX (c : Bool) {q : Nat} (hq : q < 2) :
    vdword (VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX c) q = if c then BitVec.allOnes 64 else 0 := by
  cases c
  · simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX, Bool.false_eq_true, ite_false]; exact vdword_zero q
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX, ite_true, vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes, hi,
      decide_true, Bool.true_and, show 64 * q + i < 128 by omega]

/-- The facts the code of an S-box needs: the round key broadcast in `v30`
and zero in `v31`. -/
structure KeyRegs (K : BitVec 64) (s : VG.AArch64.State) : Prop where
  key : s.v keyReg = ofVDwords K K
  zero : s.v zeroReg = 0

theorem KeyRegs.congr {K : BitVec 64} {s s' : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s)
    (hk : s'.v keyReg = s.v keyReg) (hz : s'.v zeroReg = s.v zeroReg) : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s' :=
  ⟨hk.trans h.key, hz.trans h.zero⟩

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ keyReg ∧ inReg i ≠ zeroReg ∧ inReg i ≠ tmpReg := by decide

theorem inReg_inj' : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- One input: key bit `b` as a mask, XORed with state word `w`. -/
theorem inputStep_run {K : BitVec 64} {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hk : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s) {x : VReg}
    (hx : x ≠ keyReg ∧ x ≠ zeroReg ∧ x ≠ tmpReg) {w b : Nat} (hw : w < 64) (hb : b < 64) :
    ∃ s', runBlock isa [.vop (.shift .shl .d2 x keyReg (63 - b)),
        .vop (.shift .ushr .d2 x x 63), .vop (.sub .d2 x zeroReg x),
        .ldrq tmpReg .x4 (16 * w), .vop (.logic .eor x x tmpReg)] s = some s' ∧
      s'.v x = VG.Proof.TripleDes.AArch64.BitslicedNeon.words s w ^^^ VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX (K.getLsbD b) ∧
      (∀ y, y ≠ x → y ≠ tmpReg → s'.v y = s.v y) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c := by
  obtain ⟨hxk, hxz, hxt⟩ := hx
  let v₁ := VArr.d2.map2 (fun w a b' => VShiftOp.shl.eval (63 - b) w a b') (s.v x) (s.v keyReg)
  let s₁ := s.setV x v₁
  have e₁ : exec (.vop (.shift .shl .d2 x keyReg (63 - b))) s = some s₁ := by
    rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.exec_vop]; simp only [VOp.eval, VArr.esize, VShiftOp.ok, show 63 - b < 64 by omega,
      decide_true, ite_true, Option.map_some]; rfl
  let v₂ := VArr.d2.map2 (fun w a b' => VShiftOp.ushr.eval 63 w a b') (s₁.v x) (s₁.v x)
  let s₂ := s₁.setV x v₂
  have e₂ : exec (.vop (.shift .ushr .d2 x x 63)) s₁ = some s₂ := by
    rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.exec_vop]; simp only [VOp.eval, VArr.esize, VShiftOp.ok]; rfl
  let v₃ := VArr.d2.map2 (fun _ a b' => a - b') (s₂.v zeroReg) (s₂.v x)
  let s₃ := s₂.setV x v₃
  have e₃ : exec (.vop (.sub .d2 x zeroReg x)) s₂ = some s₃ := rfl
  have hin : InRegions (s₃.rd ++ s₃.wr) (vAddr (s₃.gpr .x4) w) 16 := VG.Proof.TripleDes.AArch64.BitslicedNeon.word_in h hw
  let s₄ := s₃.setV tmpReg (s₃.mem.readW (vAddr (s₃.gpr .x4) w) 128)
  have e₄ : exec (.ldrq tmpReg .x4 (16 * w)) s₃ = some s₄ := by
    simp only [exec, addr_slot (show 16 * w < 65536 by omega), Option.bind_some, State.load, hin,
      ite_true, Option.map_some, read16_readW]
    rfl
  let s₅ := s₄.setV x (s₄.v x ^^^ s₄.v tmpReg)
  have e₅ : exec (.vop (.logic .eor x x tmpReg)) s₄ = some s₅ := rfl
  -- Through the writes one at a time (`rfl` would first try to unify the states).
  refine ⟨s₅, ?_, ?_, fun y h1 h2 => ?_,
    (gpr_setV _ _ _).trans <| (gpr_setV _ _ _).trans <| (gpr_setV _ _ _).trans <|
      (gpr_setV _ _ _).trans <| gpr_setV _ _ _,
    (mem_setV _ _ _).trans <| (mem_setV _ _ _).trans <| (mem_setV _ _ _).trans <|
      (mem_setV _ _ _).trans <| mem_setV _ _ _,
    (rd_setV _ _ _).trans <| (rd_setV _ _ _).trans <| (rd_setV _ _ _).trans <|
      (rd_setV _ _ _).trans <| rd_setV _ _ _,
    (wr_setV _ _ _).trans <| (wr_setV _ _ _).trans <| (wr_setV _ _ _).trans <|
      (wr_setV _ _ _).trans <| wr_setV _ _ _,
    (sp_setV _ _ _).trans <| (sp_setV _ _ _).trans <| (sp_setV _ _ _).trans <|
      (sp_setV _ _ _).trans <| sp_setV _ _ _, rfl⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · have hv₁ : ∀ q < 2, vdword v₁ q = K <<< (63 - b) := by
      intro q hq
      simp only [v₁, vdword_map2 _ _ _ hq, VShiftOp.eval, hk.key, vdword_dwords _ _ hq, ite_self]
    have hv₂ : ∀ q < 2, vdword v₂ q = (K <<< (63 - b)) >>> 63 := by
      intro q hq
      simp only [v₂, s₁, v_setV_self, vdword_map2 _ _ _ hq, VShiftOp.eval, hv₁ q hq]
    have zx : s₂.v zeroReg = 0 := by
      simp only [s₂, s₁, v_setV_of_ne _ _ (Ne.symm hxz), hk.zero]
    have hv₃ : ∀ q < 2, vdword v₃ q = 0 - ((K <<< (63 - b)) >>> 63) := by
      intro q hq
      simp only [v₃, vdword_map2 _ _ _ hq, zx, vdword_zero, s₂, v_setV_self, hv₂ q hq]
      rfl
    have e : s₅.v x = v₃ ^^^ s.mem.readW (vAddr (s.gpr .x4) w) 128 := by
      simp only [s₅, s₄, s₃, v_setV_self, v_setV_of_ne _ _ hxt]
      rfl
    apply VG.Proof.TripleDes.AArch64.BitslicedNeon.eq_of_vdword; intro q hq
    rw [e, vdword_xor, hv₃ q hq, VG.Proof.TripleDes.AArch64.BitslicedNeon.bitMask K hb, vdword_xor, VG.Proof.TripleDes.AArch64.BitslicedNeon.vdword_maskX _ hq, BitVec.xor_comm]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2]

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN ρ j (n + 1) = VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN ρ j n ++ inputStep ρ j n := by
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

theorem inBit_lt' : ∀ j < 8, ∀ i < 6, inBit j i < 64 := by decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {K : BitVec 64}
    {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hk : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN ρ j n) s = some s' ∧
      (∀ m < n, s'.v (inReg m) = VG.Proof.TripleDes.AArch64.BitslicedNeon.words s (readWord ρ (eBit (inBit j m))) ^^^
        VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX (K.getLsbD (inBit j m))) ∧
      VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.c = s.c := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun m hm => by omega, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, in₁, k₁, g₁, m₁, rd₁, wr₁, sp₁, c₁⟩ := ih (by omega)
    have h₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s₁ := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h (by rw [g₁]) wr₁
    obtain ⟨hxk, hxz, hxt⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.inReg_ne n (by omega)
    obtain ⟨s₂, run₂, q₂, y₂, g₂, m₂, rd₂, wr₂, sp₂, c₂⟩ :=
      VG.Proof.TripleDes.AArch64.BitslicedNeon.inputStep_run h₁ k₁ ⟨hxk, hxz, hxt⟩ (w := readWord ρ (eBit (inBit j n)))
        (VG.Proof.TripleDes.AArch64.BitslicedNeon.readWord_lt ρ j hj _ (by omega)) (VG.Proof.TripleDes.AArch64.BitslicedNeon.inBit_lt' j hj n (by omega))
    refine ⟨s₂, ?_, fun m hm => ?_, k₁.congr (y₂ _ (Ne.symm hxk) (by decide))
        (y₂ _ (Ne.symm hxz) (by decide)), g₂.trans g₁, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, c₂.trans c₁⟩
    · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN_succ]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some run₁ run₂
    · by_cases he : m = n
      · subst he
        rw [q₂]
        simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, m₁, g₁]
      · have hne : inReg m ≠ inReg n := by
          intro e; have := VG.Proof.TripleDes.AArch64.BitslicedNeon.inReg_inj' _ (by omega) _ (by omega) e; omega
        rw [y₂ _ hne (VG.Proof.TripleDes.AArch64.BitslicedNeon.inReg_ne m (by omega)).2.2, in₁ m (by omega)]

/-! ## Outputs -/

def outPost (ρ : Role) (j : Nat) (e : VG.AArch64.StraightV.Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

/-- The output registers of S-box `j`. -/
def outRegs (j : Nat) : List VReg := (List.range 4).map (outReg j)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    VG.AArch64.StraightV.check (vars 64) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg (outputCode ρ j) (VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv (VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs j)) (VG.Proof.TripleDes.AArch64.BitslicedNeon.outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputCode_regs : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => dstOf i == none && vdstOf i != some keyReg &&
      vdstOf i != some zeroReg) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outRegs_getD (j : Nat) {i : Nat} (hi : i < 4) : (VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs j).getD i .v0 = outReg j i := by
  simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs, List.getD_eq_getElem?_getD, hi]

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' k = match outIdx ρ j k with
        | some i => VG.Proof.TripleDes.AArch64.BitslicedNeon.words s k ^^^ s.v (outReg j i)
        | none => VG.Proof.TripleDes.AArch64.BitslicedNeon.words s k) ∧
      s'.gpr = s.gpr ∧ s'.v keyReg = s.v keyReg ∧ s'.v zeroReg = s.v zeroReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c ∧
      Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.varsRun (VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs j) (VG.Proof.TripleDes.AArch64.BitslicedNeon.output_check ρ j hj) h
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp (VG.Proof.TripleDes.AArch64.BitslicedNeon.outputCode_regs ρ j hj)
  have noV : ∀ r, (r = keyReg ∨ r = zeroReg) →
      ¬ ((outputCode ρ j).all fun op => vdstOf op != some r) = false := by
    intro r hr
    simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h'
    have := regs op hop
    rcases hr with rfl | rfl <;> simp [h'] at this
  refine ⟨s', hrun, fun k hk => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other _ (noV _ (Or.inl rfl)), p.other _ (noV _ (Or.inr rfl)), p.rd, p.wr, p.sp, p.carry,
    p.frame⟩
  apply VG.Proof.TripleDes.AArch64.BitslicedNeon.eq_of_vdword; intro q hq
  have hs := p.rel.slot k _ hk (hpost k hk) q hq
  simp only [VarRel] at hs
  have e : vdword (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' k) q = vdword (s'.mem.readW (vAddr (s'.gpr stateCfg.base) k) 128) q := by
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg]
  rw [e, hs]
  split
  · rename_i i hi
    have hi4 := VG.Proof.TripleDes.AArch64.BitslicedNeon.outIdx_lt ρ j k i hi
    rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.xorSet_two_pow_xor (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.varN, VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs]; omega) (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.varN, VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs]; omega)]
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals, hk, ite_true, show ¬ 64 + i < 64 by omega, ite_false,
      Nat.add_sub_cancel_left, vdword_xor, VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW, VG.Proof.TripleDes.AArch64.BitslicedNeon.outRegs_getD j hi4]
  · rw [xorSet_two_pow _ (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.varN]; omega)]
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals, hk, ite_true, VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW]

/-! ## One S-box -/

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {K : BitVec 64} {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s)
    (hk : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = VG.Proof.TripleDes.Bitslice.step ρ (K.setWidth 48) j (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s) x) ∧
      VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c ∧
      Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, in₁, k₁, g₁, m₁, rd₁, wr₁, sp₁, c₁⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.inputsN_ok ρ hj (Nat.le_refl 6) h hk
  obtain ⟨s₂, run₂, out₂, g₂, c₂, sp₂, rd₂, wr₂, kk₂, kz₂, m₂⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.sbox_ok j hj s₁
  have h₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s₂ := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h (by rw [g₂, g₁]) (wr₂.trans wr₁)
  obtain ⟨s₃, run₃, w₃, g₃, kk₃, kz₃, rd₃, wr₃, sp₃, c₃, f₃⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.outputs_ok ρ hj h₂
  have w₂ : ∀ x, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₂ x = VG.Proof.TripleDes.AArch64.BitslicedNeon.words s x := fun x => by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, m₂, m₁, g₂, g₁]
  have hin : ∀ i < 6, s₁.v (inReg i) =
      VG.Proof.TripleDes.AArch64.BitslicedNeon.words s (readWord ρ (eBit (inBit j i))) ^^^ VG.Proof.TripleDes.AArch64.BitslicedNeon.maskX ((K.setWidth 48).getLsbD (inBit j i)) := by
    intro i hi
    rw [in₁ i hi, BitVec.getLsbD_setWidth]
    simp [VG.Proof.TripleDes.Bitslice.inBit_lt j hj i hi]
  refine ⟨s₃, ?_, fun x hx => ?_, k₁.congr (kk₃.trans kk₂) (kz₃.trans kz₂), g₃.trans (g₂.trans g₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
    c₃.trans (c₂.trans c₁), ?_⟩
  · rw [sboxStep, VG.Proof.TripleDes.AArch64.BitslicedNeon.inputCode_eq]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some (VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some run₁ run₂) run₃
  · rw [w₃ x hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact w₂ x
    · have hi4 := VG.Proof.TripleDes.AArch64.BitslicedNeon.outIdx_lt ρ j x i hidx
      dsimp only
      rw [w₂ x]
      refine congrArg (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s x ^^^ ·) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      refine congrArg (fun z => (Spec.TripleDes.sBox j z).getLsbD i) ?_
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, VG.Proof.TripleDes.AArch64.BitslicedNeon.getLsbD_maskX _ hp]
  · have e : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₂ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₂, g₁]
    rw [e, m₂, m₁] at f₃
    exact f₃

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : VG.AArch64.StraightV.Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k == some (2 ^ VG.Proof.TripleDes.AArch64.BitslicedNeon.swapSlot k)

theorem swap_check : VG.AArch64.StraightV.check (vars 64) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg VG.Impl.TripleDes.AArch64.BitsliceNeon.swapHalves (VG.Proof.TripleDes.AArch64.BitslicedNeon.varEnv [.v0, .v1]) VG.Proof.TripleDes.AArch64.BitslicedNeon.swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.swapSlot k < 64 := by lit_decide

theorem swap_regs : (swapHalves.all fun i => dstOf i == none && vdstOf i != some keyReg &&
    vdstOf i != some zeroReg) = true := by
  lit_decide

theorem swapHalves_ok {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) :
    ∃ s', runBlock isa VG.Impl.TripleDes.AArch64.BitsliceNeon.swapHalves s = some s' ∧ (∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = swapW (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s) x) ∧
      s'.gpr = s.gpr ∧ s'.v keyReg = s.v keyReg ∧ s'.v zeroReg = s.v zeroReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.c = s.c ∧
      Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.varsRun [.v0, .v1] VG.Proof.TripleDes.AArch64.BitslicedNeon.swap_check h
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have regs := List.all_eq_true.mp VG.Proof.TripleDes.AArch64.BitslicedNeon.swap_regs
  have noV : ∀ r, (r = keyReg ∨ r = zeroReg) →
      ¬ (swapHalves.all fun op => vdstOf op != some r) = false := by
    intro r hr
    simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h'
    have := regs op hop
    rcases hr with rfl | rfl <;> simp [h'] at this
  refine ⟨s', hrun, fun x hx => ?_, funext fun r => p.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
      intro op hop h'
      have := regs op hop
      simp [h'] at this),
    p.other _ (noV _ (Or.inl rfl)), p.other _ (noV _ (Or.inr rfl)), p.rd, p.wr, p.sp, p.carry,
    p.frame⟩
  apply VG.Proof.TripleDes.AArch64.BitslicedNeon.eq_of_vdword; intro q hq
  have hs := p.rel.slot x _ hx (hpost x hx) q hq
  simp only [VarRel] at hs
  have e : vdword (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x) q = vdword (s'.mem.readW (vAddr (s'.gpr stateCfg.base) x) 128) q := by
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg]
  rw [e, hs, xorSet_two_pow _ (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.varN]; have := VG.Proof.TripleDes.AArch64.BitslicedNeon.swapSlot_lt x hx; omega)]
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.varVals, VG.Proof.TripleDes.AArch64.BitslicedNeon.swapSlot_lt x hx, ite_true, VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW]
  unfold swapW VG.Proof.TripleDes.AArch64.BitslicedNeon.swapSlot
  cases partner x <;> rfl

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Round`. -/
section

/-!
# An AdvSIMD round on the machine

`round_ok`: the code of a round reads the round key at the key pointer
`x5`, broadcasts it, steps the pointer by 8 in the pass's direction, and
does to the 64 state words what `roundW` does, with the key's low 48 bits.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes.Bitslice (step steps roundW steps_succ step_congr steps_congr)

/-- The key pointer after a round. -/
def nextKey (d : VG.Spec.TripleDes.Direction) (p : Addr) : Addr := if d = .encrypt then p + 8 else p - 8

theorem keyLoad_ok (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (hkey : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧
      s'.v keyReg = ofVDwords (s.mem.readW (s.gpr .x5) 64) (s.mem.readW (s.gpr .x5) 64) ∧
      s'.gpr .x5 = VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5) ∧
      (∀ r, r ≠ .x9 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ y, y ≠ keyReg → s'.v y = s.v y) := by
  let K := s.mem.readW (s.gpr .x5) 64
  have hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 8 := by
    simpa using hkey
  let s₁ := s.write .x .x9 K
  have e₁ : exec (.ldr .x .x9 .x5 0) s = some s₁ := by
    rw [VG.AArch64.exec_ldr_x ⟨by decide, by decide⟩ hk0]; simp [s₁, K]
  let s₂ := s₁.setV keyReg (ofVDwords (s₁.gpr .x9) (s₁.gpr .x9))
  have e₂ : exec (.vop (.dup .d2 keyReg .x9)) s₁ = some s₂ := rfl
  have x9₁ : s₁.gpr .x9 = K := by simp [s₁, State.write]
  have x5₂ : s₂.gpr .x5 = s.gpr .x5 := by simp [s₂, s₁, State.write, State.setV]
  let s₃ := s₂.write .x .x5 (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5))
  have e₃ : exec (if d = .encrypt then .addImm .x .x5 .x5 8 else .subImm .x .x5 .x5 8) s₂ =
      some s₃ := by
    cases d
    · simp only [ite_true, exec_addImm_x (show 8 < 4096 by decide)]
      simp only [s₃, VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey, ite_true, State.read, BitVec.setWidth_eq, x5₂]; rfl
    · simp only [reduceCtorEq, ite_false, exec_subImm_x (show 8 < 4096 by decide)]
      simp only [s₃, VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey, State.read, BitVec.setWidth_eq, x5₂, reduceCtorEq, ite_false]; rfl
  refine ⟨s₃, ?_, ?_, by simp [s₃, State.write], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
  · rw [keyLoad, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      e₃, runStep_some, runBlock_nil]
  · show s₂.v keyReg = _; rw [v_setV_self, x9₁]
  · simp [s₃, s₂, s₁, State.write, State.setV, h1, h2]
  · show s₂.v y = s.v y; rw [v_setV_of_ne _ _ hy]; rfl

/-! ## The S-boxes -/

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode ρ (n + 1) = VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode ρ n ++ sboxStep ρ n := by
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) {K : BitVec 64} {n : Nat} (hn : n ≤ 8) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s)
    (hk : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode ρ n) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = steps ρ (K.setWidth 48) n (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s) x) ∧
      VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs K s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, hk, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega)
    have h₁ := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h (by rw [g₁]) wr₁
    obtain ⟨s₂, run₂, w₂, k₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.sboxStep_ok ρ (by omega : n < 8) h₁ k₁
    refine ⟨s₂, ?_, fun x hx => ?_, k₂, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
    · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode_succ]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact step_congr ρ _ (by omega) w₁ (w₁ x hx)
    · rw [show VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₁ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₁]] at f₂
      exact f₁.trans f₂

/-! ## A round -/

theorem round_eq (d : VG.Spec.TripleDes.Direction) (ρ : Role) : VG.Impl.TripleDes.AArch64.BitsliceNeon.round d ρ = keyLoad d ++ VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode ρ 8 := rfl

theorem round_ok (d : VG.Spec.TripleDes.Direction) (ρ : Role) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hz : s.v zeroReg = 0)
    (hkey : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8) :
    ∃ s', runBlock isa (VG.Impl.TripleDes.AArch64.BitsliceNeon.round d ρ) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = roundW ρ ((s.mem.readW (s.gpr .x5) 64).setWidth 48) (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s) x) ∧
      s'.gpr .x5 = VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5) ∧ (∀ r, r ≠ .x9 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.v zeroReg = 0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, x5₁, g₁, m₁, rd₁, wr₁, sp₁, v₁⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.keyLoad_ok d hkey
  have h₁ := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h (g₁ _ (by decide) (by decide)) wr₁
  have kr : VG.Proof.TripleDes.AArch64.BitslicedNeon.KeyRegs (s.mem.readW (s.gpr .x5) 64) s₁ := ⟨k₁, by rw [v₁ _ (by decide), hz]⟩
  obtain ⟨s₂, run₂, w₂, k₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.stepsCode_ok ρ (Nat.le_refl 8) h₁ kr
  refine ⟨s₂, ?_, fun x hx => ?_, by rw [g₂, x5₁], fun r h1 h2 => by rw [g₂, g₁ r h1 h2], k₂.zero,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.round_eq]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    have e : ∀ y, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₁ y = VG.Proof.TripleDes.AArch64.BitslicedNeon.words s y := fun y => by
      simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, m₁, g₁ .x4 (by decide) (by decide)]
    exact steps_congr ρ _ (Nat.le_refl 8) (fun y _ => e y) x hx
  · rw [show VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₁ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₁ .x4 (by decide) (by decide)], m₁] at f₂
    exact f₂

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Pass`. -/
section

/-!
# An AdvSIMD DES pass on the machine

A pass with schedule component `c` in direction `d` points `x5` at its
first round key, runs eight pairs of rounds (counted in `x7`), stepping
the pointer by 8 in its direction, and exchanges the halves. `pass_ok`: it
does to the state words what `passW` does with that component of the
schedule at `x0`, which is readable and apart from the state words.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Impl.TripleDes.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW passW roundW_congr pairs_congr swapW_congr)

/-- The schedule at `x0`: readable, and apart from the state words. -/
structure Sched (s : VG.AArch64.State) : Prop where
  read : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8
  sep : (⟨s.gpr .x0, 384⟩ : Region).Disjoint (VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s)

theorem Sched.congr {s s' : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) (h0 : s'.gpr .x0 = s.gpr .x0)
    (h4 : s'.gpr .x4 = s.gpr .x4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s' where
  read i hi := by rw [h0, hrd, hwr]; exact h.read i hi
  sep := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, h0, h4]; exact h.sep

/-- The index in the schedule of round `r`'s key of component `c`, in direction `d`. -/
def keyIdx (c : Nat) (d : VG.Spec.TripleDes.Direction) (r : Nat) : Nat :=
  16 * c + if d = .encrypt then r else 15 - r

/-- The address of round `r`'s key. -/
def keyA (S : Addr) (c : Nat) (d : VG.Spec.TripleDes.Direction) (r : Nat) : Addr :=
  S + BitVec.ofNat 64 (8 * VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx c d r)

theorem keyIdx_lt {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {r : Nat} (hr : r < 16) :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx c d r < 48 := by
  unfold VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx; split <;> omega

theorem keyA_succ (S : Addr) (c : Nat) (d : VG.Spec.TripleDes.Direction) {r : Nat} (hr : r < 15) :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d r) = VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d (r + 1) := by
  cases d
  · simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx, ite_true]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => S + BitVec.ofNat 64 i) (by omega)
  · simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx, reduceCtorEq, ite_false]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_ofNat_sub _ (by omega)]
    exact congrArg (fun i => S + BitVec.ofNat 64 i) (by omega)

theorem Sched.key {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {r : Nat}
    (hr : r < 16) : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA (s.gpr .x0) c d r) 8 :=
  h.read _ (VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx_lt hc d hr)

theorem Sched.keySep {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {r : Nat}
    (hr : r < 16) : (⟨VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA (s.gpr .x0) c d r, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s) :=
  h.sep.sub_left (Offset.sub_base _ (by have := VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx_lt hc d hr; omega))

theorem keyA_roundKey (m : Mem) (S : Addr) {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {r : Nat}
    (hr : r < 16) :
    (m.readW (VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d r) 64).setWidth 48 = roundKey (componentSchedule (VG.Spec.TripleDes.scheduleAt m S) c) d r := by
  simp only [roundKey, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx]
  rw [componentSchedule_readW m S c _ hc (by split <;> omega)]

/-! ## Counting down `x7` -/

theorem sub1_run (s : VG.AArch64.State) :
    ∃ s', runBlock isa [.subImm .x .x7 .x7 1] s = some s' ∧ s'.gpr .x7 = s.gpr .x7 - 1 ∧
      (∀ r, r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.v = s.v := by
  refine ⟨s.write .x .x7 (s.read .x .x7 - BitVec.ofNat _ 1), ?_, ?_, fun r h => ?_, rfl, rfl, rfl,
    rfl, rfl⟩
  · rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  · simp [State.write, State.read]
  · simp [State.write, h]

theorem cnt_sub (m : Nat) (h : 1 ≤ m) : BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  have e : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  rw [e, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h]

/-! ## A pair of rounds -/

theorem roundPair_eq (d : VG.Spec.TripleDes.Direction) :
    roundPair d = VG.Impl.TripleDes.AArch64.BitsliceNeon.round d .ba ++ VG.Impl.TripleDes.AArch64.BitsliceNeon.round d .ab ++ ([.subImm .x .x7 .x7 1] : List Instr) := rfl

theorem roundPair_ok (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hz : s.v zeroReg = 0)
    (h₁ : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8)
    (h₂ : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5)) 8)
    (sep₂ : (⟨VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5), 8⟩ : Region).Disjoint (VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s)) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = roundW .ab ((s.mem.readW (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5)) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (s.gpr .x5) 64).setWidth 48) (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s)) x) ∧
      s'.gpr .x5 = VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5)) ∧ s'.gpr .x7 = s.gpr .x7 - 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧ s'.v zeroReg = 0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, k₁, g₁, z₁, rd₁, wr₁, sp₁, f₁⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.round_ok d .ba h hz h₁
  have x4₁ := g₁ .x4 (by decide) (by decide)
  have h₁' := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h x4₁ wr₁
  obtain ⟨s₂, run₂, w₂, k₂, g₂, z₂, rd₂, wr₂, sp₂, f₂⟩ :=
    VG.Proof.TripleDes.AArch64.BitslicedNeon.round_ok d .ab h₁' z₁ (by rw [k₁, rd₁, wr₁]; exact h₂)
  obtain ⟨s₃, run₃, c₃, g₃, m₃, rd₃, wr₃, sp₃, v₃⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.sub1_run s₂
  have st₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₁ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, x4₁]
  have kread : s₁.mem.readW (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5)) 64 = s.mem.readW (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5)) 64 :=
    f₁.readW (Region.contains_self _ _) (by simpa using sep₂) (by decide)
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, fun r a b c => ?_, by rw [v₃, z₂], rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.roundPair_eq]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some (VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some run₁ run₂) run₃
  · have e : VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₃ x = VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₂ x := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, m₃, g₃ .x4 (by decide)]
    rw [e, w₂ x hx, k₁, kread]
    exact roundW_congr .ab _ w₁ x hx
  · rw [g₃ _ (by decide), k₂, k₁]
  · rw [c₃, g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide)]
  · rw [g₃ r c, g₂ r a b, g₁ r a b]
  · rw [st₁] at f₂
    rw [m₃]
    exact f₁.trans f₂

/-! ## The loop of pairs of rounds -/

/-- The keys of the pass. -/
abbrev passKeys (s₀ : VG.AArch64.State) (c : Nat) (d : VG.Spec.TripleDes.Direction) : Nat → BitVec 48 :=
  roundKey (componentSchedule (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) c) d

structure LoopInv (c : Nat) (d : VG.Spec.TripleDes.Direction) (s₀ : VG.AArch64.State) (m : Nat) (s : VG.AArch64.State) : Prop where
  room : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s
  zero : s.v zeroReg = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s x = pairs (VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys s₀ c d) (8 - m) (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₀) x
  key : s.gpr .x5 = VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA (s₀.gpr .x0) c d (2 * (8 - m))
  cnt : s.gpr .x7 = BitVec.ofNat 64 m
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₀] s₀.mem s.mem

structure LoopPost (c : Nat) (d : VG.Spec.TripleDes.Direction) (s₀ s : VG.AArch64.State) : Prop where
  room : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s
  zero : s.v zeroReg = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  words : ∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s x = pairs (VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys s₀ c d) 8 (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₀) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₀] s₀.mem s.mem

theorem pairLoop_ok {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {s₀ : VG.AArch64.State} (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s₀)
    (m₀ : Nat) (s₁ : VG.AArch64.State) (hs₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.LoopInv c d s₀ m₀ s₁) :
    WP isa (.loop (.block (roundPair d)) (.nonzero .x .x7)) s₁ (VG.Proof.TripleDes.AArch64.BitslicedNeon.LoopPost c d s₀) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.AArch64.BitslicedNeon.LoopInv c d s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let S := s₀.gpr .x0
  have h4 : s.gpr .x4 = s₀.gpr .x4 := hs.gpr _ (by decide) (by decide) (by decide)
  have st : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₀ := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, h4]
  have r₀ : 2 * (8 - m) < 16 := by omega_using [hs.pos]
  have r₁ : 2 * (8 - m) + 1 < 16 := by omega_using [hs.pos]
  have a₁ : InRegions (s.rd ++ s.wr) (s.gpr .x5) 8 := by
    rw [hs.key, hs.rd, hs.wr]; exact hS.key hc d r₀
  have nk : VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5) = VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d (2 * (8 - m) + 1) := by
    rw [hs.key]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA_succ S c d (by omega)
  have a₂ : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5)) 8 := by
    rw [nk, hs.rd, hs.wr]; exact hS.key hc d r₁
  have sep₂ : (⟨VG.Proof.TripleDes.AArch64.BitslicedNeon.nextKey d (s.gpr .x5), 8⟩ : Region).Disjoint (VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s) := by
    rw [nk, st]; exact hS.keySep hc d r₁
  obtain ⟨s', run', w', key', cnt', g', z', rd', wr', sp', f'⟩ :=
    VG.Proof.TripleDes.AArch64.BitslicedNeon.roundPair_ok d hs.room hs.zero a₁ a₂ sep₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  have frame' : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₀] s₀.mem s'.mem := by
    rw [st] at f'; exact hs.frame.trans f'
  have rk : ∀ r < 16, (s.mem.readW (VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d r) 64).setWidth 48 = VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys s₀ c d r := by
    intro r hr
    have e := hs.frame.readW (a := VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d r) (w := 64) (r := ⟨VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA S c d r, 8⟩)
      (Region.contains_self _ _) (by simpa using hS.keySep hc d hr) (by decide)
    rw [e]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA_roundKey _ _ hc d hr
  have words' : ∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = pairs (VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys s₀ c d) (8 - m + 1) (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₀) x := by
    intro x hx
    rw [w' x hx, nk, hs.key, rk _ r₀, rk _ r₁]
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ hs.words) x hx
  have gpr' : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s₀.gpr r :=
    fun r a b c => (g' r a b c).trans (hs.gpr r a b c)
  have room' := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr hs.room (g' _ (by decide) (by decide) (by decide)) wr'
  have cntv : s'.gpr .x7 = BitVec.ofNat 64 (m - 1) := by rw [cnt', hs.cnt]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.cnt_sub m hs.pos
  have hm8 := hs.le
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', z', rd'.trans hs.rd, wr'.trans hs.wr, sp'.trans hs.sp, words', gpr', frame'⟩⟩
    show some (s'.read .x .x7 != 0) = some false
    simp [State.read, cntv]
  · right
    refine ⟨?_, m - 1, by omega, ⟨room', z', rd'.trans hs.rd, wr'.trans hs.wr, sp'.trans hs.sp,
      by omega, by omega, ?_, ?_, cntv, gpr', frame'⟩⟩
    · show some (s'.read .x .x7 != 0) = some true
      have hne : BitVec.ofNat 64 (m - 1) ≠ 0 := by
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this
        omega
      simp [State.read, cntv]
      exact hne
    · rw [show 8 - (m - 1) = 8 - m + 1 by omega]; exact words'
    · rw [key', nk, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA_succ S c d (by omega)]
      congr 1; omega

/-! ## A pass -/

theorem passOff (c : Nat) (hc : c < 3) (d : VG.Spec.TripleDes.Direction) :
    (128 * c + if d = .encrypt then 0 else 120) < 4096 ∧
      BitVec.ofNat 64 (128 * c + if d = .encrypt then 0 else 120) =
        BitVec.ofNat 64 (8 * VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx c d 0) := by
  constructor
  · split <;> omega
  · simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.keyIdx]; split <;> (congr 1; omega)

structure PassPost (c : Nat) (d : VG.Spec.TripleDes.Direction) (s s' : VG.AArch64.State) : Prop where
  room : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s'
  zero : s'.v zeroReg = 0
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  words : ∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = passW (componentSchedule (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) c) d
    (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r
  frame : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem

theorem pass_ok {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s)
    (hz : s.v zeroReg = 0) (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) : WP isa (VG.Impl.TripleDes.AArch64.BitsliceNeon.pass c d) s (VG.Proof.TripleDes.AArch64.BitslicedNeon.PassPost c d s) := by
  obtain ⟨hoff, heq⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.passOff c hc d
  let s₁ := s.write .x .x5 (s.read .x .x0 + BitVec.ofNat _ (128 * c + if d = .encrypt then 0 else 120))
  let s₂ := s₁.write .x .x7 ((8 : BitVec 16).setWidth 64 <<< (16 * 0))
  have run₁ : runBlock isa [.addImm .x .x5 .x0 (128 * c + if d = .encrypt then 0 else 120),
      .movz .x .x7 8 0] s = some s₂ := by
    rw [runBlock_cons, exec_addImm_x hoff, runStep_some, runBlock_cons]
    simp only [exec, Size.bits, show 16 * 0 < 64 by decide, ite_true, runStep_some, runBlock_nil]
    rfl
  have g₂ : ∀ r, r ≠ .x5 → r ≠ .x7 → s₂.gpr r = s.gpr r := by
    intro r a b; simp [s₂, s₁, State.write, a, b]
  have x5₂ : s₂.gpr .x5 = VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA (s.gpr .x0) c d 0 := by
    simp [s₂, s₁, State.write, State.read, VG.Proof.TripleDes.AArch64.BitslicedNeon.keyA, heq]
  have x7₂ : s₂.gpr .x7 = BitVec.ofNat 64 8 := by simp [s₂, State.write]
  have h₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s₂ := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h (g₂ _ (by decide) (by decide)) rfl
  have S₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s₂ := hS.congr (g₂ _ (by decide) (by decide)) (g₂ _ (by decide) (by decide)) rfl rfl
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, run₁, ?_⟩
  apply WP.seq
  have inv : VG.Proof.TripleDes.AArch64.BitslicedNeon.LoopInv c d s₂ 8 s₂ := ⟨h₂, hz, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl,
    by simpa using x5₂.trans (by rw [g₂ _ (by decide) (by decide)]), x7₂,
    fun _ _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.pairLoop_ok hc d S₂ 8 s₂ inv)
  intro s₃ p₃
  obtain ⟨s₄, run₄, w₄, g₄, -, z₄, rd₄, wr₄, sp₄, -, f₄⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.swapHalves_ok p₃.room
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s₃.gpr r = s.gpr r :=
    fun r a b c => (p₃.gpr r a b c).trans (g₂ r b c)
  have st₃ : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₃ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₃ .x4 (by decide) (by decide) (by decide)]
  have st₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₂ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₂ .x4 (by decide) (by decide)]
  refine ⟨VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr p₃.room (by rw [g₄]) wr₄, by rw [z₄, p₃.zero], rd₄.trans p₃.rd,
    wr₄.trans p₃.wr, sp₄.trans p₃.sp, fun x hx => ?_, fun r a b c => by rw [g₄, g₃ r a b c], ?_⟩
  · rw [w₄ x hx]
    have hx0 : s₂.gpr .x0 = s.gpr .x0 := g₂ _ (by decide) (by decide)
    have hk : VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys s₂ c d = VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys s c d := by
      rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys, VG.Proof.TripleDes.AArch64.BitslicedNeon.passKeys, hx0]; rfl
    refine swapW_congr (fun y hy => ?_) x hx
    rw [p₃.words y hy, hk]
    exact pairs_congr _ 8 (fun z _ => by
      simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.words, g₂ .x4 (by decide) (by decide)]; rfl) y hy
  · rw [st₃] at f₄
    have f₃ := p₃.frame
    rw [st₂] at f₃
    exact f₃.trans f₄

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Transpose`. -/
section

/-!
# The transposition of the AdvSIMD state, by evaluation

The 64 state words are the 16-byte slots at `x4`. The transposition only
moves and XORs bits within the doubleword lanes of the words, and masks
them with constants: the lane domain evaluates it on words of atoms (bit
`t` of word `i` is atom `64 i + t`) once, and the check that bit `p` of
word `j` is then atom `64 p + j` proves, through the doubleword-lane
evaluator, that it transposes the 64 doublewords of every lane
(`transpose_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.Bitslice VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes.Bitslice (transposeW)

def transEnv : VG.AArch64.StraightV.Env (Nat × Nat) :=
  { reg := fun _ => none, slot := fun k => if k < 64 then some (inWord k) else none }

def transPost (e : VG.AArch64.StraightV.Env (Nat × Nat)) : Bool :=
  (List.range 64).all fun j => e.slot j == some (outWord (fun p => [64 * p + j]))

theorem transpose_check :
    VG.AArch64.StraightV.check (lanes 64 12) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg (instrs transposeProg.lit) VG.Proof.TripleDes.AArch64.BitslicedNeon.transEnv VG.Proof.TripleDes.AArch64.BitslicedNeon.transPost = true := by
  decide +kernel

theorem transpose_code : instrs transposeProg.lit = transpose := by
  rw [← transposeProg.lit_eq]; rfl

theorem transpose_nogpr :
    (instrs transposeProg.lit).all (fun op => dstOf op == none || dstOf op == some .x10) = true := by
  decide +kernel

/-- Each doubleword lane of the state words, transposed. Only `x10` (the
masks' constants) and vector registers change, and in memory only the
state words. -/
theorem transpose_ok {s : VG.AArch64.State} (hok : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) :
    ∃ s', runBlock isa transpose s = some s' ∧
      (∀ q < 2, ∀ j < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s' q j = transposeW (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s q) j) ∧
      (∀ r, r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.c = s.c ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := VG.AArch64.StraightV.of_check _ _ VG.Proof.TripleDes.AArch64.BitslicedNeon.transpose_check
  rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.transpose_code] at he
  have hrel : VG.AArch64.StraightV.Rel (fun q => LaneRel 12 (assign (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s q) (2 ^ 12))) VG.Proof.TripleDes.AArch64.BitslicedNeon.stateCfg VG.Proof.TripleDes.AArch64.BitslicedNeon.transEnv s := by
    refine ⟨(fun r a h => by cases h), (fun j a hj hsl q hq => ?_), (fun _ _ h => by cases h)⟩
    simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.transEnv] at hsl
    split at hsl
    · rename_i hk
      simp only [Option.some.injEq] at hsl
      subst hsl
      exact inWord_rel (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s q) (by omega)
    · cases hsl
  obtain ⟨s', hs', p⟩ := VG.AArch64.StraightV.run (fun _ _ => lanes_sound) hok hrel he
  have nog := List.all_eq_true.mp VG.Proof.TripleDes.AArch64.BitslicedNeon.transpose_nogpr
  rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.transpose_code] at nog
  refine ⟨s', hs', fun q hq j hj => ?_, fun r hr => p.gpr r ?_, p.carry, p.sp, p.rd, p.wr, p.frame⟩
  · have hpj := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    have hs := p.rel.slot j _ (by show j < 64; omega) (beq_iff_eq.mp hpj) q hq
    have bits := outWord_rel (fun q hq a ha => by simp at ha; omega) hs
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hsj : VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s' q j = vdword (s'.mem.readW (vAddr (s'.gpr stateCfg.base) j) 128) q := rfl
    rw [hsj, bits b hb]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, transposeW, getLsbD_ofBits, hb,
      decide_true, Bool.true_and]
    exact VG.Bitslice.bitOf_word (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s q) b j hj
  · simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h
    have := nog op hop
    simp [h, hr] at this

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Bytes`. -/
section

/-!
# Blocks as little-endian words

A block's little-endian word holds bit `i` of the block (big-endian, as
`decodeBlock` reads it) at bit `i ^^^ 56`: the byte order is reversed.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

theorem xor56_lt {p : Nat} (hp : p < 64) : p ^^^ 56 < 64 := Nat.xor_lt_two_pow (n := 6) hp (by decide)

theorem xor56_xor56 (a : Nat) : a ^^^ 56 ^^^ 56 = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem getLsbD_rev64' (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (rev64 x).getLsbD p = x.getLsbD (p ^^^ 56) := by
  rw [getLsbD_rev64 _ hp, xor56_eq p hp]

/-- The little-endian word of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [VG.Proof.TripleDes.AArch64.decodeBlock_readW, VG.Proof.TripleDes.AArch64.BitslicedNeon.getLsbD_rev64' _ (VG.Proof.TripleDes.AArch64.BitslicedNeon.xor56_lt hj), VG.Proof.TripleDes.AArch64.BitslicedNeon.xor56_xor56]

/-- A word whose bits are those of `x` at `j ^^^ 56` is the little-endian word of
the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    VG.Spec.TripleDes.blockAt m p = VG.Spec.TripleDes.encodeBlock x := by
  have hw : m.readW p 64 = rev64 x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [h j hj, VG.Proof.TripleDes.AArch64.BitslicedNeon.getLsbD_rev64' _ hj]
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, VG.Spec.TripleDes.encodeBlock, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m p (n := 8) hi]
  have e : (m.read p 8) = m.readW p 64 := by simp only [Mem.readW]; rfl
  rw [e, hw]
  exact VG.Proof.TripleDes.AArch64.rev64_byte x i hi

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Batch`. -/
section

/-!
# An AdvSIMD batch

A batch of 128 blocks, in place: each doubleword lane `q` of the 64 state
words (the 1024 bytes at `x4`) is transposed, so that lane `64 q + i` of
the words is IP of block `2 i + q`; the three passes run; the lanes are
transposed back, and each block becomes its TDEA encryption or decryption
(`batch_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW ipLane_bit passW passW_congr tdeaW tdeaW_lane
  blockOut blockOut_cores ipLane_congr wAt)

/-! ## Doubleword lanes as blocks -/

/-- Doubleword `q` of state word `i` is block `2 i + q`. -/
theorem laneW_eq (s : VG.AArch64.State) {q i : Nat} (hq : q < 2) :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s q i = s.mem.readW (wAt (s.gpr .x4) (2 * i + q)) 64 := by
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW, VG.Proof.TripleDes.AArch64.BitslicedNeon.words, vAddr]
  rw [← read16_readW, vdword_read16 _ _ hq, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show 16 * i + 8 * q = 8 * (2 * i + q) by omega]

/-- Lane `64 q + i` of 128-bit words is lane `i` of their doublewords `q`. -/
theorem ipLane_dw {W : Nat → BitVec 128} {q i : Nat} (hi : i < 64) :
    ipLane W (64 * q + i) = ipLane (fun j => vdword (W j) q) i := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, getLsbD_vdword _ hi]

/-! ## The passes -/

/-- What the passes leave. -/
structure PassesPost (d : VG.Spec.TripleDes.Direction) (s s' : VG.AArch64.State) : Prop where
  room : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  words : ∀ x < 64, VG.Proof.TripleDes.AArch64.BitslicedNeon.words s' x = tdeaW (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r
  frame : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem

/-- A pass, followed by what is left of the passes, `Q`, of its result. -/
theorem pass_then {c : Nat} (hc : c < 3) (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s)
    (hz : s.v zeroReg = 0) (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) {p : Prog isa} {Q : VG.AArch64.State → Prop}
    (k : ∀ s', VG.Proof.TripleDes.AArch64.BitslicedNeon.PassPost c d s s' → WP isa p s' Q) : WP isa (.seq (VG.Impl.TripleDes.AArch64.BitsliceNeon.pass c d) p) s Q :=
  WP.seq (WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_ok hc d h hz hS) k)

theorem PassPost.sched {c : Nat} {d : VG.Spec.TripleDes.Direction} {s s' : VG.AArch64.State} (p : VG.Proof.TripleDes.AArch64.BitslicedNeon.PassPost c d s s')
    (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s' :=
  hS.congr (p.gpr _ (by decide) (by decide) (by decide)) (p.gpr _ (by decide) (by decide) (by decide))
    p.rd p.wr

theorem PassPost.schedule {c : Nat} {d : VG.Spec.TripleDes.Direction} {s s' : VG.AArch64.State} (p : VG.Proof.TripleDes.AArch64.BitslicedNeon.PassPost c d s s')
    (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) : VG.Spec.TripleDes.scheduleAt s'.mem (s'.gpr .x0) = VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .x0) := by
  rw [p.gpr _ (by decide) (by decide) (by decide)]
  exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ p.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hS.sep

theorem PassPost.state {c : Nat} {d : VG.Spec.TripleDes.Direction} {s s' : VG.AArch64.State} (p : VG.Proof.TripleDes.AArch64.BitslicedNeon.PassPost c d s s') :
    VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s' = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s := by
  simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, p.gpr .x4 (by decide) (by decide) (by decide)]

theorem passes_ok (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hz : s.v zeroReg = 0)
    (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) : WP isa (passes d) s (VG.Proof.TripleDes.AArch64.BitslicedNeon.PassesPost d s) := by
  cases d with
  | encrypt =>
    refine VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_then (by decide) .encrypt h hz hS fun s₁ p₁ => ?_
    refine VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_then (by decide) .decrypt p₁.room p₁.zero (p₁.sched hS) fun s₂ p₂ => ?_
    apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_ok (by decide) .encrypt p₂.room p₂.zero (p₂.sched (p₁.sched hS)))
    intro s₃ p₃
    have K₁ := p₁.schedule hS
    have K₂ := p₂.schedule (p₁.sched hS)
    refine ⟨p₃.room, p₃.rd.trans (p₂.rd.trans p₁.rd), p₃.wr.trans (p₂.wr.trans p₁.wr),
      p₃.sp.trans (p₂.sp.trans p₁.sp), fun x hx => ?_,
      fun r a b c => (p₃.gpr r a b c).trans ((p₂.gpr r a b c).trans (p₁.gpr r a b c)), ?_⟩
    · rw [p₃.words x hx, K₂, K₁]
      exact passW_congr _ _ (fun y hy => by
        rw [p₂.words y hy, K₁]; exact passW_congr _ _ p₁.words y hy) x hx
    · have f₂ := p₂.frame
      rw [p₁.state] at f₂
      have f₃ := p₃.frame
      rw [p₂.state, p₁.state] at f₃
      exact p₁.frame.trans (f₂.trans f₃)
  | decrypt =>
    refine VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_then (by decide) .decrypt h hz hS fun s₁ p₁ => ?_
    refine VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_then (by decide) .encrypt p₁.room p₁.zero (p₁.sched hS) fun s₂ p₂ => ?_
    apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.pass_ok (by decide) .decrypt p₂.room p₂.zero (p₂.sched (p₁.sched hS)))
    intro s₃ p₃
    have K₁ := p₁.schedule hS
    have K₂ := p₂.schedule (p₁.sched hS)
    refine ⟨p₃.room, p₃.rd.trans (p₂.rd.trans p₁.rd), p₃.wr.trans (p₂.wr.trans p₁.wr),
      p₃.sp.trans (p₂.sp.trans p₁.sp), fun x hx => ?_,
      fun r a b c => (p₃.gpr r a b c).trans ((p₂.gpr r a b c).trans (p₁.gpr r a b c)), ?_⟩
    · rw [p₃.words x hx, K₂, K₁]
      exact passW_congr _ _ (fun y hy => by
        rw [p₂.words y hy, K₁]; exact passW_congr _ _ p₁.words y hy) x hx
    · have f₂ := p₂.frame
      rw [p₁.state] at f₂
      have f₃ := p₃.frame
      rw [p₂.state, p₁.state] at f₃
      exact p₁.frame.trans (f₂.trans f₃)

/-! ## The batch -/

structure BatchPost (d : VG.Spec.TripleDes.Direction) (s s' : VG.AArch64.State) : Prop where
  out : ∀ b < 128, VG.Spec.TripleDes.blockAt s'.mem (wAt (s.gpr .x4) b) =
    blockOut (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (VG.Spec.TripleDes.blockAt s.mem (wAt (s.gpr .x4) b))
  gpr : ∀ r, r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s'.mem

theorem batch_ok (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (h : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s) (hS : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s) :
    WP isa (batch d) s (VG.Proof.TripleDes.AArch64.BitslicedNeon.BatchPost d s) := by
  let S := s.gpr .x0
  let D := s.gpr .x4
  rw [batch]
  apply WP.seq
  -- the transposition, and zero
  obtain ⟨s₁, run₁, w₁, g₁, -, sp₁, rd₁, wr₁, f₁⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.transpose_ok h
  let s₂ := s₁.setV zeroReg 0
  refine WP.of_runBlock ⟨s₂, VG.Proof.TripleDes.AArch64.BitslicedNeon.runBlock_cat_some run₁ (by
    rw [runBlock_cons]; exact (by rfl : runStep isa (some s₂) [] = some s₂)), ?_⟩
  have g₂ : ∀ r, r ≠ .x10 → s₂.gpr r = s.gpr r := g₁
  have h₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s₂ := VG.Proof.TripleDes.AArch64.BitslicedNeon.room_congr h (g₂ _ (by decide)) wr₁
  have S₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s₂ := hS.congr (g₂ _ (by decide)) (g₂ _ (by decide)) rd₁ wr₁
  have st₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₂ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₂ .x4 (by decide)]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.passes_ok d h₂ (v_setV_self _ _ _) S₂)
  intro s₃ q₃
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → r ≠ .x10 → s₃.gpr r = s.gpr r :=
    fun r a b c e => (q₃.gpr r a b c).trans (g₂ r e)
  -- the transposition back
  obtain ⟨s₄, run₄, w₄, g₄, -, sp₄, rd₄, wr₄, f₄⟩ := VG.Proof.TripleDes.AArch64.BitslicedNeon.transpose_ok q₃.room
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have si₄ : s₄.gpr .x4 = D :=
    (g₄ .x4 (by decide)).trans (g₃ _ (by decide) (by decide) (by decide) (by decide))
  have K₂ : VG.Spec.TripleDes.scheduleAt s₂.mem (s₂.gpr .x0) = VG.Spec.TripleDes.scheduleAt s.mem S := by
    rw [g₂ _ (by decide)]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS.sep
  refine ⟨fun b hb => ?_, fun r a c e f => by rw [g₄ r f, g₃ r e a c f], rd₄.trans (q₃.rd.trans rd₁),
    wr₄.trans (q₃.wr.trans wr₁), sp₄.trans (q₃.sp.trans sp₁), ?_⟩
  · have hq : b % 2 < 2 := Nat.mod_lt _ (by decide)
    have hi : b / 2 < 64 := by omega
    have eb : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
    -- lane 64 q + i before the passes: IP of the block
    have lane₂ : ipLane (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₂) (64 * (b % 2) + b / 2) =
        permute ip (VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt s.mem (wAt D b))) := by
      rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.ipLane_dw hi]
      have e : ∀ j < 64, vdword (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₂ j) (b % 2) = transposeW (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s (b % 2)) j := by
        intro j hj; exact w₁ _ hq j hj
      rw [ipLane_congr e]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hi fun j hj => ?_
      rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW_eq s hq, eb]
      exact VG.Proof.TripleDes.AArch64.BitslicedNeon.readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    have word₄ : s₄.mem.readW (wAt D b) 64 = transposeW (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s₃ (b % 2)) (b / 2) := by
      rw [← w₄ _ hq _ hi, VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW_eq s₄ hq, si₄, eb]
    rw [blockOut_cores, ← K₂]
    apply VG.Proof.TripleDes.AArch64.BitslicedNeon.blockAt_of_readW
    intro j hj
    rw [word₄, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj]
    have e₃ : ipLane (VG.Proof.TripleDes.AArch64.BitslicedNeon.laneW s₃ (b % 2)) (b / 2) = ipLane (VG.Proof.TripleDes.AArch64.BitslicedNeon.words s₃) (64 * (b % 2) + b / 2) :=
      (VG.Proof.TripleDes.AArch64.BitslicedNeon.ipLane_dw hi).symm
    rw [e₃, ipLane_congr q₃.words, tdeaW_lane _ d _ (by omega), lane₂]
  · have a : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s.mem s₂.mem := f₁
    have b : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s₂.mem s₃.mem := by rw [← st₂]; exact q₃.frame
    have c : Frame [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s] s₃.mem s₄.mem := by
      rw [show VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₃ = VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s by
        simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, g₃ .x4 (by decide) (by decide) (by decide) (by decide)]] at f₄
      exact f₄
    exact (a.trans b).trans c

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit`. -/
section

namespace VG

materialize_code Impl.TripleDes.AArch64.BitsliceNeon.encrypt
materialize_code Impl.TripleDes.AArch64.BitsliceNeon.decrypt

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.ConstantTime`. -/
section

/-!
# Constant time

The pointers and the count of blocks are public, and so is everything the
function computes from them (the batches, the counts of passes and rounds,
the addresses of the round keys): every address and branch.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64 (PublicRegs)

theorem encrypt_constantTime (pre : VG.AArch64.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3]) Impl.TripleDes.AArch64.BitsliceNeon.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decrypt_constantTime (pre : VG.AArch64.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3]) Impl.TripleDes.AArch64.BitsliceNeon.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Copy`. -/
section

/-!
# Copying words

`copy_ok`: the loop `copy` copies `n ≥ 1` words from `A` (in `x11`) to `B`
(in `x12`), where the two areas do not overlap, and changes nothing else in
memory. `x13` counts the words left, and `x10` holds each word.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes.Bitslice (wAt)

structure CopyPre (A B : Addr) (n : Nat) (s : VG.AArch64.State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (wAt A i) 8
  write : ∀ i < n, InRegions s.wr (wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : wAt p i + BitVec.ofNat 64 8 = wAt p (i + 1) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2

/-- The registers the copy changes. -/
def CopyRegs (r : Reg) : Prop := r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure CopyInv (A B : Addr) (n : Nat) (s₀ : VG.AArch64.State) (i : Nat) (s : VG.AArch64.State) : Prop where
  le : i < n
  src : s.gpr .x11 = wAt A i
  dst : s.gpr .x12 = wAt B i
  cnt : s.gpr .x13 = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

structure CopyPost (A B : Addr) (n : Nat) (s₀ s : VG.AArch64.State) : Prop where
  copied : ∀ j < n, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (wAt p i) 8 :=
  Offset.contains_base p (by omega) (by omega)

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := by simp

theorem copy_ok {A B : Addr} {n : Nat} {s₀ : VG.AArch64.State} (hpre : VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyPre A B n s₀) (s : VG.AArch64.State) (i : Nat)
    (hs : VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyInv A B n s₀ i s) : WP isa copy s (VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyPost A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyInv A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega]; exact hs, by omega⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  let v := s₀.mem.readW (wAt A j) 64
  have hv : s.mem.readW (wAt A j) 64 = v :=
    inv.frame.readW (VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x11 + BitVec.ofNat 64 0) 8 := by
    rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.add_ofNat_zero, inv.src, inv.rd, inv.wr]; exact hpre.read j hj
  let s₁ := s.write .x .x10 v
  have e₁ : exec (.ldr .x .x10 .x11 0) s = some s₁ := by
    rw [VG.AArch64.exec_ldr_x ⟨by decide, by decide⟩ hr, VG.Proof.TripleDes.AArch64.BitslicedNeon.add_ofNat_zero, inv.src, hv]
  have hw : InRegions s₁.wr (s₁.gpr .x12 + BitVec.ofNat 64 0) 8 := by
    rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.add_ofNat_zero]
    have : (s.write .x .x10 v).gpr .x12 = s.gpr .x12 := by simp [State.write]
    show InRegions s.wr ((s.write .x .x10 v).gpr .x12) 8
    rw [this, inv.dst, inv.wr]; exact hpre.write j hj
  let s₂ : VG.AArch64.State := { s₁ with
                              mem := s₁.mem.writeW (wAt B j) v }
  have e₂ : exec (.str .x .x10 .x12 0) s₁ = some s₂ := by
    rw [VG.AArch64.exec_str_x ⟨by decide, by decide⟩ hw, VG.Proof.TripleDes.AArch64.BitslicedNeon.add_ofNat_zero]
    have h12 : s₁.gpr .x12 = wAt B j := by
      show (s.write .x .x10 v).gpr .x12 = _; simp [State.write, inv.dst]; rfl
    have h10 : s₁.gpr .x10 = v := by show (s.write .x .x10 v).gpr .x10 = _; simp [State.write]
    rw [h12, h10]
  let s₃ := s₂.write .x .x11 (s₂.read .x .x11 + BitVec.ofNat _ 8)
  let s₄ := s₃.write .x .x12 (s₃.read .x .x12 + BitVec.ofNat _ 8)
  let s₅ := s₄.write .x .x13 (s₄.read .x .x13 - BitVec.ofNat _ 1)
  have run : runBlock isa [.ldr .x .x10 .x11 0, .str .x .x10 .x12 0, .addImm .x .x11 .x11 8,
      .addImm .x .x12 .x12 8, .subImm .x .x13 .x13 1] s = some s₅ := by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  have g₅ : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyRegs r → s₅.gpr r = s.gpr r := by
    intro r ⟨h1, h2, h3, h4⟩
    simp [s₅, s₄, s₃, s₂, s₁, State.write, h1, h2, h3, h4]
  have src₅ : s₅.gpr .x11 = wAt A (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.src]
    exact VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_succ A j
  have dst₅ : s₅.gpr .x12 = wAt B (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.dst]
    exact VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_succ B j
  have cnt₅ : s₅.gpr .x13 = s.gpr .x13 - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read]
  have mem₅ : s₅.mem = s.mem.writeW (wAt B j) v := rfl
  have copied₅ : ∀ x < j + 1, s₅.mem.readW (wAt B x) 64 = s₀.mem.readW (wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)]
      exact inv.copied x (by omega)
  have frame₅ : Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_in hj hpre.fitA)
  have regs₅ : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyRegs r → s₅.gpr r = s₀.gpr r := fun r hr => (g₅ r hr).trans (inv.regs r hr)
  have cntv : s₅.gpr .x13 = BitVec.ofNat 64 (m - 1) := by
    rw [cnt₅, inv.cnt, show n - j = m by omega]
    exact VG.Proof.TripleDes.AArch64.BitslicedNeon.cnt_sub m (by omega)
  have flag : isa.eval (.nonzero .x .x13) s₅ = some (m - 1 != 0) := by
    show some (s₅.read .x .x13 != 0) = _
    have hlt : m - 1 < 2 ^ 64 := by have := hpre.fitA; omega
    simp only [State.read, BitVec.setWidth_eq, cntv]
    congr 1
    by_cases h0 : m - 1 = 0
    · simp [h0]
    · have hne : BitVec.ofNat 64 (m - 1) ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this; simp at this; omega
      change (BitVec.ofNat 64 (m - 1) != (0 : BitVec 64)) = (m - 1 != 0)
      simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]
  by_cases h1 : m = 1
  · left
    refine ⟨by rw [flag, h1]; rfl, ?_⟩
    exact ⟨fun x hx => copied₅ x (by omega), frame₅, regs₅, inv.rd, inv.wr, inv.sp, inv.v⟩
  · right
    refine ⟨by rw [flag]; simp; omega, m - 1, by omega, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, inv.rd,
      inv.wr, inv.sp, inv.v⟩, by omega⟩
    · omega
    · rw [src₅]; congr 2; omega
    · rw [dst₅]; congr 2; omega
    · rw [cntv]; congr 1; omega
    · intro x hx; exact copied₅ x (by omega)

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Ecb`. -/
section

/-!
# The function

While at least 128 blocks are left, a batch runs on the next 128 in place
(`wide_ok`); the `n mod 128` blocks left, if any, are copied into the
scratch buffer, run as a batch there, and copied back (`tail_ok`). Every
block becomes its encryption or decryption (`ecb_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le ecb_blocks)

/-- What the function may assume of the state it starts in: the schedule
readable, the `n` blocks of data and the scratch buffer writable, apart from
each other. -/
structure Env (s : VG.AArch64.State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 384⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 1024⟩]
  keyData : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega

theorem Env.len {s : VG.AArch64.State} (E : VG.Proof.TripleDes.AArch64.BitslicedNeon.Env s) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  VG.Proof.TripleDes.AArch64.BitslicedNeon.len_lt_of_disjoint E.dataBuf (by simp)

theorem Env.keyIn {s : VG.AArch64.State} (E : VG.Proof.TripleDes.AArch64.BitslicedNeon.Env s) :
    ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [E.rd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    VG.Spec.TripleDes.blockAt m' p' = VG.Spec.TripleDes.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m' p' (n := 8) hi, ← Mem.extractLsb'_read m p (n := 8) hi]
  have e : ∀ (m : Mem) (p : Addr), m.read p 8 = m.readW p 64 := fun m p => by
    simp only [Mem.readW]; rfl
  rw [e, e, h]

/-! ## The batches of 128 blocks -/

/-- The registers the batches change. -/
def WideRegs (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10

/-- `m` blocks left, a multiple of 128 fewer than `n`, and at least 128. -/
structure WideInv (d : VG.Spec.TripleDes.Direction) (s₀ : VG.AArch64.State) (n m : Nat) (s : VG.AArch64.State) : Prop where
  ge : 128 ≤ m
  le : m ≤ n
  mod : m % 128 = n % 128
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  done : ∀ b < n - m, VG.Spec.TripleDes.blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) d (VG.Spec.TripleDes.blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩] s₀.mem s.mem

structure WidePost (d : VG.Spec.TripleDes.Direction) (s₀ : VG.AArch64.State) (n : Nat) (s : VG.AArch64.State) : Prop where
  x2 : s.gpr .x2 = BitVec.ofNat 64 (n % 128)
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - n % 128)
  gpr : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  done : ∀ b < n - n % 128, VG.Spec.TripleDes.blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) d (VG.Spec.TripleDes.blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - n % 128)⟩] s₀.mem s.mem

theorem lsr7 (m : Nat) (hm : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> 7 = BitVec.ofNat 64 (m / 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ofNat_ne_zero {m : Nat} (h : m < 2 ^ 64) (h0 : m ≠ 0) : BitVec.ofNat 64 m ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  simp at this
  omega

theorem eval_nonzero (s : VG.AArch64.State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr (VG.Proof.TripleDes.AArch64.BitslicedNeon.ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

theorem eval_zero (s : VG.AArch64.State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr (VG.Proof.TripleDes.AArch64.BitslicedNeon.ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

theorem loop_ok (d : VG.Spec.TripleDes.Direction) {s₀ : VG.AArch64.State} (E : VG.Proof.TripleDes.AArch64.BitslicedNeon.Env s₀) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : VG.AArch64.State) (hs : VG.Proof.TripleDes.AArch64.BitslicedNeon.WideInv d s₀ n m s) :
    WP isa (.loop (.seq (.block [.addImm .x .x4 .x1 0]) (.seq (batch d)
        (.block [.addImm .x .x1 .x1 1024, .subImm .x .x2 .x2 128, wholeLeft])))
      (.nonzero .x .x10)) s (VG.Proof.TripleDes.AArch64.BitslicedNeon.WidePost d s₀ n) := by
  refine WP.loop (M := isa) (VG.Proof.TripleDes.AArch64.BitslicedNeon.WideInv d s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hge := h.ge
  have hle := h.le
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  have g := h.gpr
  have hx0 : s.gpr .x0 = S := g _ (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.WideRegs])
  apply WP.seq
  let s₁ := s.write .x .x4 (s.read .x .x1 + BitVec.ofNat _ 0)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have g₁ : ∀ r, r ≠ .x4 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  have x4₁ : s₁.gpr .x4 = wAt D (n - m) := by simp [s₁, State.write, State.read, h.x1]; rfl
  have dataR : (⟨D, 8 * n⟩ : Region) ∈ s₁.wr := by
    show _ ∈ s.wr; rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  have room₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s₁ := Ok.of_off (off := 8 * (n - m)) dataR (by show s₁.gpr .x4 = _; rw [x4₁]) (by
    show 8 * (n - m) + 16 * 64 ≤ 8 * n; omega) (by omega)
  have st₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₁ = ⟨wAt D (n - m), 1024⟩ := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, x4₁]
  have stSub : Region.Sub (VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₁) ⟨D, 8 * n⟩ := by
    rw [st₁]; exact Offset.sub_base _ (by omega)
  have S₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s₁ := by
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [g₁ _ (by decide), hx0]
      show InRegions (s.rd ++ s.wr) _ 8
      rw [h.rd, h.wr]; exact E.keyIn i hi
    · rw [g₁ _ (by decide), hx0]
      exact (hn ▸ E.keyData).sub_right stSub
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.batch_ok d room₁ S₁)
  intro s₂ q
  have g₂ : ∀ r, r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x4 → s₂.gpr r = s.gpr r :=
    fun r a b c e f => (q.gpr r a b c e).trans (g₁ r f)
  let s₃ := s₂.write .x .x1 (s₂.read .x .x1 + BitVec.ofNat _ 1024)
  let s₄ := s₃.write .x .x2 (s₃.read .x .x2 - BitVec.ofNat _ 128)
  let s₅ := s₄.write .x .x10 (s₄.read .x .x2 >>> 7)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, wholeLeft, exec_lsr_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  have x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 (m - 128) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x2,
      show (BitVec.ofNat 64 128) = BitVec.ofNat 64 128 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  have x1₅ : s₅.gpr .x1 = wAt D (n - (m - 128)) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1, wAt, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  have x10₅ : s₅.gpr .x10 = BitVec.ofNat 64 ((m - 128) / 128) := by
    simp only [s₅, State.write, State.read, BitVec.setWidth_eq, ite_true]
    have : s₄.gpr .x2 = s₅.gpr .x2 := by simp [s₅, State.write]
    rw [this, x2₅, VG.Proof.TripleDes.AArch64.BitslicedNeon.lsr7 _ (by omega)]
  have g₅ : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.WideRegs r → s₅.gpr r = s₀.gpr r := by
    intro r ⟨a, b, c, e, f, i, j⟩
    simp only [s₅, s₄, s₃, State.write, BitVec.setWidth_eq, j, b, a, ite_false]
    rw [g₂ r e f i j c, g r ⟨a, b, c, e, f, i, j⟩]
  have mem₅ : s₅.mem = s₂.mem := rfl
  -- the memory written so far
  have frame' : Frame [⟨D, 8 * (n - (m - 128))⟩] s₀.mem s₅.mem := by
    have f₁ : Frame [⟨D, 8 * (n - (m - 128))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
    have f₂ : Frame [⟨D, 8 * (n - (m - 128))⟩] s.mem s₂.mem := q.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by rw [st₁]; exact Offset.sub_base _ (by omega)⟩
    rw [mem₅]; exact f₁.trans f₂
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s₀.gpr .x3, 1024⟩ := hn ▸ E.dataBuf
  have done' : ∀ b < n - (m - 128), VG.Spec.TripleDes.blockAt s₅.mem (wAt D b) =
      blockOut (VG.Spec.TripleDes.scheduleAt s₀.mem S) d (VG.Spec.TripleDes.blockAt s₀.mem (wAt D b)) := by
    intro b hb
    rw [mem₅]
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine VG.Proof.TripleDes.Bitslice.blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [st₁]
      exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := q.out j (by omega)
      rw [x4₁, wAt_wAt] at e
      rw [e, g₁ _ (by decide), hx0]
      have hK : VG.Spec.TripleDes.scheduleAt s.mem S = VG.Spec.TripleDes.scheduleAt s₀.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega))
      have hB : VG.Spec.TripleDes.blockAt s.mem (wAt D (n - m + j)) = VG.Spec.TripleDes.blockAt s₀.mem (wAt D (n - m + j)) :=
        VG.Proof.TripleDes.Bitslice.blockAt_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (by omega) (by omega)
      show blockOut (VG.Spec.TripleDes.scheduleAt s₁.mem S) d (VG.Spec.TripleDes.blockAt s₁.mem _) = _
      rw [show s₁.mem = s.mem from rfl, hK, hB]
  have wr₅ : s₅.wr = s₀.wr := q.wr.trans h.wr
  have rd₅ : s₅.rd = s₀.rd := q.rd.trans h.rd
  have sp₅ : s₅.sp = s₀.sp := q.sp.trans h.sp
  have flag := VG.Proof.TripleDes.AArch64.BitslicedNeon.eval_nonzero s₅ .x10 x10₅ (by omega)
  by_cases hend : m - 128 < 128
  · left
    have e : m - 128 = n % 128 := by have := h.mod; omega
    refine ⟨by rw [flag]; simp; omega, by rw [x2₅, e], by rw [x1₅, e], g₅, rd₅, wr₅, sp₅,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by rw [flag]; simp; omega, m - 128, by omega,
      ⟨by omega, by omega, by have := h.mod; omega, x2₅, x1₅, g₅, rd₅, wr₅, sp₅, done', frame'⟩⟩

theorem wide_ok (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (E : VG.Proof.TripleDes.AArch64.BitslicedNeon.Env s) :
    WP isa (wide d) s (VG.Proof.TripleDes.AArch64.BitslicedNeon.WidePost d s (s.gpr .x2).toNat) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.read .x .x2 >>> 7)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 (n / 128) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show s.gpr .x2 = BitVec.ofNat 64 n by simp [n], VG.Proof.TripleDes.AArch64.BitslicedNeon.lsr7 _ hl]
  have g₁ : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  apply WP.ite _ (VG.Proof.TripleDes.AArch64.BitslicedNeon.eval_zero s₁ .x10 x10₁ (by omega))
  · intro hz
    have hz' : n < 128 := by simp at hz; omega
    apply WP.block_nil
    have e : n % 128 = n := Nat.mod_eq_of_lt hz'
    refine ⟨?_, ?_, fun r hr => g₁ r hr.2.2.2.2.2.2, rfl, rfl, rfl, fun b hb => by omega, ?_⟩
    · rw [g₁ _ (by decide), e]; simp [n]
    · rw [g₁ _ (by decide), e, Nat.sub_self]; simp [wAt]
    · rw [e, Nat.sub_self]; exact Frame.refl _ _
  · intro hnz
    have hge : 128 ≤ n := by simp at hnz; omega
    have E₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Env s₁ := by
      have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
      have h2 := g₁ .x2 (by decide); have h3 := g₁ .x3 (by decide)
      exact ⟨by rw [h0]; exact E.rd, by rw [h1, h2, h3]; exact E.wr,
        by rw [h0, h1, h2]; exact E.keyData, by rw [h0, h3]; exact E.keyBuf,
        by rw [h1, h2, h3]; exact E.dataBuf, by rw [h1, h2]; exact E.fit⟩
    have hn₁ : (s₁.gpr .x2).toNat = n := by rw [g₁ _ (by decide)]
    have I : VG.Proof.TripleDes.AArch64.BitslicedNeon.WideInv d s₁ n n s₁ := ⟨hge, Nat.le_refl _, rfl, by rw [g₁ _ (by decide)]; simp [n],
      by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega,
      by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.loop_ok d E₁ hn₁ n s₁ I)
    intro s₂ p
    have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
    refine ⟨p.x2, by rw [p.x1, h1], fun r hr => (p.gpr r hr).trans (g₁ r hr.2.2.2.2.2.2), p.rd, p.wr,
      p.sp, fun b hb => ?_, by rw [← h1]; exact p.frame⟩
    rw [← h1, p.done b hb, h0, h1]; rfl

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Tail`. -/
section

/-!
# The blocks left

Fewer than 128 blocks left (`k` of them, at `x1`) are copied into the
scratch buffer (at `x3`), run there as a batch whose other lanes hold
whatever the buffer held, and copied back (`tail_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame)

/-- What the blocks left need: the `k < 128` blocks at `x1` writable, the
scratch buffer at `x3` writable, the schedule at `x0` readable, apart from
each other. -/
structure TailEnv (s : VG.AArch64.State) (k : Nat) : Prop where
  lt : k < 128
  x2 : s.gpr .x2 = BitVec.ofNat 64 k
  dataW : ∀ i < k, InRegions s.wr (wAt (s.gpr .x1) i) 8
  scratch : (⟨s.gpr .x3, 1024⟩ : Region) ∈ s.wr
  key : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8
  keyData : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * k⟩
  keyBuf : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  dataBuf : (⟨s.gpr .x1, 8 * k⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩

/-- The registers the blocks left change. -/
def TailRegs (r : Reg) : Prop :=
  r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure TailPost (d : VG.Spec.TripleDes.Direction) (k : Nat) (s s' : VG.AArch64.State) : Prop where
  out : ∀ b < k, VG.Spec.TripleDes.blockAt s'.mem (wAt (s.gpr .x1) b) =
    blockOut (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (VG.Spec.TripleDes.blockAt s.mem (wAt (s.gpr .x1) b))
  gpr : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.TailRegs r → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr .x1, 8 * k⟩, ⟨s.gpr .x3, 1024⟩] s.mem s'.mem

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

theorem scratch_word {B : Addr} {i : Nat} (hi : i < 128) :
    (⟨B, 1024⟩ : Region).Contains (wAt B i) 8 := Offset.contains_base _ (by omega) (by omega)

theorem tail_ok (d : VG.Spec.TripleDes.Direction) {k : Nat} {s : VG.AArch64.State} (E : VG.Proof.TripleDes.AArch64.BitslicedNeon.TailEnv s k) :
    WP isa (VG.Impl.TripleDes.AArch64.BitsliceNeon.tail d) s (VG.Proof.TripleDes.AArch64.BitslicedNeon.TailPost d k s) := by
  let D := s.gpr .x1
  let B := s.gpr .x3
  let S := s.gpr .x0
  have hk := E.lt
  have scrIn : ∀ i < 128, InRegions s.wr (wAt B i) 8 := fun i hi => ⟨_, E.scratch, VG.Proof.TripleDes.AArch64.BitslicedNeon.scratch_word hi⟩
  rw [VG.Impl.TripleDes.AArch64.BitsliceNeon.tail]
  apply WP.ite _ (VG.Proof.TripleDes.AArch64.BitslicedNeon.eval_zero s .x2 E.x2 (by omega))
  · intro hz
    have hk0 : k = 0 := by simpa using hz
    subst hk0
    apply WP.block_nil
    exact ⟨fun b hb => by omega, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  · intro hnz
    have hk0 : k ≠ 0 := by simpa using hnz
    apply WP.seq
    -- x11 := x1, x12 := x3, x13 := x2
    let s₁ := ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).write .x .x12
      ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).read .x .x3 + BitVec.ofNat _ 0))
    let s₁' := s₁.write .x .x13 (s₁.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₁', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have g₁ : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₁'.gpr r = s.gpr r := by
      intro r a b c; simp [s₁', s₁, State.write, a, b, c]
    have pre₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyPre D B k s₁' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega⟩
      · obtain ⟨r, hr, hc⟩ := E.dataW i hi
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      · exact scrIn i (by omega)
      · exact E.dataBuf.sub_right (Region.sub_prefix (by omega))
    have inv₁ : VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyInv D B k s₁' 0 s₁' := by
      refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_zero]; simp [s₁', s₁, State.write, State.read, D]
      · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_zero]; simp [s₁', s₁, State.write, State.read, B]
      · simp [s₁', s₁, State.write, State.read, E.x2]
    apply WP.seq
    apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.copy_ok pre₁ s₁' 0 inv₁)
    intro s₂ c₂
    have g₂ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s.gpr r :=
      fun r a b c e => (c₂.regs r ⟨a, b, c, e⟩).trans (g₁ r b c e)
    apply WP.seq
    -- x4 := x3
    let s₃ := s₂.write .x .x4 (s₂.read .x .x3 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₃, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have g₃ : ∀ r, r ≠ .x4 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₃.gpr r = s.gpr r := by
      intro r a b c e f; simp only [s₃, State.write, a, ite_false]; exact g₂ r b c e f
    have x4₃ : s₃.gpr .x4 = B := by
      simp [s₃, State.write, State.read]; exact g₂ _ (by decide) (by decide) (by decide) (by decide)
    have wr₃ : s₃.wr = s.wr := c₂.wr
    have room₃ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Room s₃ := Ok.of_off (off := 0) (by rw [wr₃]; exact E.scratch)
      (by show s₃.gpr .x4 = _; rw [x4₃]; simp [B]) (by show 0 + 16 * 64 ≤ 1024; decide) (by show 1024 < 2 ^ 64; decide)
    have st₃ : VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR s₃ = ⟨B, 1024⟩ := by simp only [VG.Proof.TripleDes.AArch64.BitslicedNeon.stateR, x4₃]
    have S₃ : VG.Proof.TripleDes.AArch64.BitslicedNeon.Sched s₃ := by
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        show InRegions (s₂.rd ++ s₂.wr) _ 8
        rw [c₂.rd, c₂.wr]; exact E.key i hi
      · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), st₃]; exact E.keyBuf
    apply WP.seq
    apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.batch_ok d room₃ S₃)
    intro s₄ q₄
    have g₄ : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.TailRegs r → s₄.gpr r = s.gpr r := by
      intro r ⟨a, b, c, e, f, i, j, l⟩
      rw [q₄.gpr r b c e f, g₃ r a f i j l]
    apply WP.seq
    -- x11 := x3, x12 := x1, x13 := x2
    let s₅ := ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).write .x .x12
      ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).read .x .x1 + BitVec.ofNat _ 0))
    let s₅' := s₅.write .x .x13 (s₅.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₅', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have g₅ : ∀ r, VG.Proof.TripleDes.AArch64.BitslicedNeon.TailRegs r → s₅'.gpr r = s.gpr r := by
      intro r hr
      have ⟨_, _, _, _, _, i, j, l⟩ := hr
      simp only [s₅', s₅, State.write, i, j, l, ite_false]; exact g₄ r hr
    have wr₅ : s₅'.wr = s.wr := q₄.wr.trans wr₃
    have rd₅ : s₅'.rd = s.rd := q₄.rd.trans c₂.rd
    have pre₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyPre B D k s₅' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega⟩
      · obtain ⟨r, hr, hc⟩ := scrIn i (by omega)
        rw [wr₅]; exact ⟨r, List.mem_append_right _ hr, hc⟩
      · rw [wr₅]; exact E.dataW i hi
      · exact (E.dataBuf.sub_right (Region.sub_prefix (by omega))).symm
    have inv₂ : VG.Proof.TripleDes.AArch64.BitslicedNeon.CopyInv B D k s₅' 0 s₅' := by
      refine ⟨by omega, ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · rw [VG.Proof.TripleDes.AArch64.BitslicedNeon.wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      · simp [s₅', s₅, State.write, State.read]
        rw [g₄ _ ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide⟩, E.x2]
    apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.copy_ok pre₂ s₅' 0 inv₂)
    intro s₆ c₆
    -- memory
    have m₃ : s₃.mem = s₂.mem := rfl
    have m₅ : s₅'.mem = s₄.mem := rfl
    have dataSep : (⟨D, 8 * k⟩ : Region).Disjoint ⟨B, 8 * k⟩ :=
      E.dataBuf.sub_right (Region.sub_prefix (by omega))
    have K₃ : VG.Spec.TripleDes.scheduleAt s₃.mem (s₃.gpr .x0) = VG.Spec.TripleDes.scheduleAt s.mem S := by
      rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), m₃]
      exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S c₂.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.keyBuf.sub_right (Region.sub_prefix (by omega))
    refine ⟨fun b hb => ?_, fun r hr => (c₆.regs r ⟨hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2⟩).trans (g₅ r hr), c₆.rd.trans rd₅, c₆.wr.trans wr₅,
      c₆.sp.trans (q₄.sp.trans c₂.sp), ?_⟩
    · -- the block in the data, from the scratch buffer after the batch
      have e₆ : VG.Spec.TripleDes.blockAt s₆.mem (wAt D b) = VG.Spec.TripleDes.blockAt s₄.mem (wAt B b) := by
        rw [← m₅]; exact VG.Proof.TripleDes.AArch64.BitslicedNeon.blockAt_eq_of_readW (c₆.copied b hb)
      -- the block in the scratch buffer before the batch, from the data
      have e₂ : VG.Spec.TripleDes.blockAt s₂.mem (wAt B b) = VG.Spec.TripleDes.blockAt s.mem (wAt D b) := by
        refine VG.Proof.TripleDes.AArch64.BitslicedNeon.blockAt_eq_of_readW ((c₂.copied b hb).trans ?_)
        rfl
      rw [e₆]
      have o := q₄.out b (by omega)
      rw [x4₃, K₃, m₃, e₂] at o
      exact o
    · have a : Frame [⟨D, 8 * k⟩, ⟨B, 1024⟩] s.mem s₂.mem := c₂.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
      have b : Frame [⟨D, 8 * k⟩, ⟨B, 1024⟩] s₂.mem s₄.mem := q₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [st₃]; exact fun _ h => h⟩
      have c : Frame [⟨D, 8 * k⟩, ⟨B, 1024⟩] s₅'.mem s₆.mem := c₆.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      rw [m₅] at c
      exact (a.trans b).trans c

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified`. -/
section

/-! # The AdvSIMD bitsliced ECB functions meet their contracts -/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame ecb_blocks)
open VG.Proof.TripleDes.AArch64.Ecb (contract)

def satState : VG.AArch64.State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem publicRegs_four (s₁ s₂ : VG.AArch64.State) :
    VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [VG.Proof.TripleDes.AArch64.PublicRegs]

/-- Every block becomes its encryption or decryption. -/
theorem ecb_correct (d : VG.Spec.TripleDes.Direction) {s : VG.AArch64.State} (E : VG.Proof.TripleDes.AArch64.BitslicedNeon.Env s) :
    WP isa (ecb d) s (fun s' => ∀ b < (s.gpr .x2).toNat, VG.Spec.TripleDes.blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (VG.Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (VG.Spec.TripleDes.blockAt s.mem (wAt (s.gpr .x1) b))) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  let k := n % 128
  have hl := E.len
  have hfit := E.fit
  rw [Impl.TripleDes.AArch64.BitsliceNeon.ecb]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.wide_ok d E)
  intro s₁ w
  have g := w.gpr
  have h0 : s₁.gpr .x0 = S := g _ (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.WideRegs])
  have h3 : s₁.gpr .x3 = s.gpr .x3 := g _ (by simp [VG.Proof.TripleDes.AArch64.BitslicedNeon.WideRegs])
  have h1 : s₁.gpr .x1 = wAt D (n - k) := w.x1
  have sub₁ : Region.Sub ⟨s₁.gpr .x1, 8 * k⟩ ⟨D, 8 * n⟩ := by
    rw [h1]; exact Offset.sub_base _ (by omega)
  have T : VG.Proof.TripleDes.AArch64.BitslicedNeon.TailEnv s₁ k := by
    refine ⟨Nat.mod_lt _ (by decide), w.x2, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [w.wr, E.wr, h1, wAt_wAt]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [w.wr, E.wr, h3]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [w.rd, w.wr, h0]; exact E.keyIn i hi
    · rw [h0]; exact E.keyData.sub_right sub₁
    · rw [h0, h3]; exact E.keyBuf
    · rw [h3]; exact E.dataBuf.sub_left sub₁
  apply WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.tail_ok d T)
  intro s' t
  intro b hb
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩ := E.dataBuf
  by_cases hbk : b < n - k
  · rw [← w.done b hbk]
    refine VG.Proof.TripleDes.Bitslice.blockAt_frame t.frame fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h1]; exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · rw [h3]; exact dataB.sub_left (Offset.sub_base _ (by omega))
  · obtain ⟨j, rfl⟩ : ∃ j, b = n - k + j := ⟨b - (n - k), by omega⟩
    have e := t.out j (by omega)
    rw [h1, wAt_wAt, h0] at e
    rw [e]
    have hK : VG.Spec.TripleDes.scheduleAt s₁.mem S = VG.Spec.TripleDes.scheduleAt s.mem S :=
      VG.Proof.TripleDes.scheduleAt_eq_of_frame S w.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.keyData.sub_right (Region.sub_prefix (by omega))
    have hB : VG.Spec.TripleDes.blockAt s₁.mem (wAt D (n - k + j)) = VG.Spec.TripleDes.blockAt s.mem (wAt D (n - k + j)) :=
      VG.Proof.TripleDes.Bitslice.blockAt_frame w.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base D (by omega) (by omega)
    rw [hK, hB]

theorem ecb_contract (d : VG.Spec.TripleDes.Direction) (s : VG.AArch64.State) (hs : (contract d).pre s) :
    WP isa (ecb d) s (fun s' => (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  exact WP.mono (VG.Proof.TripleDes.AArch64.BitslicedNeon.ecb_correct d ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩) fun s' h =>
    ecb_blocks _ _ _ _ _ _ h

theorem encrypt_correct (s : VG.AArch64.State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, hp, hg⟩ := WP.gprs (c := encrypt) (VG.Proof.TripleDes.AArch64.BitslicedNeon.ecb_contract .encrypt s hs) (rs := preserved)
    (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : VG.AArch64.State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, hp, hg⟩ := WP.gprs (c := decrypt) (VG.Proof.TripleDes.AArch64.BitslicedNeon.ecb_contract .decrypt s hs) (rs := preserved)
    (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem encrypt_verified : Verified target encrypt (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct VG.Proof.TripleDes.AArch64.BitslicedNeon.encrypt_correct (VG.Proof.TripleDes.AArch64.BitslicedNeon.encrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, VG.Proof.TripleDes.AArch64.BitslicedNeon.publicRegs_four] [satState] using VG.Proof.TripleDes.AArch64.BitslicedNeon.satState

theorem decrypt_verified : Verified target decrypt (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct VG.Proof.TripleDes.AArch64.BitslicedNeon.decrypt_correct (VG.Proof.TripleDes.AArch64.BitslicedNeon.decrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, VG.Proof.TripleDes.AArch64.BitslicedNeon.publicRegs_four] [satState] using VG.Proof.TripleDes.AArch64.BitslicedNeon.satState

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end
