module

public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `TripleDes.AArch64.Bitsliced.Machine`, which the modules that import this one used -/

section

/-!
# The AdvSIMD machine state of a batch

The 64 state words are the 16-byte slots at `x4` (`words`), in a writable
region (`Room`). Code that only moves and XORs whole words (the S-box
outputs, the exchange of the halves) is checked on the variable domain,
doubleword lane by doubleword lane (`varsRun`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Bitslice
open VG.Impl.TripleDes.AArch64.BitsliceNeon

/-- The state words. -/
def stateCfg : Cfg := { base := .x4, slots := 64 }

/-- State word `j`. -/
def words (s : State) (j : Nat) : BitVec 128 := s.mem.readW (vAddr (s.gpr .x4) j) 128

/-- Doubleword lane `q` of the state words. -/
def laneW (s : State) (q : Nat) : Nat → BitVec 64 := fun j => vdword (words s j) q

/-- The state words' area. -/
def stateR (s : State) : Region := ⟨s.gpr .x4, 1024⟩

/-- What a batch's code needs of the machine: the state words writable. -/
abbrev Room (s : State) : Prop := Ok stateCfg s

theorem room_congr {s s' : State} (h : Room s) (hb : s'.gpr .x4 = s.gpr .x4) (hw : s'.wr = s.wr) :
    Room s' := h.congr hb hw

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

theorem eq_of_vdword {x y : BitVec 128} (h : ∀ q < 2, vdword x q = vdword y q) : x = y :=
  vec64_ext (h 0 (by decide)) (h 1 (by decide))

/-! ## Words as XORs of variables -/

/-- Slot `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List VReg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables, in doubleword lane `q`. -/
def varVals (s : State) (regs : List VReg) (q v : Nat) : BitVec 64 :=
  if v < 64 then laneW s q v else vdword (s.v (regs.getD (v - 64) .v0)) q

def varN (regs : List VReg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List VReg) :
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

/-- Run a block that the variable domain accepts on the state words. -/
theorem varsRun {is : List Instr} (regs : List VReg) {post : Env Nat → Bool}
    (hchk : check (vars 64) stateCfg is (varEnv regs) post = true) {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (fun q => VarRel (varVals s regs q) (varN regs)) stateCfg e' s s'
        (fun r => (is.all fun i => vdstOf i != some r) = false)
        (fun r => (is.all fun i => !clobbers i r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  obtain ⟨s', hs', p⟩ := run (fun q _ => vars_sound _ _) h (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-- The all-zero or all-one word. -/
def maskX (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

theorem getLsbD_maskX (b : Bool) {P : Nat} (hP : P < 128) : (maskX b).getLsbD P = b := by
  cases b
  · simp [maskX]
  · simp only [maskX, ite_true, BitVec.getLsbD_allOnes, hP, decide_true]

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-!
# The AdvSIMD S-box circuits' machine code

Untrusted. The kernel checks each allocated circuit on all 64 inputs once,
and the doubleword-lane evaluator (`StraightV`) with the truth-table domain
lifts that check to every bit position of every doubleword of arbitrary
128-bit words. The circuits use only vector registers, and neither the key
nor the zero register.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.Bitslice VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

/-- No slots: the circuits access no memory. -/
def sboxCfg : Cfg := { base := .x4, slots := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg j i) == some (outputTable j i)

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
    (instrs (sboxLiteral j)).all (fun op => vdstOf op != some keyReg && vdstOf op != some zeroReg &&
      (dsts op).isEmpty) = true := by
  decide +kernel

/-- Bit `P` of each input register, as the S-box's input. -/
def inputAt (s : State) (P : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.v (inReg i)).getLsbD P

theorem inputAt_bit (s : State) (P k : Nat) (hk : k < 6) :
    (inputAt s P).toNat.testBit k = (s.v (inReg k)).getLsbD P := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxOk (s : State) : Ok sboxCfg s := ⟨fun _ h => absurd h (by simp [sboxCfg]), by decide⟩

/-- Every S-box output bit, for arbitrary input words. Memory, the
general-purpose registers and the key and zero registers do not change. -/
theorem sbox_ok (j : Nat) (hj : j < 8) (s : State) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ P < 128, (s'.v (outReg j i)).getLsbD P =
        (Spec.TripleDes.sBox j (inputAt s P)).getLsbD i) ∧
      s'.gpr = s.gpr ∧ s'.c = s.c ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.v keyReg = s.v keyReg ∧ s'.v zeroReg = s.v zeroReg ∧ s'.mem = s.mem := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg j i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (fun q => TableRel p (inputAt s (64 * q + p)).toNat) sboxCfg e' s s'
        (fun r => ((sboxCode j).all fun op => vdstOf op != some r) = false)
        (fun r => ((sboxCode j).all fun op => !clobbers op r) = false) := by
    intro p hp
    refine run (fun q _ => table_sound hp (inputAt s (64 * q + p)).isLt) (sboxOk s)
      ⟨fun r a h q hq => ?_, (fun _ _ hk _ => absurd hk (by simp [sboxCfg])), (fun _ _ h => by cases h)⟩ he
    have hc := (inputAt s (64 * q + p)).isLt
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      inputAt_bit s _ k hk6, getLsbD_vdword _ hp]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  have pres := sbox_preserves j hj
  rw [codeEq] at pres
  have pres' := List.all_eq_true.mp pres
  have noV : ∀ r, (r = keyReg ∨ r = zeroReg) →
      ¬ ((sboxCode j).all fun op => vdstOf op != some r) = false := by
    intro r hr
    simp only [Bool.not_eq_false, List.all_eq_true, bne_iff_ne, ne_eq]
    intro op hop h
    have := pres' op hop
    rcases hr with rfl | rfl <;> simp [h] at this
  have frame0 : s'.mem = s.mem := by
    funext a
    exact p₀.frame a (by simp [slotRegion, sboxCfg, Region.Contains])
  refine ⟨s', hs', fun i hi P hP => ?_, funext fun r => p₀.gpr r (by
      simp only [Bool.not_eq_false, List.all_eq_true]
      intro op hop
      have := pres' op hop
      simp only [Bool.and_eq_true] at this
      simpa using clobbers_eq_false_of_isEmpty (r := r) this.2),
    p₀.carry, p₀.sp, p₀.rd, p₀.wr, p₀.other _ (noV _ (Or.inl rfl)), p₀.other _ (noV _ (Or.inr rfl)),
    frame0⟩
  obtain ⟨s'', hs'', p₁⟩ := key (P % 64) (Nat.mod_lt _ (by decide))
  rw [hs'] at hs''
  cases hs''
  have h := p₁.rel.reg (outReg j i) _ (hout i hi) (P / 64) (by omega_using [hP])
  have eP : 64 * (P / 64) + P % 64 = P := Nat.div_add_mod P 64
  simp only [TableRel, outputTable, testBit_tableOf, (inputAt s _).isLt,
    decide_true, Bool.true_and, eP, getLsbD_vdword _ (Nat.mod_lt _ (by decide) : P % 64 < 64)] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.AArch64.BitslicedNeon
