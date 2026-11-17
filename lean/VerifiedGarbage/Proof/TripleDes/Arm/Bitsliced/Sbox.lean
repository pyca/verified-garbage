module

public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.Arm.StraightNot
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.Arm.StraightNot
meta import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# The bitsliced S-box circuits' machine code on ARMv7

Untrusted. The kernel checks each allocated circuit on all 64 inputs, with
its values spilled to the first words of the working space (`sboxCfg`), and
the truth-table evaluator lifts that check to every bit position of
arbitrary 32-bit words. The circuits write only those words of memory
(`sbox_ok`'s frame), and never the working space's base.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm.Bitslice
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

/-- The words the circuits spill to. -/
def sboxCfg : Cfg := { base := .r3, slots := spills, ext := .r3, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg j i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    checkN (table 32 64) sboxCfg (fun _ => none) (instrs (sboxLiteral j)) sboxEnv (sboxPost j) = true := by
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

/-- Bit `p` of each input register, as the S-box's input. -/
def inputsAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.gpr (inReg i)).getLsbD p

theorem inputsAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputsAt s p).toNat.testBit k = (s.gpr (inReg k)).getLsbD p := by
  simp only [inputsAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

/-- Every S-box output bit, for arbitrary input words; only the spilled
words of memory change, and not the working space's base. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ p < 32, (s'.gpr (outReg j i)).getLsbD p =
        (Spec.TripleDes.sBox j (inputsAt s p)).getLsbD i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r3 = s.gpr .r3 ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_checkN _ _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg j i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 32, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (TableRel p (inputsAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode j).all fun op => !clobbers op r) = false) := by
    intro p hp
    have hc := (inputsAt s p).isLt
    refine runN (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      inputsAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun i hi p hp => ?_, p₀.rd, p₀.wr, p₀.sp, p₀.base, p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key p hp
  obtain rfl := run_unique hs'' hs'
  have h := p₁.rel.reg (outReg j i) _ (hout i hi)
  simp only [TableRel, outputTable, testBit_tableOf, (inputsAt s p).isLt,
    decide_true, Bool.true_and] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.Arm.Bitsliced
