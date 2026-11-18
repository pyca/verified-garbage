module

public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# The bitsliced S-box circuits' machine code on x86 (32-bit)

Untrusted. As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Sbox.lean`): the
kernel checks each allocated circuit on all 64 inputs, with its inputs in
the first six words of the working space and its values spilled to the
words after them (`sboxCfg`), and the truth-table evaluator lifts that check
to every bit position of arbitrary 32-bit words. The circuits write only
those words of memory (`sbox_ok`'s frame), and never the working space's
base.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86.Bitslice
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

/-- The words the circuits use: their inputs and the values they spill. -/
def sboxCfg : Cfg := { base := .ebp, slots := spills, ext := .ebp, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun _ => none,
    slot := fun k => if k < 6 then some (inputTable k) else none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    check (table 32 64) sboxCfg (fun _ => none) (instrs (sboxLiteral j)) sboxEnv (sboxPost j) = true := by
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

/-- Bit `p` of each input word, as the S-box's input. -/
def inputsAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun i => (fw s i).getLsbD p

theorem inputsAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputsAt s p).toNat.testBit k = (fw s k).getLsbD p := by
  simp only [inputsAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

/-- Every S-box output bit, for arbitrary input words; only the circuits'
words of memory change, and not the working space's base. -/
theorem sbox_ok (j : Nat) (hj : j < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ p < 32, (s'.gpr (outReg i)).getLsbD p =
        (Spec.TripleDes.sBox j (inputsAt s p)).getLsbD i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg i) = some (outputTable j i) := by
    intro i hi
    have h := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    exact beq_iff_eq.mp h
  have key : ∀ p < 32, ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      Post (TableRel p (inputsAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode j).all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (inputsAt s p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a hk h => ?_,
      (fun _ _ hk => by simp [sboxCfg] at hk)⟩ he
    simp only [sboxEnv] at h
    split at h
    · rename_i hk6
      cases h
      simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
        inputsAt_bit s p k hk6]
      rfl
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  have nesp : ((sboxCode j).all fun i => i.dst != some .esp) = true := by
    have : ∀ j < 8, ((sboxCode j).all fun i => i.dst != some .esp) = true := by lit_decide
    exact this j hj
  refine ⟨s', hs', fun i hi p hp => ?_, p₀.rd, p₀.wr, p₀.base, p₀.other _ (by rw [nesp]; exact Bool.noConfusion),
    p₀.frame⟩
  obtain ⟨s'', hs'', p₁⟩ := key p hp
  obtain rfl := run_unique hs'' hs'
  have h := p₁.rel.reg (outReg i) _ (hout i hi)
  simp only [TableRel, outputTable, testBit_tableOf, (inputsAt s p).isLt,
    decide_true, Bool.true_and] at h
  rw [BitVec.ofNat_toNat] at h
  exact h.symm

end VG.Proof.TripleDes.X86.Bitsliced
