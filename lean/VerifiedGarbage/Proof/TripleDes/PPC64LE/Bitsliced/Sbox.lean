module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# The bitsliced S-box circuits' machine code on PPC64LE

Untrusted. The kernel checks each allocated circuit on all 64 inputs, and
the truth-table evaluator lifts that check to every bit position of
arbitrary 64-bit words (`TabAll`, a relation at every position at once),
as on RISC-V (`Proof/TripleDes/RISCV64/Bitsliced/Sbox.lean`). The register
`r11` holds all ones, the table whose every row is true. The circuits use
only registers, and write only the inputs' and the free registers
(`sbox_keeps`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.Straight VG.Bitslice VG.Impl.TripleDes.PPC64LE.Bitslice
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

/-- The circuits touch no memory. -/
def sboxCfg : Cfg := { base := .r10, slots := 0, ext := .r10, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => if r = .r11 then some (2 ^ 64 - 1) else
      ((List.range 6).find? (fun k => inReg k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => e.reg (outReg j i) == some (outputTable j i)

theorem sbox_check : ∀ j < 8,
    check (table 64 64) sboxCfg (fun _ => none) (instrs (sboxLiteral j)) sboxEnv (sboxPost j) = true := by
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

/-- The registers the circuits leave alone. -/
def sboxKept : List Reg := [.r10, .r3, .r4, .r5, .r7, .r8, .r9, .r11, .r0]

theorem sbox_keeps : ∀ j < 8,
    sboxKept.all (fun r => (instrs (sboxLiteral j)).all fun op => dst op != some r) = true := by
  lit_decide

/-- A table related to a word at every bit position `p`, row `cs p`. -/
def TabAll (cs : Nat → Nat) (a : Nat) (x : BitVec 64) : Prop := ∀ p < 64, TableRel p (cs p) a x

theorem tabAll_sound {cs : Nat → Nat} (hcs : ∀ p < 64, cs p < 64) :
    (table 64 64).Sound (TabAll cs) where
  xor ha hb h p hp := (table_sound hp (hcs p hp)).xor (ha p hp) (hb p hp) h
  and ha hb h p hp := (table_sound hp (hcs p hp)).and (ha p hp) (hb p hp) h
  or ha hb h p hp := (table_sound hp (hcs p hp)).or (ha p hp) (hb p hp) h
  ror _ h := by cases h
  shr _ h := by cases h
  const h p hp := (table_sound hp (hcs p hp)).const h

/-- Bit `p` of each input register, as the S-box's input. -/
def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.gpr (inReg i)).getLsbD p

theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k = (s.gpr (inReg k)).getLsbD p := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxCfg_ok (s : State) : Ok sboxCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sboxCfg]

theorem inReg_ne_r11 : ∀ k < 6, inReg k ≠ .r11 := by decide

/-- Every S-box output bit, for arbitrary input words, with all ones in
`r11`; only the circuit's registers change. -/
theorem sbox_ok (j : Nat) (hj : j < 8) (s : State) (hones : s.gpr .r11 = BitVec.allOnes 64) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ p < 64, (s'.gpr (outReg j i)).getLsbD p =
        (Spec.TripleDes.sBox j (inputAt s p)).getLsbD i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.mem = s.mem ∧
      (∀ r ∈ sboxKept, s'.gpr r = s.gpr r) := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg j i) = some (outputTable j i) := by
    intro i hi
    have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simpa using this
  let cs : Nat → Nat := fun p => (inputAt s p).toNat
  have hcs : ∀ p < 64, cs p < 64 := fun p _ => (inputAt s p).isLt
  have hrel : Rel (TabAll cs) sboxCfg (fun _ => none) sboxEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    simp only [sboxEnv] at h
    split at h
    · rename_i hr
      subst hr
      cases h
      intro p hp
      simp only [TableRel, hones, BitVec.getLsbD_allOnes, hp, decide_true]
      exact Nat.testBit_two_pow_sub_one .. ▸ (by simpa using hcs p hp)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      have hqr := List.find?_some hk
      have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
      simp only [beq_iff_eq] at hqr
      subst hqr
      intro p hp
      simp only [TableRel, inputTable, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
        inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) (sboxCfg_ok s) hrel he
  have hmem : s'.mem = s.mem := by
    funext x
    exact p₀.frame x fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, sboxCfg, Region.Contains] at hc
  refine ⟨s', hs', fun i hi p hp => ?_, p₀.rd, p₀.wr, p₀.sp, p₀.lr, hmem, fun r hr => p₀.other r ?_⟩
  · have hc := hcs p hp
    have := p₀.rel.reg (outReg j i) _ (hout i hi) p hp
    simp only [TableRel] at this
    rw [← this, VG.Proof.TripleDes.testBit_outputTable hc]
    simp only [cs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have h := List.all_eq_true.mp (sbox_keeps j hj) r hr
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.PPC64LE.Bitsliced
