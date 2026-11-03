module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Straight
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.Framework.RISCV64.Linear

/-!
# The bitsliced S-box circuits' machine code on RISC-V

Untrusted. The kernel checks each allocated circuit on all 64 inputs, and
the truth-table evaluator lifts that check to every bit position of
arbitrary 64-bit words (`TabAll`, a relation at every position at once,
which makes it a function, as the evaluator needs), as for SM4's S-box
(`Proof/Sm4/RISCV64/Sbox.lean`). The circuits use only registers, and write
only the inputs' and the free registers (`sbox_keeps`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice
open VG.Proof.TripleDes (inputTable outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (j : Nat) : Prog isa := sboxLiterals.getD j (.block [])

/-- The circuits touch no memory. -/
def sboxCfg : Cfg := { base := .s0, slots := 0, ext := .s0, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => inReg k == r)).map fun k => .v (inputTable k),
    slot := fun _ => none }

def sboxPost (j : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun i => word (e.reg (outReg j i)) == some (outputTable j i)

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
def sboxKept : List Reg := [.s0, .a1, .a2, .a3, .a4, .a5, .a6]

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

theorem tabAll_fun {cs : Nat → Nat} (a : Nat) (x y : BitVec 64) (hx : TabAll cs a x)
    (hy : TabAll cs a y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have h1 := hx p hp
  have h2 := hy p hp
  simp only [TableRel] at h1 h2
  rw [← h1, ← h2]

/-- Bit `p` of each input register, as the S-box's input. -/
def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun i => (s.gpr (inReg i)).getLsbD p

theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k = (s.gpr (inReg k)).getLsbD p := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxCfg_ok (s : State) : Ok sboxCfg s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [sboxCfg]

/-- Every S-box output bit, for arbitrary input words; only the circuit's
registers change. -/
theorem sbox_ok (j : Nat) (hj : j < 8) (s : State) :
    ∃ s', runBlock isa (sboxCode j) s = some s' ∧
      (∀ i < 4, ∀ p < 64, (s'.gpr (outReg j i)).getLsbD p =
        (Spec.TripleDes.sBox j (inputAt s p)).getLsbD i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r ∈ sboxKept, s'.gpr r = s.gpr r) := by
  have codeEq : instrs (sboxLiteral j) = sboxCode j := by rw [sboxLiteral_eq j hj]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check j hj)
  rw [codeEq] at he
  have hout : ∀ i < 4, e'.reg (outReg j i) = some (.v (outputTable j i)) := by
    intro i hi
    have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    cases h : e'.reg (outReg j i) with
    | none => rw [h] at this; cases this
    | some v => cases v <;> rw [h] at this <;> simp_all [word]
  let cs : Nat → Nat := fun p => (inputAt s p).toNat
  have hcs : ∀ p < 64, cs p < 64 := fun p _ => (inputAt s p).isLt
  have hrel : Rel (TabAll cs) sboxCfg (fun _ => none) sboxEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    intro p hp
    simp only [TableRel, inputTable, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
      inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) tabAll_fun (sboxCfg_ok s) hrel he
  have hmem : s'.mem = s.mem := by
    funext x
    exact p₀.frame x fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, sboxCfg, Region.Contains] at hc
  refine ⟨s', hs', fun i hi p hp => ?_, p₀.rd, p₀.wr, p₀.sp, hmem, fun r hr => p₀.other r ?_⟩
  · have hc := hcs p hp
    have := p₀.rel.reg (outReg j i) _ (hout i hi) p hp
    simp only [TableRel] at this
    rw [← this, VG.Proof.TripleDes.testBit_outputTable hc]
    simp only [cs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have h := List.all_eq_true.mp (sbox_keeps j hj) r hr
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.RISCV64.Bitsliced
