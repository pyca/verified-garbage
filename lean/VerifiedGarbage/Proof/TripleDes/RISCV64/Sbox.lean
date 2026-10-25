module

public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
import VerifiedGarbage.Proof.Framework.Mem

/-!
# DES S-box machine-code correctness

Untrusted. The kernel checks each allocated circuit on all 64 inputs at
once, as truth tables (`Bitslice.table`), and the run relates each table to
the concrete word at every bit position (`TabAll`, as for AES:
`Proof/Aes/RISCV64/Layers.lean`). This verifies both the circuits and the
allocator's output, including spills.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (inputTable outputTable testBit_outputTable)

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])

/-- The S-boxes' memory: slots 0–30 of the frame (they store only to the
spill slots, 15–30: `Spills.lean`). -/
def sboxCfg : Cfg := { base := sb, slots := 31, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => q k == r)).map fun k => .v (inputTable k),
    slot := fun _ => none }

def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => word (e.reg (q j)) == some (outputTable i j)

theorem sbox_check : ∀ i < 8,
    check (table 64 64) sboxCfg (fun _ => none) (instrs (sboxLiteral i))
      sboxEnv (sboxPost i) = true := by
  lit_decide

/-- The registers the S-boxes keep. -/
def sboxKept : List Reg := [.ra, .s1, .s2, .s3, .s4, .a0, .a1, .a2, .a3, .a4, .a5, .a6]

theorem sbox_preserves : ∀ i < 8,
    sboxKept.all (fun r => (instrs (sboxLiteral i)).all fun op => dst op != some r) = true := by
  decide +kernel

def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.gpr (q j)).getLsbD p

theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k = (s.gpr (q k)).getLsbD p := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxLiteral_eq : ∀ i < 8, sboxLiteral i = .block (sboxCode i)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

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

/-- Every S-box output bit, for arbitrary input words and any readable/
writable slots. Only the slots can change. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        (Spec.TripleDes.sBox i (inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ sboxKept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral i) = sboxCode i := by rw [sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.reg (q j) = some (.v (outputTable i j)) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at this
    cases h : e'.reg (q j) with
    | none => rw [h] at this; cases this
    | some v => cases v <;> rw [h] at this <;> simp_all [word]
  let cs : Nat → Nat := fun p => (inputAt s p).toNat
  have hcs : ∀ p < 64, cs p < 64 := fun p _ => (inputAt s p).isLt
  have hrel : Rel (TabAll cs) sboxCfg (fun _ => none) sboxEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    intro p hp
    simp only [TableRel, inputTable, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
      inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) tabAll_fun hok hrel he
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have h := p₀.rel.reg (q j) _ (hout j hj) p hp
    simp only [TableRel, testBit_outputTable (hcs p hp), cs, BitVec.ofNat_toNat] at h
    exact h.symm
  · have h := List.all_eq_true.mp (sbox_preserves i hi) r hr
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.RISCV64
