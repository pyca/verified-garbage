module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Straight
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.Framework.RISCV64.Linear

/-! ### `TripleDes.RISCV64.Bitsliced.Step`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.Bitsliced.Sbox`, which only this module used -/

section

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
def sboxKept : List Reg := [.s0, .a1, .a2, .a3, .a4, .a5, .a6, .s11, .ra]

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

end

end

/-!
# One S-box of a bitsliced round on RISC-V, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the key's bits `inBit j i`
of `a5` as masks XORed with the words of `E`; its circuit; XORing its
outputs into their words) does to the state words what `step` does.
`swapHalves_ok`: the exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Interleave.runBlock_append, h₁, Option.bind_some, h₂]

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- Bit `c` of `q` shifted to the top and arithmetically back. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = maskVal (q.getLsbD c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega_using [], decide_false, Bool.not_false, show 63 - (63 - c) = c by omega_using [hc]]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega_arith); rfl, key]
  unfold maskVal
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega_using [hi], decide_false,
      Bool.not_false, Bool.and_true]

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 64) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .a5 ∧ inReg i ≠ .a6 ∧ inReg i ≠ .s0 ∧ inReg i ≠ .a1 ∧
    inReg i ≠ .a2 ∧ inReg i ≠ .a3 ∧ inReg i ≠ .a4 := by decide

theorem inReg_inj : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

theorem slot_al {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    (s.gpr .s0 + BitVec.ofNat 64 (stOff w)).toNat % 8 = 0 :=
  wordAddr_al h.al w (by omega_using [hw])

theorem slot_rd {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (s.gpr .s0 + BitVec.ofNat 64 (stOff w)) 8 :=
  let ⟨r, hr, hc⟩ := slot_in h (k := w) (by omega_using [hw]); ⟨r, List.mem_append_right _ hr, hc⟩

/-- One input into `q`: key bit `b` of `a5` as a mask, XORed with state word `w`. -/
theorem inputStep_run' {s : State} (h : Room s) {q : Reg} (h6 : q ≠ .a6) (h0 : q ≠ .s0)
    {b w : Nat} (hb : b < 48) (hw : w < 64) :
    ∃ s', runBlock isa [.shift .sll .d q key (63 - b), .shift .sra .d q q 63,
        .load .d tmp base (stOff w), .logic .xor q q tmp] s = some s' ∧
      s'.gpr q = maskVal ((s.gpr .a5).getLsbD b) ^^^ sl s w ∧
      (∀ r, r ≠ q → r ≠ .a6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.write q (s.gpr .a5 <<< (63 - b))
  have e₁ : exec (.shift .sll .d q .a5 (63 - b)) s = some s₁ := exec_shift_d (by omega_using [])
  let s₂ := s₁.write q ((s₁.gpr q).sshiftRight 63)
  have e₂ : exec (.shift .sra .d q q 63) s₁ = some s₂ := exec_shift_d (by decide)
  have g0 : s₂.gpr .s0 = s.gpr .s0 := by
    simp only [s₂, s₁, RegUpd.gpr_write, Ne.symm h0, ite_false]
  let s₃ := s₂.write .a6 (s₂.mem.readW (s₂.gpr .s0 + BitVec.ofNat 64 (stOff w)) 64)
  have e₃ : exec (.load .d .a6 .s0 (stOff w)) s₂ = some s₃ :=
    exec_load_d (by unfold stOff; omega_using [hw]) (by rw [g0]; exact slot_al h hw) (by rw [g0]; exact slot_rd h hw)
  let s₄ := s₃.write q (s₃.gpr q ^^^ s₃.gpr .a6)
  have e₄ : exec (.logic .xor q q .a6) s₃ = some s₄ := exec_logic
  refine ⟨s₄, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, show key = .a5 from rfl, e₁, runStep_some, runBlock_cons, e₂, runStep_some,
      runBlock_cons, show base = .s0 from rfl, show tmp = .a6 from rfl, e₃, runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_nil]
  · have g0' : s₂.mem = s.mem := rfl
    simp only [s₄, s₃, RegUpd.gpr_write, ite_true, h6, ite_false, g0, g0']
    simp only [s₂, s₁, RegUpd.gpr_write, ite_true]
    rw [bit_mask _ (by omega_using [hb])]
    rfl
  · simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_write, h1, h2, ite_false]

/-- One input: key bit `b` of `a5` as a mask, XORed with state word `w`. -/
theorem inputStep_run {s : State} (h : Room s) {i : Nat} (hi : i < 6) {b w : Nat} (hb : b < 48)
    (hw : w < 64) :
    ∃ s', runBlock isa [.shift .sll .d (inReg i) key (63 - b), .shift .sra .d (inReg i) (inReg i) 63,
        .load .d tmp base (stOff w), .logic .xor (inReg i) (inReg i) tmp] s = some s' ∧
      s'.gpr (inReg i) = maskVal ((s.gpr .a5).getLsbD b) ^^^ sl s w ∧
      (∀ r, r ≠ inReg i → r ≠ .a6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨-, h6, h0, -⟩ := inReg_ne i hi
  exact inputStep_run' h h6 h0 hb hw

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j n := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s) :
    ∃ s', runBlock isa (inputsN ρ j n) s = some s' ∧
      (∀ m < n, s'.gpr (inReg m) = maskVal ((s.gpr .a5).getLsbD (inBit j m)) ^^^
        sl s (readWord ρ (eBit (inBit j m)))) ∧
      (∀ r, (∀ m < n, r ≠ inReg m) → r ≠ .a6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun m hm => by omega, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ih (by omega_using [hn])
    have g0 : s₁.gpr .s0 = s.gpr .s0 := o₁ _ (fun m hm => (inReg_ne m (by omega_using [hn, hm])).2.2.1.symm) (by decide)
    have g5 : s₁.gpr .a5 = s.gpr .a5 := o₁ _ (fun m hm => (inReg_ne m (by omega_using [hn, hm])).1.symm) (by decide)
    have h₁ : Room s₁ := h.congr g0 wr₁
    obtain ⟨s₂, run₂, q₂, o₂, m₂, rd₂, wr₂, sp₂⟩ :=
      inputStep_run h₁ (i := n) (by omega_using [hn]) (b := inBit j n) (w := readWord ρ (eBit (inBit j n)))
        (by unfold inBit; omega_using [hn]) (readWord_lt ρ j hj n (by omega_using [hn]))
    refine ⟨s₂, ?_, fun m hm => ?_, fun r hr h6 => ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · by_cases he : m = n
      · subst he
        rw [q₂, g5]
        simp only [sl, m₁, g0]
      · have hne : inReg m ≠ inReg n := by
          intro e; exact he (inReg_inj _ (by omega_using [hn, hm]) _ (by omega_using [hn]) e)
        rw [o₂ _ hne (inReg_ne m (by omega_using [hn, hm])).2.1, in₁ m (by omega_using [hm, he])]
    · rw [o₂ _ (hr n (by omega_using [])) h6, o₁ _ (fun m hm => hr m (by omega_using [hm])) h6]

/-! ## Outputs -/

/-- S-box `j`'s output registers. -/
def outRegs (j : Nat) : List Reg := (List.range 4).map (outReg j)

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 64) varsCfg (fun _ => none) (outputCode ρ j) (varEnv (outRegs j)) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

/-- What the outputs' code writes: `a6`. -/
theorem outputCode_dst : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => dst i == none || dst i == some .a6) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, sl s' k = match outIdx ρ j k with
        | some i => sl s k ^^^ s.gpr (outReg j i)
        | none => sl s k) ∧
      (∀ r, r ≠ .a6 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun (outRegs j) (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, fun r hr => p.other r ?_, p.rd, p.wr, p.sp, p.frame⟩
  · rw [varRel_slot p.rel hk (hpost k hk)]
    split
    · rename_i i hi
      have hi4 := outIdx_lt ρ j k i hi
      rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega_using [hk]) (by simp [varN, outRegs]; omega_using [hi4])]
      have e1 : ¬ 64 + i < 64 := by omega_using []
      simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outRegs]
      simp [List.getD_eq_getElem?_getD, hi4]
    · rw [xorSet_two_pow _ (by simp [varN]; omega_using [hk])]
      simp only [varVals, hk, ite_true]
  · have hd := List.all_eq_true.mp (outputCode_dst ρ j hj)
    have : (outputCode ρ j).all (fun i => dst i != some r) = true := List.all_eq_true.mpr fun i hi => by
      have := hd i hi
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with e | e <;> rw [e] <;> simp [Ne.symm hr]
    simp [this]

/-! ## One S-box -/

/-- The registers an S-box step leaves alone. -/
def stepKept : List Reg := [.s0, .a1, .a2, .a3, .a4, .a5, .s11, .ra]

theorem stepKept_in : ∀ r ∈ stepKept, r ∈ sboxKept ∧ r ≠ .a6 ∧ ∀ m < 6, r ≠ inReg m := by decide

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : ∀ b < 48, (s.gpr .a5).getLsbD b = k.getLsbD b) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, sp₂, m₂, o₂⟩ := sbox_ok j hj s₁
  have k₂ : ∀ r ∈ stepKept, s₂.gpr r = s.gpr r := fun r hr => by
    obtain ⟨hs, h6, hm⟩ := stepKept_in r hr
    rw [o₂ r hs, o₁ r hm h6]
  have g0 : s₂.gpr .s0 = s.gpr .s0 := k₂ _ (by decide)
  have h₂ : Room s₂ := h.congr g0 (wr₂.trans wr₁)
  obtain ⟨s₃, run₃, sl₃, o₃, rd₃, wr₃, sp₃, f₃⟩ := outputs_ok ρ hj h₂
  have sl₂ : ∀ x, sl s₂ x = sl s x := fun x => by simp only [sl, m₂, m₁, g0]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      maskVal (k.getLsbD (inBit j i)) ^^^ sl s (readWord ρ (eBit (inBit j i))) := by
    intro i hi
    rw [in₁ i hi, hkey _ (by unfold inBit; omega_using [hi])]
  refine ⟨s₃, ?_, fun x hx => ?_, fun r hr => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [sboxStep, inputCode_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · simp only [words]
    rw [sl₃ _ hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact sl₂ x
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [sl₂ x]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_mask _ hp]
      rw [Bool.xor_comm]
  · rw [o₃ r (stepKept_in r hr).2.1, k₂ r hr]
  · have : stR s₂ = stR s := by simp only [stR, g0]
    rw [this] at f₃
    rw [show s₂.mem = s.mem from m₂.trans m₁] at f₃
    exact f₃

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k == some (2 ^ swapSlot k)

theorem swap_check :
    check (vars 64) varsCfg (fun _ => none) swapHalves (varEnv []) swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by lit_decide

theorem swapHalves_dst : (swapHalves.all fun i => dst i == none || dst i == some .t0 ||
    dst i == some .t1) = true := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 64, sl s' k = sl s (swapSlot k) := by
    intro k hk
    rw [varRel_slot p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, fun r h0 h1 => p.other r ?_, p.rd, p.wr, p.sp, p.frame⟩
  · simp only [words]
    rw [key _ hx]
    simp only [swapW, swapSlot]
    rcases partner x with _ | y <;> rfl
  · have hd := List.all_eq_true.mp swapHalves_dst
    have : swapHalves.all (fun i => dst i != some r) = true := List.all_eq_true.mpr fun i hi => by
      have := hd i hi
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with (e | e) | e <;> rw [e] <;> simp [Ne.symm h0, Ne.symm h1]
    simp [this]

end VG.Proof.TripleDes.RISCV64.Bitsliced

end

end

/-!
# Bitsliced DES rounds and passes on RISC-V

`round_ok`: the code of a round loads the round key at the key pointer `a3`
into `a5`, steps the pointer by `δ d` (8 or −8) and does to the state words
what `roundW` does with the key's low 48 bits. `pass_ok`: a pass points
`a3` at its first key in the schedules' copy (`schedOff`), runs eight pairs
of rounds (counted down in `a4`) and exchanges the halves: what `passW`
does with the component schedule. `passes_ok`: the three passes do what
`tdeaW` does.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.RISCV64.Straight (wordAddr wordAddr_al)

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 64 := BitVec.ofInt 64 (if d = .encrypt then 8 else -8)

/-- The schedules' copy. -/
def schedA (s : State) : Addr := s.gpr .s0 + BitVec.ofNat 64 schedOff

/-- A round key's address: word `i < 48` of the schedules' copy. -/
def KeyAt (s : State) (A : Addr) : Prop := ∃ i < 48, A = schedA s + BitVec.ofNat 64 (8 * i)

theorem keyAt_addr {s : State} {A : Addr} (h : KeyAt s A) :
    ∃ i < 48, A = s.gpr .s0 + BitVec.ofNat 64 (schedOff + 8 * i) := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, Offset.add_add _ _ _⟩

theorem KeyAt.congr {s s' : State} {A : Addr} (h : KeyAt s A) (hb : s'.gpr .s0 = s.gpr .s0) : KeyAt s' A := by
  simp only [KeyAt, schedA, hb]; exact h

theorem keyAt_rd {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) :
    InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 0) 8 := by
  obtain ⟨i, hi, rfl⟩ := keyAt_addr hk
  rw [BitVec.add_zero]
  have := slot_in h (k := 64 + i) (by omega_using [hi])
  simp only [wordAddr, schedOff] at this ⊢
  rw [show 512 + 8 * i = 8 * (64 + i) by omega_using []]
  let ⟨r, hr, hc⟩ := this; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem keyAt_al {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) :
    (A + BitVec.ofNat 64 0).toNat % 8 = 0 := by
  obtain ⟨i, hi, rfl⟩ := keyAt_addr hk
  rw [BitVec.add_zero, show schedOff + 8 * i = 8 * (64 + i) by unfold schedOff; omega_using []]
  exact wordAddr_al h.al _ (by omega_using [hi])

/-- Round keys are apart from the state words. -/
theorem keyAt_apart {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) :
    (⟨A, 8⟩ : Region).Disjoint (stR s) := by
  obtain ⟨i, hi, rfl⟩ := keyAt_addr hk
  have := h.fit
  exact Offset.disjoint_base _ (by unfold schedOff; omega_using []) (by unfold schedOff frameBytes at *; omega_using [hi])

theorem stR_congr {s s' : State} (hb : s'.gpr .s0 = s.gpr .s0) : stR s' = stR s := by
  simp only [stR, hb]

/-! ## A round -/

theorem keyLoad_ok (d : Direction) {s : State} (h : Room s) {A : Addr} (hA : s.gpr .a3 = A)
    (hk : KeyAt s A) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧ s'.gpr .a5 = s.mem.readW A 64 ∧
      s'.gpr .a3 = A + δ d ∧ (∀ r, r ≠ .a5 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e₁ := exec_load_d (s := s) (t := .a5) (n := .a3) (off := 0) (by decide)
    (by rw [hA]; exact keyAt_al h hk) (by rw [hA]; exact keyAt_rd h hk)
  let s₁ := s.write .a5 (s.mem.readW (s.gpr .a3 + BitVec.ofNat 64 0) 64)
  have e₂ := exec_addi (s := s₁) (d := .a3) (n := .a3) (imm := if d = .encrypt then 8 else -8)
    (by cases d <;> decide)
  let s₂ := s₁.write .a3 (s₁.gpr .a3 + BitVec.ofInt 64 (if d = .encrypt then 8 else -8))
  have g3 : s₁.gpr .a3 = s.gpr .a3 := by simp [s₁, RegUpd.gpr_write]
  refine ⟨s₂, ?_, ?_, ?_, fun r h5 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [keyLoad, runBlock_cons, show key = .a5 from rfl, show keyPtr = .a3 from rfl, e₁, runStep_some,
      runBlock_cons, e₂, runStep_some, runBlock_nil]
  · simp [s₂, s₁, RegUpd.gpr_write, hA]
  · simp only [s₂, RegUpd.gpr_write, ite_true, g3, hA, δ]
  · simp [s₂, s₁, RegUpd.gpr_write, h5, h3]

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : ∀ b < 48, (s.gpr .a5).getLsbD b = k.getLsbD b) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega_using [hn])
    have g0 : s₁.gpr .s0 = s.gpr .s0 := k₁ _ (by decide)
    have g5 : s₁.gpr .a5 = s.gpr .a5 := k₁ _ (by decide)
    obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, f₂⟩ :=
      sboxStep_ok ρ (j := n) (by omega_using [hn]) (h.congr g0 wr₁) k (by rw [g5]; exact hkey)
    refine ⟨s₂, ?_, fun x hx => ?_, fun r hr => by rw [k₂ r hr, k₁ r hr], rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega_using [hn]) w₁ (w₁ x hx)
    · rw [stR_congr g0] at f₂; exact f₁.trans f₂

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

/-- The registers a round leaves alone. -/
def roundKept : List Reg := [.s0, .a1, .a2, .a4, .s11, .ra]

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) {A : Addr} (hA : s.gpr .a3 = A)
    (hk : KeyAt s A) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW A 64).setWidth 48) (words s) x) ∧
      s'.gpr .a3 = A + δ d ∧ (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, p₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := keyLoad_ok d h hA hk
  have g0 : s₁.gpr .s0 = s.gpr .s0 := o₁ _ (by decide) (by decide)
  obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, f₂⟩ :=
    stepsCode_ok ρ ((s.mem.readW A 64).setWidth 48) (Nat.le_refl 8) (h.congr g0 wr₁)
      (fun b hb => by rw [k₁, BitVec.getLsbD_setWidth]; simp [hb])
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r hr => ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8)
      (fun y _ => by simp only [words, sl, m₁, g0]) x hx
  · rw [k₂ _ (by decide), p₁]
  · have hs : r ∈ stepKept ∧ r ≠ .a5 ∧ r ≠ .a3 :=
      (by decide : ∀ r ∈ roundKept, r ∈ stepKept ∧ r ≠ .a5 ∧ r ≠ .a3) r hr
    rw [k₂ r hs.1, o₁ r hs.2.1 hs.2.2]
  · rw [stR_congr g0, m₁] at f₂; exact f₂

/-! ## Pairs of rounds -/

theorem roundPair_eq (d : Direction) :
    roundPair d = round d .ba ++ (round d .ab ++ ([.addi pairs pairs (-1)] : List Instr)) := by
  simp only [roundPair, List.append_assoc]

theorem Frame.readKey {s : State} (h : Room s) {A : Addr} (hk : KeyAt s A) {m : Mem}
    (hf : Frame [stR s] s.mem m) : m.readW A 64 = s.mem.readW A 64 :=
  hf.readW (Region.contains_self A 8) (by simpa using keyAt_apart h hk) (by decide)

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) {A : Addr} (hA : s.gpr .a3 = A)
    (hk₁ : KeyAt s A) (hk₂ : KeyAt s (A + δ d)) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (A + δ d) 64).setWidth 48)
        (roundW .ba ((s.mem.readW A 64).setWidth 48) (words s)) x) ∧
      s'.gpr .a3 = A + δ d + δ d ∧ s'.gpr .a4 = s.gpr .a4 + BitVec.ofInt 64 (-1) ∧
      (∀ r ∈ [Reg.s0, .a1, .a2, .s11, .ra], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, p₁, k₁, rd₁, wr₁, sp₁, f₁⟩ := round_ok d .ba h hA hk₁
  have g0 : s₁.gpr .s0 = s.gpr .s0 := k₁ _ (by decide)
  have h₁ := h.congr g0 wr₁
  obtain ⟨s₂, run₂, w₂, p₂, k₂, rd₂, wr₂, sp₂, f₂⟩ := round_ok d .ab h₁ p₁ (hk₂.congr g0)
  have e₃ := exec_addi (s := s₂) (d := .a4) (n := .a4) (imm := -1) (by decide)
  have g4 : s₂.gpr .a4 = s.gpr .a4 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  refine ⟨s₂.write .a4 (s₂.gpr .a4 + BitVec.ofInt 64 (-1)), ?_, fun x hx => ?_, ?_, ?_, fun r hr => ?_,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [roundPair_eq]
    refine runBlock_cat_some run₁ (runBlock_cat_some run₂ ?_)
    rw [runBlock_cons, show Impl.TripleDes.RISCV64.Bitslice.pairs = Reg.a4 from rfl, e₃, runStep_some, runBlock_nil]
  · have : words (s₂.write .a4 (s₂.gpr .a4 + BitVec.ofInt 64 (-1))) x = words s₂ x := by
      simp only [words, sl, RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [this, w₂ x hx]
    rw [Frame.readKey h hk₂ f₁]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, p₂]
  · simp only [RegUpd.gpr_write, ite_true, g4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_write, reduceCtorEq, ite_false] <;>
      rw [k₂ _ (by decide), k₁ _ (by decide)]
  · simp only [RegUpd.mem_write]
    rw [stR_congr g0] at f₂; exact f₁.trans f₂

/-! ## A pass -/

/-- The offset in the schedules' copy of a pass's first key. -/
def kOff (c : Nat) (d : Direction) : Nat := 128 * c + if d = .encrypt then 0 else 120

/-- The word of the component that is round `r`'s key. -/
def ix (d : Direction) (r : Nat) : Nat := if d = .encrypt then r else 15 - r

theorem kaddr : ∀ c < 3, ∀ d : Direction, ∀ r < 16,
    BitVec.ofNat 64 (kOff c d) + BitVec.ofNat 64 r * δ d = BitVec.ofNat 64 (8 * (16 * c + ix d r)) := by
  intro c hc d r hr
  cases d
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 64 (kOff c .encrypt) + BitVec.ofNat 64 r * δ .encrypt =
      BitVec.ofNat 64 (8 * (16 * c + ix .encrypt r))) c hc r hr
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 64 (kOff c .decrypt) + BitVec.ofNat 64 r * δ .decrypt =
      BitVec.ofNat 64 (8 * (16 * c + ix .decrypt r))) c hc r hr

theorem kptr_succ (a₀ δ : Addr) (r : Nat) :
    a₀ + BitVec.ofNat 64 r * δ + δ = a₀ + BitVec.ofNat 64 (r + 1) * δ := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul]
  exact congrArg (fun t => a₀ + (BitVec.ofNat 64 r * δ + t)) (BitVec.one_mul δ).symm

/-- The keys of a pass: the low 48 bits of the words at `P + r δ`. -/
def keyOf (m : Mem) (P δ : Addr) (r : Nat) : BitVec 48 :=
  (m.readW (P + BitVec.ofNat 64 r * δ) 64).setWidth 48

/-- The pass's first key's address. -/
def passP (s : State) (c : Nat) (d : Direction) : Addr := schedA s + BitVec.ofNat 64 (kOff c d)

theorem passKeyAt {s : State} {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    KeyAt s (passP s c d + BitVec.ofNat 64 r * δ d) := by
  refine ⟨16 * c + ix d r, by unfold ix; split <;> omega_arith, ?_⟩
  rw [passP, BitVec.add_assoc, kaddr c hc d r hr]

theorem keyOf_pass (m : Mem) (s : State) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    keyOf m (passP s c d) (δ d) r = roundKey (componentSchedule (scheduleAt m (schedA s)) c) d r := by
  have hi : ix d r < 16 := by unfold ix; split <;> omega_arith
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl, componentSchedule_readW m _ _ _ hc hi, keyOf, passP, BitVec.add_assoc, kaddr c hc d r hr]


/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (c : Nat) (d : Direction) (m : Nat) (s : State) : Prop where
  le : m ≤ 8
  s0 : s.gpr .s0 = s₀.gpr .s0
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = s₀.gpr .a2
  s11 : s.gpr .s11 = s₀.gpr .s11
  ra : s.gpr .ra = s₀.gpr .ra
  ptr : s.gpr .a3 = passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d
  cnt : s.gpr .a4 = BitVec.ofNat 64 (8 - m)
  wds : ∀ x < 64, words s x = VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP s₀ c d) (δ d)) m (words s₀) x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀] s₀.mem s.mem

theorem pair_step {s₀ : State} (h₀ : Room s₀) {c : Nat} (hc : c < 3) {d : Direction} {m : Nat} (hm : m < 8)
    {s : State} (I : PairInv s₀ c d m s) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧ PairInv s₀ c d (m + 1) s' := by
  have h : Room s := h₀.congr I.s0 I.wr
  have hk₁ := (passKeyAt (s := s₀) hc d (r := 2 * m) (by omega_using [hm])).congr I.s0
  have hk₂ := (passKeyAt (s := s₀) hc d (r := 2 * m + 1) (by omega_using [hm])).congr I.s0
  rw [← kptr_succ] at hk₂
  obtain ⟨s', run, w, p3, p4, k, rd, wr, sp, f⟩ := roundPair_ok d h I.ptr hk₁ hk₂
  have rk : ∀ r < 16, s.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 =
      s₀.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 := fun r hr => by
    have := Frame.readKey h₀ (passKeyAt (s := s₀) hc d hr) I.frame
    exact this
  refine ⟨s', run, ⟨by omega_using [hm], (k _ (by decide)).trans I.s0, (k _ (by decide)).trans I.a1,
    (k _ (by decide)).trans I.a2, (k _ (by decide)).trans I.s11, (k _ (by decide)).trans I.ra, ?_, ?_,
    fun x hx => ?_, rd.trans I.rd, wr.trans I.wr, sp.trans I.sp, ?_⟩⟩
  · rw [p3, kptr_succ, kptr_succ]; congr 3
  · rw [p4, I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 64 (8 - m) + BitVec.ofInt 64 (-1) =
      BitVec.ofNat 64 (8 - (m + 1))) m hm
  · have e : passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d + δ d =
        passP s₀ c d + BitVec.ofNat 64 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega_using [hm]), rk _ (by omega_using [hm])]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · have := I.frame.trans (by rw [← stR_congr I.s0]; exact f)
    exact this

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) {c : Nat} (hc : c < 3) (d : Direction) {s : State}
    (I : PairInv s₀ c d 0 s) :
    WP isa (.loop (.block (roundPair d)) (.nonzero pairs)) s (PairInv s₀ c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  obtain ⟨v', run, J'⟩ := pair_step h₀ hc hm J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show Impl.TripleDes.RISCV64.Bitslice.pairs = Reg.a4 from rfl, Steps.eval_nonzero_ofNat _ _ (by omega_using []) J'.cnt]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right; exact ⟨by simp; omega_using [hm, e], 8 - (m + 1), by omega_using [hm, hn], m + 1, by omega_using [hm, e], rfl, J'⟩

/-- The registers a pass leaves alone. -/
def passKept : List Reg := [.s0, .a1, .a2, .s11, .ra]

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x = passW (componentSchedule (scheduleAt s.mem (schedA s)) c) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  unfold pass
  apply WP.seq
  have e₁ := exec_addi (s := s) (d := .a3) (n := .s0)
    (imm := ((schedOff : Int) + 128 * (c : Int) + if d = .encrypt then 0 else 120))
    (by cases d <;> (simp only [imm12, schedOff, reduceCtorEq, ite_true, ite_false]; omega_using [hc]))
  let s₁ := s.write .a3 (s.gpr .s0 +
    BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) + if d = .encrypt then 0 else 120))
  have e₂ := exec_li (s := s₁) (d := .a4) (imm := 8) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, show keyPtr = .a3 from rfl, show base = .s0 from rfl, e₁, runStep_some,
      runBlock_cons, show Impl.TripleDes.RISCV64.Bitslice.pairs = Reg.a4 from rfl, e₂, runStep_some, runBlock_nil], ?_⟩
  have hI : BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) + if d = .encrypt then 0 else 120) =
      BitVec.ofNat 64 schedOff + BitVec.ofNat 64 (kOff c d) := by
    cases d
    · exact (by decide : ∀ c : Nat, c < 3 → BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) +
        if Direction.encrypt = .encrypt then 0 else 120) =
        BitVec.ofNat 64 schedOff + BitVec.ofNat 64 (kOff c .encrypt)) c hc
    · exact (by decide : ∀ c : Nat, c < 3 → BitVec.ofInt 64 ((schedOff : Int) + 128 * (c : Int) +
        if Direction.decrypt = .encrypt then 0 else 120) =
        BitVec.ofNat 64 schedOff + BitVec.ofNat 64 (kOff c .decrypt)) c hc
  have z : BitVec.ofNat 64 (2 * 0) * δ d = 0#64 := by cases d <;> decide
  have I0 : PairInv s c d 0 (s₁.write .a4 (BitVec.ofInt 64 8)) := by
    refine ⟨by decide, by simp [s₁, RegUpd.gpr_write], by simp [s₁, RegUpd.gpr_write],
      by simp [s₁, RegUpd.gpr_write], by simp [s₁, RegUpd.gpr_write], by simp [s₁, RegUpd.gpr_write], ?_,
      by simp [RegUpd.gpr_write], fun x hx => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
    simp only [s₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, passP, schedA, z]
    rw [hI, BitVec.add_zero]
    exact (BitVec.add_assoc _ _ _).symm
  apply WP.seq
  refine WP.mono (pairLoop_ok h hc d I0) fun v J => ?_
  have hv : Room v := h.congr J.s0 J.wr
  obtain ⟨v', run, w, k, rd, wr, sp, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, fun r hr => ?_, rd.trans J.rd, wr.trans J.wr,
    sp.trans J.sp, ?_⟩
  · rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
    refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
    rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8 (fun r hr => keyOf_pass _ _ hc d hr)]
  · simp only [passKept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [k _ (by decide) (by decide), J.s0]
    · rw [k _ (by decide) (by decide), J.a1]
    · rw [k _ (by decide) (by decide), J.a2]
    · rw [k _ (by decide) (by decide), J.s11]
    · rw [k _ (by decide) (by decide), J.ra]
  · rw [stR_congr J.s0] at f; exact J.frame.trans f

/-! ## The three passes -/

theorem passes_ok (d : Direction) {s : State} (h : Room s) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (schedA s)) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  have step : ∀ (c : Nat) (hc : c < 3) (d' : Direction) {u : State}, Room u → schedA u = schedA s →
      scheduleAt u.mem (schedA s) = scheduleAt s.mem (schedA s) → u.gpr .s0 = s.gpr .s0 →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (schedA s)) c) d' (words u) x) → (∀ r ∈ passKept, u'.gpr r = u.gpr r) →
        u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → Frame [stR u] u.mem u'.mem → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u hu hA hK _ Q hQ
    refine WP.mono (pass_ok c hc d' hu) fun u' ⟨w, k, rd, wr, sp, f⟩ => hQ u' ?_ k rd wr sp f
    rw [hA, hK] at w; exact w
  have hK : ∀ {u : State}, u.gpr .s0 = s.gpr .s0 → Frame [stR s] s.mem u.mem →
      scheduleAt u.mem (schedA s) = scheduleAt s.mem (schedA s) := fun hb hf =>
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := h.fit
      exact Offset.disjoint_base _ (by unfold schedOff; omega_using []) (by unfold schedOff frameBytes at *; omega_using [])
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ h rfl rfl rfl fun u₁ w₁ k₁ rd₁ wr₁ sp₁ f₁ => ?_
    have g₁ : u₁.gpr .s0 = s.gpr .s0 := k₁ _ (by decide)
    have h₁ : Room u₁ := h.congr g₁ wr₁
    apply WP.seq
    refine step _ (by decide) _ h₁ (by simp only [schedA, g₁]) (hK g₁ f₁) g₁
      fun u₂ w₂ k₂ rd₂ wr₂ sp₂ f₂ => ?_
    have g₂ : u₂.gpr .s0 = s.gpr .s0 := (k₂ _ (by decide)).trans g₁
    have h₂ : Room u₂ := h.congr g₂ (wr₂.trans wr₁)
    have f₁₂ : Frame [stR s] s.mem u₂.mem := f₁.trans (by rw [← stR_congr g₁]; exact f₂)
    refine step _ (by decide) _ h₂ (by simp only [schedA, g₂]) (hK g₂ f₁₂) g₂
      fun u₃ w₃ k₃ rd₃ wr₃ sp₃ f₃ => ⟨fun x hx => ?_, fun r hr => by rw [k₃ r hr, k₂ r hr, k₁ r hr],
        rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
        f₁₂.trans (by rw [← stR_congr g₂]; exact f₃)⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.RISCV64.Bitsliced
