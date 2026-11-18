module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-! ### `TripleDes.PPC64LE.Bitsliced.Step`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Bitsliced.Sbox`, which only this module used -/

section

/-!
# The bitsliced S-box circuits' machine code on PPC64LE

Untrusted. The kernel checks each allocated circuit on all 64 inputs, and
the truth-table evaluator lifts that check to every bit position of
arbitrary 64-bit words (`TabAll`, a relation at every position at once),
as on RISC-V (`Proof/TripleDes/RISCV64/Bitsliced/Pass.lean`). The register
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

end

end

/-!
# One S-box of a bitsliced round on PPC64LE, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the key's bits `inBit j i`
as masks XORed with the words of `E`, from the complemented key in `r9`;
its circuit; XORing its outputs into their words) does to the state words
what `step` does. `swapHalves_ok`: the exchange of the halves does what
`swapW` does. As on RISC-V (`Proof/TripleDes/RISCV64/Bitsliced/Pass.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.Straight VG.PPC64LE.RegUpd VG.Bitslice VG.Impl.TripleDes.PPC64LE.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Interleave.runBlock_append, h₁, Option.bind_some, h₂]

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- Bit `c` of `q`, shifted to the top and back to the bottom. -/
theorem bit_bottom (q : BitVec 64) {c : Nat} (hc : c < 64) :
    q <<< (63 - c) >>> 63 = if q.getLsbD c then 1#64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp only [show (63 + 0 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 + 0 < 63 - c) by omega_using [], decide_false, Bool.not_false, show 63 + 0 - (63 - c) = c by omega_using [hc]]
    cases q.getLsbD c <;> rfl
  · simp only [show ¬ (63 + i < 64) by omega_using [hpos], decide_false, Bool.false_and]
    cases q.getLsbD c <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega_using [hpos]]

/-- The complemented key's bit `c`, at the bottom, minus one: key bit `c` as a mask. -/
theorem bit_mask (k : BitVec 64) {c : Nat} (hc : c < 64) :
    (~~~k) <<< (63 - c) >>> 63 - BitVec.ofNat 64 1 = maskVal (k.getLsbD c) := by
  rw [bit_bottom _ hc]
  simp only [BitVec.getLsbD_not, hc, decide_true, Bool.true_and]
  cases k.getLsbD c <;> rfl

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 64) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .r9 ∧ inReg i ≠ .r0 ∧ inReg i ≠ .r10 ∧ inReg i ≠ .r4 ∧
    inReg i ≠ .r8 ∧ inReg i ≠ .r3 ∧ inReg i ≠ .r5 ∧ inReg i ≠ .r7 ∧ inReg i ≠ .r11 := by decide

theorem inReg_inj : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

theorem slot_rd {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (stOff w)) 8 :=
  let ⟨r, hr, hc⟩ := slot_in h (k := w) (by omega_using [hw]); ⟨r, List.mem_append_right _ hr, hc⟩

/-- One input into `q`: key bit `b` of `~~~r9` as a mask, XORed with state word `w`. -/
theorem inputStep_run' {s : State} (h : Room s) {q : Reg} (h0 : q ≠ .r0) (h10 : q ≠ .r10)
    {b w : Nat} (hb : b < 48) (hw : w < 64) :
    ∃ s', runBlock isa [.lsl q key (63 - b), .lsr .d q q 63, .subi q q 1,
        .load .d tmp base (stOff w), .logic .xor q q tmp] s = some s' ∧
      s'.gpr q = maskVal ((~~~(s.gpr .r9)).getLsbD b) ^^^ sl s w ∧
      (∀ r, r ≠ q → r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  let s₁ := s.write q (s.gpr .r9 <<< (63 - b))
  have e₁ : exec (.lsl q .r9 (63 - b)) s = some s₁ := exec_lsl (by omega_using [])
  let s₂ := s₁.write q (s₁.gpr q >>> 63)
  have e₂ : exec (.lsr .d q q 63) s₁ = some s₂ := exec_lsr_d (by decide)
  let s₃ := s₂.write q (s₂.gpr q - BitVec.ofNat 64 1)
  have e₃ : exec (.subi q q 1) s₂ = some s₃ := exec_subi h0 (by decide)
  have g10 : s₃.gpr .r10 = s.gpr .r10 := by
    simp only [s₃, s₂, s₁, gpr_write, Ne.symm h10, ite_false]
  let s₄ := s₃.write .r0 (s₃.mem.readW (s₃.gpr .r10 + BitVec.ofNat 64 (stOff w)) 64)
  have e₄ : exec (.load .d .r0 .r10 (stOff w)) s₃ = some s₄ :=
    exec_load_d (by decide) ⟨by unfold stOff; omega_using [hw], by unfold stOff; omega_using []⟩
      (by rw [g10]; exact slot_rd h hw)
  let s₅ := s₄.write q (s₄.gpr q ^^^ s₄.gpr .r0)
  have e₅ : exec (.logic .xor q q .r0) s₄ = some s₅ := exec_logic
  refine ⟨s₅, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, show key = .r9 from rfl, e₁, runStep_some, runBlock_cons, e₂, runStep_some,
      runBlock_cons, e₃, runStep_some, runBlock_cons, show base = .r10 from rfl, show tmp = .r0 from rfl,
      e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · have g' : s₃.mem = s.mem := rfl
    simp only [s₅, s₄, gpr_write, ite_true, h0, ite_false, g10, g']
    simp only [s₃, s₂, s₁, gpr_write, ite_true]
    rw [← bit_mask (~~~(s.gpr .r9)) (by omega_using [hb] : b < 64), BitVec.not_not]
    rfl
  · simp only [s₅, s₄, s₃, s₂, s₁, gpr_write, h1, h2, ite_false]

/-- One input: key bit `b` of `~~~r9` as a mask, XORed with state word `w`. -/
theorem inputStep_run {s : State} (h : Room s) {i : Nat} (hi : i < 6) {b w : Nat} (hb : b < 48)
    (hw : w < 64) :
    ∃ s', runBlock isa [.lsl (inReg i) key (63 - b), .lsr .d (inReg i) (inReg i) 63,
        .subi (inReg i) (inReg i) 1, .load .d tmp base (stOff w), .logic .xor (inReg i) (inReg i) tmp] s
        = some s' ∧
      s'.gpr (inReg i) = maskVal ((~~~(s.gpr .r9)).getLsbD b) ^^^ sl s w ∧
      (∀ r, r ≠ inReg i → r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  obtain ⟨-, h0, h10, -⟩ := inReg_ne i hi
  exact inputStep_run' h h0 h10 hb hw

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
      (∀ m < n, s'.gpr (inReg m) = maskVal ((~~~(s.gpr .r9)).getLsbD (inBit j m)) ^^^
        sl s (readWord ρ (eBit (inBit j m)))) ∧
      (∀ r, (∀ m < n, r ≠ inReg m) → r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun m hm => by omega, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁, lr₁⟩ := ih (by omega_using [hn])
    have g0 : s₁.gpr .r10 = s.gpr .r10 :=
      o₁ _ (fun m hm => (inReg_ne m (by omega_using [hn, hm])).2.2.1.symm) (by decide)
    have g9 : s₁.gpr .r9 = s.gpr .r9 := o₁ _ (fun m hm => (inReg_ne m (by omega_using [hn, hm])).1.symm) (by decide)
    have h₁ : Room s₁ := h.congr g0 wr₁
    obtain ⟨s₂, run₂, q₂, o₂, m₂, rd₂, wr₂, sp₂, lr₂⟩ :=
      inputStep_run h₁ (i := n) (by omega_using [hn]) (b := inBit j n) (w := readWord ρ (eBit (inBit j n)))
        (by unfold inBit; omega_using [hn]) (readWord_lt ρ j hj n (by omega_using [hn]))
    refine ⟨s₂, ?_, fun m hm => ?_, fun r hr h6 => ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, lr₂.trans lr₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · by_cases he : m = n
      · subst he
        rw [q₂, g9]
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

/-- What the outputs' code writes: `r0`. -/
theorem outputCode_dst : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => dst i == none || dst i == some .r0) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, sl s' k = match outIdx ρ j k with
        | some i => sl s k ^^^ s.gpr (outReg j i)
        | none => sl s k) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun (outRegs j) (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, fun r hr => p.other r ?_, p.rd, p.wr, p.sp, p.lr, p.frame⟩
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
def stepKept : List Reg := [.r10, .r4, .r8, .r3, .r5, .r9, .r7, .r11]

theorem stepKept_in : ∀ r ∈ stepKept, r ∈ sboxKept ∧ r ≠ .r0 ∧ ∀ m < 6, r ≠ inReg m := by decide

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : ∀ b < 48, (~~~(s.gpr .r9)).getLsbD b = k.getLsbD b)
    (hones : s.gpr .r11 = BitVec.allOnes 64) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁, lr₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h
  have o11 : s₁.gpr .r11 = BitVec.allOnes 64 := by
    rw [o₁ _ (fun m hm => (inReg_ne m (by omega_using [hm])).2.2.2.2.2.2.2.2.symm) (by decide), hones]
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, sp₂, lr₂, m₂, o₂⟩ := sbox_ok j hj s₁ o11
  have k₂ : ∀ r ∈ stepKept, s₂.gpr r = s.gpr r := fun r hr => by
    obtain ⟨hs, h6, hm⟩ := stepKept_in r hr
    rw [o₂ r hs, o₁ r hm h6]
  have g0 : s₂.gpr .r10 = s.gpr .r10 := k₂ _ (by decide)
  have h₂ : Room s₂ := h.congr g0 (wr₂.trans wr₁)
  obtain ⟨s₃, run₃, sl₃, o₃, rd₃, wr₃, sp₃, lr₃, f₃⟩ := outputs_ok ρ hj h₂
  have sl₂ : ∀ x, sl s₂ x = sl s x := fun x => by simp only [sl, m₂, m₁, g0]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      maskVal (k.getLsbD (inBit j i)) ^^^ sl s (readWord ρ (eBit (inBit j i))) := by
    intro i hi
    rw [in₁ i hi, hkey _ (by unfold inBit; omega_using [hi])]
  refine ⟨s₃, ?_, fun x hx => ?_, fun r hr => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), lr₃.trans (lr₂.trans lr₁), ?_⟩
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

theorem swapHalves_dst : (swapHalves.all fun i => dst i == none || dst i == some .r12 ||
    dst i == some .r14) = true := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      (∀ r, r ≠ .r12 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 64, sl s' k = sl s (swapSlot k) := by
    intro k hk
    rw [varRel_slot p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, fun r h0 h1 => p.other r ?_, p.rd, p.wr, p.sp, p.lr, p.frame⟩
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

end VG.Proof.TripleDes.PPC64LE.Bitsliced

end

end

/-!
# Bitsliced DES rounds and passes on PPC64LE

`round_ok`: the code of a round loads the round key at the key pointer `r3`
into `r9`, complements it, steps the pointer by `δ d` (8 or −8) and does to
the state words what `roundW` does with the key's low 48 bits. `pass_ok`: a
pass points `r3` at its first key in the schedule (`r7`), runs eight pairs
of rounds (counted down in `r5`) and exchanges the halves: what `passW`
does with the component schedule. `passes_ok`: the three passes do what
`tdeaW` does. As on RISC-V (`Proof/TripleDes/RISCV64/Bitsliced/Pass.lean`),
but for the schedule, which the code reads where the caller keeps it.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Bitslice VG.Impl.TripleDes.PPC64LE.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.PPC64LE.Straight (wordAddr)

/-- The schedule at `r7`: readable, and apart from the scratch buffer. -/
structure Sched (s : State) : Prop where
  rd : InRegions (s.rd ++ s.wr) (s.gpr .r7) 384
  sep : (⟨s.gpr .r7, 384⟩ : Region).Disjoint (frameR s)

theorem Sched.congr {s s' : State} (h : Sched s) (h7 : s'.gpr .r7 = s.gpr .r7)
    (h10 : s'.gpr .r10 = s.gpr .r10) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Sched s' where
  rd := by rw [h7, hrd, hwr]; exact h.rd
  sep := by simp only [frameR, h7, h10]; exact h.sep

/-- The ones register holds all ones. -/
def Ones (s : State) : Prop := s.gpr .r11 = BitVec.allOnes 64

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 64 := BitVec.ofInt 64 (if d = .encrypt then 8 else -8)

/-- A round key's address: word `i < 48` of the schedule. -/
def KeyAt (s : State) (A : Addr) : Prop := ∃ i < 48, A = s.gpr .r7 + BitVec.ofNat 64 (8 * i)

theorem KeyAt.congr {s s' : State} {A : Addr} (h : KeyAt s A) (hb : s'.gpr .r7 = s.gpr .r7) :
    KeyAt s' A := by
  simp only [KeyAt, hb]; exact h

theorem keyAt_rd {s : State} (h : Sched s) {A : Addr} (hk : KeyAt s A) :
    InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 0) 8 := by
  obtain ⟨i, hi, rfl⟩ := hk
  rw [BitVec.add_zero]
  exact covers_of_in h.rd _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

/-- Round keys are apart from the state words. -/
theorem keyAt_apart {s : State} (h : Sched s) {A : Addr} (hk : KeyAt s A) :
    (⟨A, 8⟩ : Region).Disjoint (stR s) := by
  obtain ⟨i, hi, rfl⟩ := hk
  exact (h.sep.sub_left (Offset.sub_base _ (by omega_using [hi]))).sub_right (Region.sub_prefix (by omega_using []))

theorem stR_congr {s s' : State} (hb : s'.gpr .r10 = s.gpr .r10) : stR s' = stR s := by
  simp only [stR, hb]

/-! ## A round -/

theorem δ_encrypt : δ .encrypt = BitVec.ofNat 64 8 := by decide

theorem δ_decrypt : δ .decrypt = -BitVec.ofNat 64 8 := by decide

theorem keyStep (d : Direction) (s : State) :
    runBlock isa [if d = .encrypt then Instr.addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8] s =
      some (s.write .r3 (s.gpr .r3 + δ d)) := by
  cases d
  · rw [ite_eq_left (rfl : Direction.encrypt = .encrypt), runBlock_cons, show keyPtr = .r3 from rfl,
      exec_addi (by decide) (by decide), runStep_some, runBlock_nil, δ_encrypt]
  · rw [ite_eq_right (by decide : ¬ Direction.decrypt = .encrypt), runBlock_cons, show keyPtr = .r3 from rfl,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil, δ_decrypt, BitVec.sub_eq_add_neg]

theorem keyLoad_ok (d : Direction) {s : State} (h : Sched s) {A : Addr} (hA : s.gpr .r3 = A)
    (hk : KeyAt s A) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧ s'.gpr .r9 = s.mem.readW A 64 ^^^ s.gpr .r11 ∧
      s'.gpr .r3 = A + δ d ∧ (∀ r, r ≠ .r9 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  have e₁ := exec_load_d (s := s) (t := .r9) (n := .r3) (off := 0) (by decide) (by decide)
    (by rw [hA]; exact keyAt_rd h hk)
  let s₁ := s.write .r9 (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 0) 64)
  let s₂ := s₁.write .r9 (s₁.gpr .r9 ^^^ s₁.gpr .r11)
  have e₂ : exec (.logic .xor .r9 .r9 .r11) s₁ = some s₂ := exec_logic
  refine ⟨s₂.write .r3 (s₂.gpr .r3 + δ d), ?_, ?_, ?_, fun r h9 h3 => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [keyLoad, show key = .r9 from rfl, show ones = .r11 from rfl, show [Instr.load .d .r9 keyPtr 0,
      .logic .xor .r9 .r9 .r11, if d = .encrypt then .addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8] =
      [Instr.load .d .r9 .r3 0, .logic .xor .r9 .r9 .r11] ++
        [if d = .encrypt then .addi keyPtr keyPtr 8 else .subi keyPtr keyPtr 8] from rfl]
    refine runBlock_cat_some ?_ (keyStep d s₂)
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil]
  · simp [s₂, s₁, gpr_write, hA]
  · simp [s₂, s₁, gpr_write, hA]
  · simp [s₂, s₁, gpr_write, h9, h3]

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : ∀ b < 48, (~~~(s.gpr .r9)).getLsbD b = k.getLsbD b) (hones : Ones s) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, k₁, rd₁, wr₁, sp₁, lr₁, f₁⟩ := ih (by omega_using [hn])
    have g0 : s₁.gpr .r10 = s.gpr .r10 := k₁ _ (by decide)
    have g9 : s₁.gpr .r9 = s.gpr .r9 := k₁ _ (by decide)
    have g11 : s₁.gpr .r11 = s.gpr .r11 := k₁ _ (by decide)
    obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, lr₂, f₂⟩ :=
      sboxStep_ok ρ (j := n) (by omega_using [hn]) (h.congr g0 wr₁) k (by rw [g9]; exact hkey)
        (by rw [g11]; exact hones)
    refine ⟨s₂, ?_, fun x hx => ?_, fun r hr => by rw [k₂ r hr, k₁ r hr], rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁, lr₂.trans lr₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega_using [hn]) w₁ (w₁ x hx)
    · rw [stR_congr g0] at f₂; exact f₁.trans f₂

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

/-- The registers a round leaves alone. -/
def roundKept : List Reg := [.r10, .r4, .r8, .r5, .r7, .r11]

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) (hs : Sched s) (hones : Ones s)
    {A : Addr} (hA : s.gpr .r3 = A) (hk : KeyAt s A) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ ((s.mem.readW A 64).setWidth 48) (words s) x) ∧
      s'.gpr .r3 = A + δ d ∧ (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, p₁, o₁, m₁, rd₁, wr₁, sp₁, lr₁⟩ := keyLoad_ok d hs hA hk
  have g0 : s₁.gpr .r10 = s.gpr .r10 := o₁ _ (by decide) (by decide)
  have g11 : s₁.gpr .r11 = s.gpr .r11 := o₁ _ (by decide) (by decide)
  obtain ⟨s₂, run₂, w₂, k₂, rd₂, wr₂, sp₂, lr₂, f₂⟩ :=
    stepsCode_ok ρ ((s.mem.readW A 64).setWidth 48) (Nat.le_refl 8) (h.congr g0 wr₁)
      (fun b hb => by
        rw [k₁, show s.gpr .r11 = BitVec.allOnes 64 from hones, BitVec.xor_allOnes, BitVec.not_not,
          BitVec.getLsbD_setWidth]
        simp [hb])
      (by rw [Ones, g11]; exact hones)
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, fun r hr => ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁,
    lr₂.trans lr₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8)
      (fun y _ => by simp only [words, sl, m₁, g0]) x hx
  · rw [k₂ _ (by decide), p₁]
  · have hs : r ∈ stepKept ∧ r ≠ .r9 ∧ r ≠ .r3 := by
      simp only [roundKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k₂ r hs.1, o₁ r hs.2.1 hs.2.2]
  · rw [stR_congr g0, m₁] at f₂; exact f₂

/-! ## Pairs of rounds -/

theorem roundPair_eq (d : Direction) :
    roundPair d = round d .ba ++ (round d .ab ++ ([.subi pairs pairs 1] : List Instr)) := by
  simp only [roundPair, List.append_assoc]

theorem Frame.readKey {s : State} (h : Sched s) {A : Addr} (hk : KeyAt s A) {m : Mem}
    (hf : Frame [stR s] s.mem m) : m.readW A 64 = s.mem.readW A 64 :=
  hf.readW (Region.contains_self A 8) (by simpa using keyAt_apart h hk) (by decide)

/-- The registers a pair of rounds leaves alone. -/
def pairKept : List Reg := [.r10, .r4, .r8, .r7, .r11]

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) (hs : Sched s) (hones : Ones s)
    {A : Addr} (hA : s.gpr .r3 = A) (hk₁ : KeyAt s A) (hk₂ : KeyAt s (A + δ d)) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (A + δ d) 64).setWidth 48)
        (roundW .ba ((s.mem.readW A 64).setWidth 48) (words s)) x) ∧
      s'.gpr .r3 = A + δ d + δ d ∧ s'.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 1 ∧
      (∀ r ∈ pairKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, p₁, k₁, rd₁, wr₁, sp₁, lr₁, f₁⟩ := round_ok d .ba h hs hones hA hk₁
  have g0 : s₁.gpr .r10 = s.gpr .r10 := k₁ _ (by decide)
  have g7 : s₁.gpr .r7 = s.gpr .r7 := k₁ _ (by decide)
  have g11 : s₁.gpr .r11 = s.gpr .r11 := k₁ _ (by decide)
  have h₁ := h.congr g0 wr₁
  obtain ⟨s₂, run₂, w₂, p₂, k₂, rd₂, wr₂, sp₂, lr₂, f₂⟩ :=
    round_ok d .ab h₁ (hs.congr g7 g0 rd₁ wr₁) (by rw [Ones, g11]; exact hones) p₁ (hk₂.congr g7)
  have e₃ := exec_subi (s := s₂) (d := .r5) (n := .r5) (imm := 1) (by decide) (by decide)
  have g5 : s₂.gpr .r5 = s.gpr .r5 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  refine ⟨s₂.write .r5 (s₂.gpr .r5 - BitVec.ofNat 64 1), ?_, fun x hx => ?_, ?_, ?_, fun r hr => ?_,
    rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, lr₂.trans lr₁, ?_⟩
  · rw [roundPair_eq]
    refine runBlock_cat_some run₁ (runBlock_cat_some run₂ ?_)
    rw [runBlock_cons, show Impl.TripleDes.PPC64LE.Bitslice.pairs = Reg.r5 from rfl, e₃, runStep_some,
      runBlock_nil]
  · have : words (s₂.write .r5 (s₂.gpr .r5 - BitVec.ofNat 64 1)) x = words s₂ x := by
      simp only [words, sl, mem_write, gpr_write, reduceCtorEq, ite_false]
    rw [this, w₂ x hx]
    rw [Frame.readKey hs hk₂ f₁]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · simp only [gpr_write, reduceCtorEq, ite_false, p₂]
  · simp only [gpr_write, ite_true, g5]
  · simp only [pairKept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_write, reduceCtorEq, ite_false] <;>
      rw [k₂ _ (by decide), k₁ _ (by decide)]
  · simp only [mem_write]
    rw [stR_congr g0] at f₂; exact f₁.trans f₂

/-! ## A pass -/

/-- The offset in the schedule of a pass's first key. -/
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
def passP (s : State) (c : Nat) (d : Direction) : Addr := s.gpr .r7 + BitVec.ofNat 64 (kOff c d)

theorem passKeyAt {s : State} {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    KeyAt s (passP s c d + BitVec.ofNat 64 r * δ d) := by
  refine ⟨16 * c + ix d r, by unfold ix; split <;> omega_arith, ?_⟩
  rw [passP, BitVec.add_assoc, kaddr c hc d r hr]

theorem keyOf_pass (m : Mem) (s : State) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    keyOf m (passP s c d) (δ d) r = roundKey (componentSchedule (scheduleAt m (s.gpr .r7)) c) d r := by
  have hi : ix d r < 16 := by unfold ix; split <;> omega_arith
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl, componentSchedule_readW m _ _ _ hc hi,
    keyOf, passP, BitVec.add_assoc, kaddr c hc d r hr]

/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (c : Nat) (d : Direction) (m : Nat) (s : State) : Prop where
  le : m ≤ 8
  kept : ∀ r ∈ pairKept, s.gpr r = s₀.gpr r
  ptr : s.gpr .r3 = passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d
  cnt : s.gpr .r5 = BitVec.ofNat 64 (8 - m)
  wds : ∀ x < 64, words s x =
    VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP s₀ c d) (δ d)) m (words s₀) x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [stR s₀] s₀.mem s.mem

theorem eval_nonzero_ofNat (s : State) (r : Reg) {a : Nat} (ha : a < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 a) : isa.eval (.nonzero .d r) s = some (decide (a ≠ 0)) := by
  change VG.PPC64LE.eval (.nonzero .d r) s = _
  simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, h]
  congr 1
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
  constructor
  · intro hx h0; subst h0; exact hx rfl
  · intro hx h0
    apply hx
    have := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this

theorem pair_step {s₀ : State} (h₀ : Room s₀) (hs₀ : Sched s₀) (ho₀ : Ones s₀) {c : Nat} (hc : c < 3)
    {d : Direction} {m : Nat} (hm : m < 8) {s : State} (I : PairInv s₀ c d m s) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧ PairInv s₀ c d (m + 1) s' := by
  have g10 := I.kept .r10 (by decide)
  have g7 := I.kept .r7 (by decide)
  have h : Room s := h₀.congr g10 I.wr
  have hs : Sched s := hs₀.congr g7 g10 I.rd I.wr
  have ho : Ones s := by rw [Ones, I.kept .r11 (by decide)]; exact ho₀
  have hk₁ := (passKeyAt (s := s₀) hc d (r := 2 * m) (by omega_using [hm])).congr g7
  have hk₂ := (passKeyAt (s := s₀) hc d (r := 2 * m + 1) (by omega_using [hm])).congr g7
  rw [← kptr_succ] at hk₂
  obtain ⟨s', run, w, p3, p5, k, rd, wr, sp, lr, f⟩ := roundPair_ok d h hs ho I.ptr hk₁ hk₂
  have rk : ∀ r < 16, s.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 =
      s₀.mem.readW (passP s₀ c d + BitVec.ofNat 64 r * δ d) 64 := fun r hr =>
    Frame.readKey hs₀ (passKeyAt (s := s₀) hc d hr) I.frame
  refine ⟨s', run, ⟨by omega_using [hm], fun r hr => (k r hr).trans (I.kept r hr), ?_, ?_, fun x hx => ?_,
    rd.trans I.rd, wr.trans I.wr, sp.trans I.sp, lr.trans I.lr, ?_⟩⟩
  · rw [p3, kptr_succ, kptr_succ]; congr 3
  · rw [p5, I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 64 (8 - m) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (8 - (m + 1))) m hm
  · have e : passP s₀ c d + BitVec.ofNat 64 (2 * m) * δ d + δ d =
        passP s₀ c d + BitVec.ofNat 64 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega_using [hm]), rk _ (by omega_using [hm])]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · exact I.frame.trans (by rw [← stR_congr g10]; exact f)

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) (hs₀ : Sched s₀) (ho₀ : Ones s₀) {c : Nat} (hc : c < 3)
    (d : Direction) {s : State} (I : PairInv s₀ c d 0 s) :
    WP isa (.loop (.block (roundPair d)) (.nonzero .d pairs)) s (PairInv s₀ c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  obtain ⟨v', run, J'⟩ := pair_step h₀ hs₀ ho₀ hc hm J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show Impl.TripleDes.PPC64LE.Bitslice.pairs = Reg.r5 from rfl,
    eval_nonzero_ofNat _ _ (by omega_using []) J'.cnt]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right; exact ⟨by simp; omega_using [hm, e], 8 - (m + 1), by omega_using [hm, hn], m + 1, by omega_using [hm, e], rfl, J'⟩

/-- The registers a pass leaves alone. -/
def passKept : List Reg := [.r10, .r4, .r8, .r7, .r11]

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) (hs : Sched s)
    (ho : Ones s) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x =
        passW (componentSchedule (scheduleAt s.mem (s.gpr .r7)) c) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  unfold pass
  apply WP.seq
  have e₁ := exec_addi (s := s) (d := .r3) (n := .r7)
    (imm := 128 * c + if d = .encrypt then 0 else 120) (by decide)
    (by cases d <;> (simp only [reduceCtorEq, ite_true, ite_false]; omega_using [hc]))
  let s₁ := s.write .r3 (s.gpr .r7 + BitVec.ofNat 64 (128 * c + if d = .encrypt then 0 else 120))
  have e₂ := exec_li (s := s₁) (d := .r5) (imm := 8) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, show keyPtr = .r3 from rfl, show sched = .r7 from rfl, e₁, runStep_some,
      runBlock_cons, show Impl.TripleDes.PPC64LE.Bitslice.pairs = Reg.r5 from rfl, e₂, runStep_some,
      runBlock_nil], ?_⟩
  have z : BitVec.ofNat 64 (2 * 0) * δ d = 0#64 := by cases d <;> decide
  have I0 : PairInv s c d 0 (s₁.write .r5 (BitVec.ofNat 64 8)) := by
    refine ⟨by decide, fun r hr => ?_, ?_, by simp [gpr_write], fun x hx => rfl, rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
    · simp only [pairKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [s₁, gpr_write]
    · simp only [s₁, gpr_write, reduceCtorEq, ite_false, ite_true, passP, z, kOff, BitVec.add_zero]
  apply WP.seq
  refine WP.mono (pairLoop_ok h hs ho hc d I0) fun v J => ?_
  have hv : Room v := h.congr (J.kept .r10 (by decide)) J.wr
  obtain ⟨v', run, w, k, rd, wr, sp, lr, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, fun r hr => ?_, rd.trans J.rd, wr.trans J.wr,
    sp.trans J.sp, lr.trans J.lr, ?_⟩
  · rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
    refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
    rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8 (fun r hr => keyOf_pass _ _ hc d hr)]
  · have hne : r ≠ .r12 ∧ r ≠ .r14 := by
      simp only [passKept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k _ hne.1 hne.2, J.kept r hr]
  · rw [stR_congr (J.kept .r10 (by decide))] at f; exact J.frame.trans f

/-! ## The three passes -/

theorem passes_ok (d : Direction) {s : State} (h : Room s) (hs : Sched s) (ho : Ones s) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (s.gpr .r7)) d (words s) x) ∧
      (∀ r ∈ passKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ Frame [stR s] s.mem s'.mem := by
  have hK : ∀ {u : State}, Frame [stR s] s.mem u.mem →
      scheduleAt u.mem (s.gpr .r7) = scheduleAt s.mem (s.gpr .r7) := fun hf =>
    VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (Region.sub_prefix (by omega_using []))
  have step : ∀ (c : Nat) (hc : c < 3) (d' : Direction) {u : State}, Room u → Sched u → Ones u →
      u.gpr .r7 = s.gpr .r7 → Frame [stR s] s.mem u.mem →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (s.gpr .r7)) c) d' (words u) x) → (∀ r ∈ passKept, u'.gpr r = u.gpr r) →
        u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → u'.lr = u.lr → Frame [stR u] u.mem u'.mem → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u hu hsu hou h7 hf Q hQ
    refine WP.mono (pass_ok c hc d' hu hsu hou) fun u' ⟨w, k, rd, wr, sp, lr, f⟩ =>
      hQ u' ?_ k rd wr sp lr f
    rw [h7, hK hf] at w; exact w
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ h hs ho rfl (Frame.refl _ _) fun u₁ w₁ k₁ rd₁ wr₁ sp₁ lr₁ f₁ => ?_
    have g₁ : u₁.gpr .r10 = s.gpr .r10 := k₁ _ (by decide)
    have g₁7 : u₁.gpr .r7 = s.gpr .r7 := k₁ _ (by decide)
    have h₁ : Room u₁ := h.congr g₁ wr₁
    have hs₁ : Sched u₁ := hs.congr g₁7 g₁ rd₁ wr₁
    have ho₁ : Ones u₁ := by rw [Ones, k₁ _ (by decide)]; exact ho
    apply WP.seq
    refine step _ (by decide) _ h₁ hs₁ ho₁ g₁7 f₁ fun u₂ w₂ k₂ rd₂ wr₂ sp₂ lr₂ f₂ => ?_
    have g₂ : u₂.gpr .r10 = s.gpr .r10 := (k₂ _ (by decide)).trans g₁
    have g₂7 : u₂.gpr .r7 = s.gpr .r7 := (k₂ _ (by decide)).trans g₁7
    have h₂ : Room u₂ := h.congr g₂ (wr₂.trans wr₁)
    have hs₂ : Sched u₂ := hs.congr g₂7 g₂ (rd₂.trans rd₁) (wr₂.trans wr₁)
    have ho₂ : Ones u₂ := by rw [Ones, k₂ _ (by decide), k₁ _ (by decide)]; exact ho
    have f₁₂ : Frame [stR s] s.mem u₂.mem := f₁.trans (by rw [← stR_congr g₁]; exact f₂)
    refine step _ (by decide) _ h₂ hs₂ ho₂ g₂7 f₁₂
      fun u₃ w₃ k₃ rd₃ wr₃ sp₃ lr₃ f₃ => ⟨fun x hx => ?_, fun r hr => by rw [k₃ r hr, k₂ r hr, k₁ r hr],
        rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
        lr₃.trans (lr₂.trans lr₁), f₁₂.trans (by rw [← stR_congr g₂]; exact f₃)⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.PPC64LE.Bitsliced
