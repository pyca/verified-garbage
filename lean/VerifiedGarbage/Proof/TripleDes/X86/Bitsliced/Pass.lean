module

public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.SboxTables

/-! ### `TripleDes.X86.Bitsliced.Step`, which only this module used -/

section

/-! ### `TripleDes.X86.Bitsliced.Sbox`, which only this module used -/

section

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

end

end

/-!
# One S-box of a bitsliced round on x86 (32-bit), and the exchange of the halves

As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Step.lean`). `sboxStep_ok`: the
code of S-box `j` (its inputs, the key's bits `inBit j i`, from the round
key's words in words `kloSlot` and `khiSlot` of the working space, as masks
XORed with the words of `E`, into the first six words; its circuit; XORing
its outputs into their words) does to the state words what `step` does, and
writes only the circuits' words and the state words. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Straight VG.X86.Wp VG.Bitslice VG.Impl.TripleDes.X86.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 32) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-- The carry of a word added to itself is its top bit. -/
theorem carry_double (x : BitVec 32) : decide (2 ^ 32 ≤ x.toNat + x.toNat) = x.getLsbD 31 := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  apply decide_eq_decide.mpr
  omega_using [this]

/-- A word of the working space in a state that differs from `s` by a store to another. -/
theorem fw_write {s s' : State} (h : Room s) {k j : Nat} {v : BitVec 32}
    (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) k) v) (hb : s'.gpr .ebp = s.gpr .ebp)
    (hk : k < wsWords) (hj : j < wsWords) : fw s' j = if j = k then v else fw s j := by
  rw [← fw_stFw h hk hj v, fw, fw, hb, hm]; rfl

/-! ## Inputs -/

/-- One input: bit `c` of the word in slot `kslot` as a mask, XORed with the
word in slot `st`, into slot `i`. -/
theorem inputAt_wp {s : State} (h : Room s) {kslot c st i : Nat} (hk : kslot < wsWords) (hc : c < 32)
    (hst : st < wsWords) (hi : i < wsWords) :
    WP isa (.block (inputAt kslot c st i)) s fun s' =>
      s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) i) (maskVal ((fw s kslot).getLsbD c) ^^^ fw s st) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have tail : ∀ (s₂ : State), s₂.cf = some ((fw s kslot).getLsbD c) → s₂.mem = s.mem →
      (∀ r, r ≠ .eax → s₂.gpr r = s.gpr r) → s₂.rd = s.rd → s₂.wr = s.wr →
      WP isa (.block [.alu .sbb .ecx (.reg .ecx), .alu .xor .ecx (.mem (ws st)), .store (ws i) .ecx]) s₂
        fun s' => s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) i)
            (maskVal ((fw s kslot).getLsbD c) ^^^ fw s st) ∧
          (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    intro s₂ cf₂ m₂ g₂ rd₂ wr₂
    refine wp_sbb_self cf₂ fun s₃ u₃ => ?_
    have b₃ : s₃.gpr .ebp = s.gpr .ebp := by rw [u₃.other _ (by decide), g₂ _ (by decide)]
    refine wp_xorm (B := s.gpr .ebp) b₃ (by rw [u₃.rd, u₃.wr, rd₂, wr₂]; exact slot_rd h hst) fun s₄ u₄ => ?_
    have b₄ : s₄.gpr .ebp = s.gpr .ebp := by rw [u₄.other _ (by decide), b₃]
    refine wp_stm (B := s.gpr .ebp) b₄ (by rw [u₄.wr, u₃.wr, wr₂]; exact slot_in h hi) fun s₅ u₅ =>
      WP.block_nil ⟨?_, fun r h0 h1 => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, rd₂], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]⟩
    · rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₄.gpr, u₃.gpr, u₃.mem, m₂]
      rfl
    · rw [u₅.gpr, u₄.other _ h1, u₃.other _ h1, g₂ _ h0]
  unfold inputAt
  split
  · rename_i h31
    subst h31
    refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h hk) fun s₁ u₁ => ?_
    refine wp_add fun s₂ u₂ cf₂ => ?_
    refine tail s₂ ?_ (by rw [u₂.mem, u₁.mem]) (fun r hr => by rw [u₂.other _ hr, u₁.other _ hr])
      (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    rw [cf₂, carry_double, u₁.gpr]; rfl
  · rename_i h31
    refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h hk) fun s₁ u₁ => ?_
    refine wp_shr (by omega_using [hc, h31]) fun s₂ u₂ cf₂ => ?_
    refine tail s₂ ?_ (by rw [u₂.mem, u₁.mem]) (fun r hr => by rw [u₂.other _ hr, u₁.other _ hr])
      (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    rw [cf₂, u₁.gpr, Nat.add_sub_cancel]; rfl

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j n := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

/-- The slot of the key word with S-box `j`'s input `m`. -/
def keySlot (j m : Nat) : Nat := if inBit j m < 32 then kloSlot else khiSlot

theorem keySlot_bounds (j m : Nat) : 6 ≤ keySlot j m ∧ keySlot j m < wsWords := by
  unfold keySlot; split <;> decide

/-- The first `n` inputs of S-box `j`, in the first words of the working space. -/
structure Ins (ρ : Role) (j n : Nat) (s s' : State) : Prop where
  ins : ∀ m < n, fw s' m = maskVal ((fw s (keySlot j m)).getLsbD (inBit j m % 32)) ^^^
    words s (readWord ρ (eBit (inBit j m)))
  rest : ∀ k, n ≤ k → k < wsWords → fw s' k = fw s k
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [headR s 6] s.mem s'.mem

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s) :
    WP isa (.block (inputsN ρ j n)) s (Ins ρ j n s) := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun m hm => by omega, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [inputsN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s₁ p₁ => ?_
    have b₁ : s₁.gpr .ebp = s.gpr .ebp := p₁.regs _ (by decide) (by decide)
    have h₁ : Room s₁ := h.congr b₁ p₁.wr
    obtain ⟨kb0, kb1⟩ := keySlot_bounds j n
    have hw := readWord_lt ρ j hj n (by omega_using [hn])
    have hst : stSlot (readWord ρ (eBit (inBit j n))) < wsWords := by
      unfold stSlot spills wsWords; omega_using [hw]
    refine WP.mono (inputAt_wp h₁ (kslot := keySlot j n) (c := inBit j n % 32)
      (st := stSlot (readWord ρ (eBit (inBit j n)))) (i := n) kb1 (Nat.mod_lt _ (by decide)) hst
      (by unfold wsWords; omega_using [hn])) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    have b₂ : s₂.gpr .ebp = s₁.gpr .ebp := g₂ _ (by decide) (by decide)
    have fwn : ∀ k, k < wsWords → fw s₂ k = if k = n then
        maskVal ((fw s₁ (keySlot j n)).getLsbD (inBit j n % 32)) ^^^
          fw s₁ (stSlot (readWord ρ (eBit (inBit j n)))) else fw s₁ k := fun k hk =>
      fw_write h₁ m₂ b₂ (by unfold wsWords; omega_using [hn]) hk
    refine ⟨fun m hm => ?_, fun k hk hk' => ?_, fun r h0 h1 => by rw [g₂ r h0 h1, p₁.regs r h0 h1],
      rd₂.trans p₁.rd, wr₂.trans p₁.wr, ?_⟩
    · rw [fwn m (by unfold wsWords; omega_using [hn, hm])]
      by_cases he : m = n
      · subst he
        rw [ite_eq_left rfl, p₁.rest _ (by omega_using [kb0, hn]) kb1,
          p₁.rest _ (by unfold stSlot spills; omega_using [hn]) hst]
        rfl
      · rw [ite_eq_right he]; exact p₁.ins m (by omega_using [hm, he])
    · rw [fwn k hk', ite_eq_right (by omega_using [hk]), p₁.rest k (by omega_using [hk]) hk']
    · refine p₁.frame.trans ?_
      rw [m₂, b₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (slot_contains _ (by omega_using [hn]) (by have := h.fit; unfold wsWords at this; omega_using [this]))

/-! ## Outputs -/

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot (spills + k) ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 32) varsCfg (fun _ => none) (outputCode ρ j) (varEnv outRegs) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem output_kept : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => i.dst != some .esp) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, words s' k = match outIdx ρ j k with
        | some i => words s k ^^^ s.gpr (outReg i)
        | none => words s k) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun outRegs (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, p.base, p.other _ (by rw [output_kept ρ j hj]; exact Bool.noConfusion),
    p.rd, p.wr, p.frame⟩
  rw [varRel_word p.rel hk (hpost k hk)]
  split
  · rename_i i hi
    have hi4 := outIdx_lt ρ j k i hi
    rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega_using [hk])
      (by simp [varN, outRegs]; omega_using [hi4])]
    have e1 : ¬ 64 + i < 64 := by omega_using []
    simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outReg]
  · rw [xorSet_two_pow _ (by simp [varN]; omega_using [hk])]
    simp only [varVals, hk, ite_true]

/-! ## One S-box -/

theorem sboxStep_eq (ρ : Role) (j : Nat) :
    sboxStep ρ j = inputsN ρ j 6 ++ (sboxCode j ++ outputCode ρ j) := by
  simp only [sboxStep, inputCode_eq, List.append_assoc]

/-- The key `k`'s low and high words. -/
structure KeyWords (lo hi : BitVec 32) (k : BitVec 48) : Prop where
  lo : ∀ b < 32, lo.getLsbD b = k.getLsbD b
  hi : ∀ b < 16, hi.getLsbD b = k.getLsbD (32 + b)

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : KeyWords (fw s kloSlot) (fw s khiSlot) k) :
    WP isa (.block (sboxStep ρ j)) s fun s' =>
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [stR s] s.mem s'.mem := by
  rw [sboxStep_eq, WP.block_append_iff]
  refine WP.mono (inputsN_ok ρ hj (Nat.le_refl 6) h) fun s₁ p₁ => ?_
  have g₁ : s₁.gpr .ebp = s.gpr .ebp := p₁.regs _ (by decide) (by decide)
  have h₁ : Room s₁ := h.congr g₁ p₁.wr
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, g₂', sp₂, f₂⟩ := sbox_ok j hj (h₁.ok rfl (by decide) rfl)
  have g₂ : s₂.gpr .ebp = s.gpr .ebp := g₂'.trans g₁
  have h₂ : Room s₂ := h.congr g₂ (wr₂.trans p₁.wr)
  obtain ⟨s₃, run₃, w₃, g₃, sp₃, rd₃, wr₃, f₃⟩ := outputs_ok ρ hj h₂
  refine WP.of_runBlock ⟨s₃, runBlock_cat_some run₂ run₃, ?_⟩
  have f₁₂ : Frame [headR s spills] s.mem s₂.mem := by
    have e : slotRegion sboxCfg s₁ = headR s spills := by simp only [slotRegion, sboxCfg, headR, g₁]
    rw [e] at f₂
    exact (headR_mono (by decide) p₁.frame).trans f₂
  have w₂ : ∀ x < 64, words s₂ x = words s x := fun x hx => by
    simp only [words, fw, g₂]
    exact fw_frame h f₁₂ (Nat.le_add_right _ _) (by unfold spills wsWords; omega_using [hx])
  have kbit : ∀ i < 6, (fw s (keySlot j i)).getLsbD (inBit j i % 32) = k.getLsbD (inBit j i) := by
    intro i hi
    have hb : inBit j i < 48 := by unfold inBit; omega_using [hi, hj]
    unfold keySlot
    split
    · rename_i hlt
      rw [Nat.mod_eq_of_lt hlt]; exact hkey.lo _ hlt
    · rename_i hge
      rw [show inBit j i % 32 = inBit j i - 32 by omega_using [hb, hge],
        hkey.hi _ (by omega_using [hb, hge])]
      congr 1; omega_using [hge]
  have hin : ∀ i < 6, fw s₁ i =
      maskVal (k.getLsbD (inBit j i)) ^^^ words s (readWord ρ (eBit (inBit j i))) := by
    intro i hi
    rw [p₁.ins i hi, kbit i hi]
  refine ⟨fun x hx => ?_, g₃.trans g₂, sp₃.trans (sp₂.trans (p₁.regs _ (by decide) (by decide))),
    rd₃.trans (rd₂.trans p₁.rd), wr₃.trans (wr₂.trans p₁.wr), ?_⟩
  · rw [w₃ _ hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact w₂ x hx
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [w₂ x hx]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputsAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_mask _ hp]
      rw [Bool.xor_comm]
  · refine (f₁₂.sub fun r hr => ?_).trans (by rw [← stR_congr g₂]; exact f₃)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold spills; omega_using [])⟩

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot (spills + k) == some (2 ^ swapSlot k)

theorem swap_check :
    check (vars 32) varsCfg (fun _ => none) swapHalves (varEnv []) swapPost = true := by
  lit_decide

theorem swap_kept : (swapHalves.all fun i => i.dst != some .esp) = true := by lit_decide

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 64, words s' k = words s (swapSlot k) := by
    intro k hk
    rw [varRel_word p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, p.base, p.other _ (by rw [swap_kept]; exact Bool.noConfusion), p.rd, p.wr,
    p.frame⟩
  rw [key _ hx]
  simp only [swapW, swapSlot]
  rcases partner x with _ | y <;> rfl

end VG.Proof.TripleDes.X86.Bitsliced

end

end

/-!
# Bitsliced DES rounds and passes on x86 (32-bit)

As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Pass.lean`). `round_ok`: the
code of a round copies the round key at the key pointer (word `kpSlot` of
the working space) into words `kloSlot` and `khiSlot`, steps the pointer by
`δ d` (8 or −8) and does to the state words what `roundW` does with the
key's low 48 bits. `pass_ok`: a pass points the key pointer at its first key
in the schedule (whose address is word `schedSlot`), runs eight pairs of
rounds (counted down in word `cntSlot`) and exchanges the halves: what
`passW` does with the component schedule. `passes_ok`: the three passes do
what `tdeaW` does. They write only the first 82 words of the working space.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Wp VG.Bitslice VG.Impl.TripleDes.X86.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.X86.Straight (wordAddr addr_add_ofNat)

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 32 := if d = .encrypt then 8 else -8

/-- The schedule at `Sb` is readable, does not wrap around and is apart from
the working space. -/
structure Sched (s : State) (Sb : BitVec 32) : Prop where
  rd : (⟨Sb.setWidth 64, 384⟩ : Region) ∈ s.rd
  fit : Sb.toNat + 384 ≤ 2 ^ 32
  apart : (⟨Sb.setWidth 64, 384⟩ : Region).Disjoint (frameR s)

theorem Sched.congr {s s' : State} {Sb : BitVec 32} (h : Sched s Sb) (hb : s'.gpr .ebp = s.gpr .ebp)
    (hr : s'.rd = s.rd) : Sched s' Sb where
  rd := by rw [hr]; exact h.rd
  fit := h.fit
  apart := by rw [frameR, hb]; exact h.apart

/-- A round key's pointer: to word `i < 48` of the schedule. -/
def KeyAt (Sb P : BitVec 32) : Prop := ∃ i < 48, P = Sb + BitVec.ofNat 32 (8 * i)

/-- The key at `P`: the low 48 bits of its doubleword. -/
def keyW (m : Mem) (P : BitVec 32) : BitVec 48 := (m.readW (P.setWidth 64) 64).setWidth 48

theorem keyAt_addr {Sb P : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) (hk : KeyAt Sb P) :
    ∃ i < 48, P = Sb + BitVec.ofNat 32 (8 * i) ∧
      P.setWidth 64 = Sb.setWidth 64 + BitVec.ofNat 64 (8 * i) ∧ P.toNat + 8 ≤ 2 ^ 32 := by
  obtain ⟨i, hi, rfl⟩ := hk
  refine ⟨i, hi, rfl, addr_eq (by omega_using [hf, hi]), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [hi]),
    Nat.mod_eq_of_lt (by omega_using [hf, hi])]
  omega_using [hf, hi]

/-- A word of a round key, in the schedule. -/
theorem keyAt_contains {Sb P : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) (hk : KeyAt Sb P) {off : Nat}
    (ho : off + 4 ≤ 8) : (⟨Sb.setWidth 64, 384⟩ : Region).Contains (addr P off) 4 := by
  obtain ⟨i, hi, rfl⟩ := hk
  rw [addr_add_ofNat, addr_eq (by omega_using [hf, hi, ho])]
  exact Offset.contains_base _ (by omega_using [hi, ho]) (by omega_using [hi, ho])

theorem keyAt_rd {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {off : Nat}
    (ho : off + 4 ≤ 8) : InRegions (s.rd ++ s.wr) (addr P off) 4 :=
  ⟨_, List.mem_append_left _ hs.rd, keyAt_contains hs.fit hk ho⟩

/-- A round key is not in the working space. -/
theorem keyW_frame {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {n : Nat}
    (hn : n ≤ wsWords) {m : Mem} (hf : Frame [headR s n] s.mem m) : keyW m P = keyW s.mem P := by
  obtain ⟨i, hi, -, ha, -⟩ := keyAt_addr hs.fit hk
  rw [keyW, keyW, ha]
  refine congrArg (BitVec.setWidth 48) (hf.readW (r := ⟨Sb.setWidth 64, 384⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (fun r hr => ?_) (by decide))
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

/-- A word of a round key, after writes to the working space. -/
theorem keyWord_frame {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {n : Nat}
    (hn : n ≤ wsWords) {m : Mem} (hf : Frame [headR s n] s.mem m) {off : Nat} (ho : off + 4 ≤ 8) :
    m.readW (addr P off) 32 = s.mem.readW (addr P off) 32 := by
  refine hf.readW (r := ⟨Sb.setWidth 64, 384⟩) (keyAt_contains hs.fit hk ho) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

/-- The two words of a key. -/
theorem keyWords_read (m : Mem) {P : BitVec 32} (hP : P.toNat + 8 ≤ 2 ^ 32) :
    KeyWords (m.readW (addr P 0) 32) (m.readW (addr P 4) 32) (keyW m P) := by
  rw [addr_eq (by omega_using [hP]), addr_eq (by omega_using [hP]), BitVec.add_zero, Mem.readW_lo32 rfl,
    Mem.readW_hi32 rfl, keyW]
  constructor
  · intro b hb
    simp only [BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show b < 48 by omega_using [hb]]
  · intro b hb
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', show b < 32 by omega_using [hb],
      decide_true, Bool.true_and, show 32 + b < 48 by omega_using [hb]]

/-! ## A round -/

/-- What a block that stores only to the working space's first `n` words keeps. -/
structure Kept (n : Nat) (s s' : State) : Prop where
  ebp : s'.gpr .ebp = s.gpr .ebp
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [headR s n] s.mem s'.mem

theorem Kept.refl (n : Nat) (s : State) : Kept n s s := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {n : Nat} {s₁ s₂ s₃ : State} (h₁ : Kept n s₁ s₂) (h₂ : Kept n s₂ s₃) : Kept n s₁ s₃ :=
  ⟨h₂.ebp.trans h₁.ebp, h₂.esp.trans h₁.esp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.frame.trans (by rw [← headR_congr h₁.ebp]; exact h₂.frame)⟩

theorem Kept.mono {n n' : Nat} {s s' : State} (h : Kept n s s') (hn : n ≤ n') : Kept n' s s' :=
  ⟨h.ebp, h.esp, h.rd, h.wr, headR_mono hn h.frame⟩

theorem Kept.room {n : Nat} {s s' : State} (h : Kept n s s') (hr : Room s) : Room s' :=
  hr.congr h.ebp h.wr

theorem Kept.sched {n : Nat} {s s' : State} {Sb : BitVec 32} (h : Kept n s s') (hs : Sched s Sb) :
    Sched s' Sb := hs.congr h.ebp h.rd

theorem Kept.fw {n : Nat} {s s' : State} (h : Kept n s s') (hr : Room s) {k : Nat} (hn : n ≤ k)
    (hk : k < wsWords) : fw s' k = fw s k := fw_of_frame hr h.ebp h.frame hn hk

theorem keyLoad_ok (d : Direction) {s : State} (h : Room s) {Sb P : BitVec 32} (hs : Sched s Sb)
    (hk : KeyAt Sb P) (hP : fw s kpSlot = P) :
    WP isa (.block (keyLoad d)) s fun s' =>
      KeyWords (fw s' kloSlot) (fw s' khiSlot) (keyW s.mem P) ∧ fw s' kpSlot = P + δ d ∧
      (∀ k, k < kloSlot → fw s' k = fw s k) ∧ Kept 81 s s' := by
  obtain ⟨-, -, -, -, hfit⟩ := keyAt_addr hs.fit hk
  unfold keyLoad
  refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h (by decide)) fun s₁ u₁ => ?_
  have p₁ : s₁.gpr .eax = P := u₁.gpr.trans hP
  refine wp_ldm (B := P) p₁ (by rw [u₁.rd, u₁.wr]; exact keyAt_rd hs hk (by decide)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebp = s.gpr .ebp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stm (B := s.gpr .ebp) b₂ (by rw [u₂.wr, u₁.wr]; exact slot_in h (by decide)) fun s₃ u₃ => ?_
  have m₃ : s₃.mem = s.mem.writeW (wordAddr (s.gpr .ebp) kloSlot) (s.mem.readW (addr P 0) 32) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.mem]
  have k₃ : Kept 81 s s₃ := ⟨by rw [u₃.gpr]; exact b₂,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], by rw [m₃]; exact stFw_frame h (k := kloSlot) (by decide) (by decide) _⟩
  have h₃ : Room s₃ := k₃.room h
  refine wp_ldm (B := P) (by rw [u₃.gpr, u₂.other _ (by decide)]; exact p₁)
    (by rw [k₃.rd, k₃.wr]; exact keyAt_rd hs hk (by decide)) fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .ebp = s₃.gpr .ebp := u₄.other _ (by decide)
  refine wp_stm (B := s₃.gpr .ebp) b₄ (by rw [u₄.wr]; exact slot_in h₃ (by decide)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₃.mem.writeW (wordAddr (s₃.gpr .ebp) khiSlot) (s.mem.readW (addr P 4) 32) := by
    rw [u₅.mem, u₄.mem, u₄.gpr, keyWord_frame hs hk (by decide) k₃.frame (by decide)]
  have k₅ : Kept 81 s₃ s₅ := ⟨by rw [u₅.gpr]; exact b₄, by rw [u₅.gpr, u₄.other _ (by decide)],
    by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr],
    by rw [m₅]; exact stFw_frame h₃ (k := khiSlot) (by decide) (by decide) _⟩
  have h₅ : Room s₅ := k₅.room h₃
  have a₅ : s₅.gpr .eax = P := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide)]; exact p₁
  -- The pointer stepped and stored: what both directions end with.
  have fin : ∀ s₆ : State, s₆.gpr .eax = P + δ d → (∀ r, r ≠ .eax → s₆.gpr r = s₅.gpr r) → s₆.mem = s₅.mem →
      s₆.rd = s₅.rd → s₆.wr = s₅.wr →
      WP isa (.block [.store (ws kpSlot) .eax]) s₆ fun s' =>
        KeyWords (fw s' kloSlot) (fw s' khiSlot) (keyW s.mem P) ∧ fw s' kpSlot = P + δ d ∧
        (∀ k, k < kloSlot → fw s' k = fw s k) ∧ Kept 81 s s' := by
    intro s₆ a₆ g₆ m₆ rd₆ wr₆
    have b₆ : s₆.gpr .ebp = s₅.gpr .ebp := g₆ _ (by decide)
    refine wp_stm (B := s₅.gpr .ebp) b₆ (by rw [wr₆]; exact slot_in h₅ (by decide)) fun s₇ u₇ =>
      WP.block_nil ?_
    have m₇ : s₇.mem = s₅.mem.writeW (wordAddr (s₅.gpr .ebp) kpSlot) (P + δ d) := by
      rw [u₇.mem, m₆, a₆]
    have k₇ : Kept 81 s₅ s₇ := ⟨by rw [u₇.gpr]; exact b₆, by rw [u₇.gpr, g₆ _ (by decide)],
      by rw [u₇.rd, rd₆], by rw [u₇.wr, wr₆],
      by rw [m₇]; exact stFw_frame h₅ (k := kpSlot) (by decide) (by decide) _⟩
    have f : ∀ j, j < wsWords → fw s₇ j =
        if j = kpSlot then P + δ d else if j = khiSlot then s.mem.readW (addr P 4) 32
        else if j = kloSlot then s.mem.readW (addr P 0) 32 else fw s j := by
      intro j hj
      rw [fw_write h₅ m₇ k₇.ebp (by decide) hj]
      by_cases e80 : j = kpSlot
      · rw [ite_eq_left e80, ite_eq_left e80]
      rw [ite_eq_right e80, ite_eq_right e80, fw_write h₃ m₅ k₅.ebp (by decide) hj]
      by_cases e79 : j = khiSlot
      · rw [ite_eq_left e79, ite_eq_left e79]
      rw [ite_eq_right e79, ite_eq_right e79, fw_write h m₃ k₃.ebp (by decide) hj]
    refine ⟨?_, ?_, fun k hk => ?_, k₃.trans (k₅.trans k₇)⟩
    · rw [f kloSlot (by decide), f khiSlot (by decide)]
      exact keyWords_read s.mem hfit
    · rw [f kpSlot (by decide)]; rfl
    · unfold kloSlot at hk
      rw [f k (by unfold wsWords; omega_using [hk]), ite_eq_right (by unfold kpSlot; omega_using [hk]),
        ite_eq_right (by unfold khiSlot; omega_using [hk]), ite_eq_right (by unfold kloSlot; omega_using [hk])]
  cases d
  · refine wp_addi fun s₆ u₆ => fin s₆ ?_ (fun r hr => u₆.other r hr) u₆.mem u₆.rd u₆.wr
    rw [u₆.gpr, a₅]; rfl
  · refine wp_subi fun s₆ u₆ _ _ => fin s₆ ?_ (fun r hr => u₆.other r hr) u₆.mem u₆.rd u₆.wr
    rw [u₆.gpr, a₅]; exact BitVec.sub_eq_add_neg _ _

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : KeyWords (fw s kloSlot) (fw s khiSlot) k) :
    WP isa (.block (stepsCode ρ n)) s fun s' =>
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧ Kept (spills + 64) s s' := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, Kept.refl _ _⟩
  | succ n ih =>
    rw [stepsCode_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s₁ ⟨w₁, k₁⟩ => ?_
    have h₁ : Room s₁ := k₁.room h
    have key₁ : KeyWords (fw s₁ kloSlot) (fw s₁ khiSlot) k := by
      rw [k₁.fw h (by decide) (by decide), k₁.fw h (by decide) (by decide)]
      exact hkey
    refine WP.mono (sboxStep_ok ρ (j := n) (by omega_using [hn]) h₁ k key₁)
      fun s₂ ⟨w₂, g₂, sp₂, rd₂, wr₂, f₂⟩ => ⟨fun x hx => ?_, k₁.trans ⟨g₂, sp₂, rd₂, wr₂, f₂⟩⟩
    rw [w₂ x hx, steps_succ]
    exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega_using [hn]) w₁ (w₁ x hx)

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) {Sb P : BitVec 32}
    (hs : Sched s Sb) (hk : KeyAt Sb P) (hP : fw s kpSlot = P) :
    WP isa (.block (round d ρ)) s fun s' =>
      (∀ x < 64, words s' x = roundW ρ (keyW s.mem P) (words s) x) ∧ fw s' kpSlot = P + δ d ∧
      Kept 81 s s' := by
  rw [round_eq, WP.block_append_iff]
  refine WP.mono (keyLoad_ok d h hs hk hP) fun s₁ ⟨key₁, p₁, w₁, k₁⟩ => ?_
  have h₁ : Room s₁ := k₁.room h
  refine WP.mono (stepsCode_ok ρ (keyW s.mem P) (Nat.le_refl 8) h₁ key₁) fun s₂ ⟨w₂, k₂⟩ =>
    ⟨fun x hx => ?_, ?_, k₁.trans (k₂.mono (by decide))⟩
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8)
      (fun y hy => w₁ _ (by unfold spills kloSlot; omega_using [hy])) x hx
  · rw [k₂.fw h₁ (by decide) (by decide), p₁]

/-! ## Pairs of rounds -/

/-- The count of pairs left, one less. -/
def countDown : List Instr :=
  [.mov .eax (.mem (ws cntSlot)), .alu .sub .eax (.imm 1), .store (ws cntSlot) .eax]

theorem roundPair_eq (d : Direction) : roundPair d = round d .ba ++ (round d .ab ++ countDown) := by
  simp only [roundPair, countDown, List.append_assoc]

theorem countDown_ok {s : State} (h : Room s) :
    WP isa (.block countDown) s fun s' =>
      fw s' cntSlot = fw s cntSlot - 1 ∧ s'.zf = some (fw s cntSlot - 1 == 0) ∧
      (∀ j < wsWords, j ≠ cntSlot → fw s' j = fw s j) ∧ Kept 82 s s' := by
  unfold countDown
  refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h (by decide)) fun s₁ u₁ => ?_
  refine wp_subi fun s₂ u₂ _ z₂ => ?_
  have b₂ : s₂.gpr .ebp = s.gpr .ebp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stm (B := s.gpr .ebp) b₂ (by rw [u₂.wr, u₁.wr]; exact slot_in h (by decide)) fun s₃ u₃ =>
    WP.block_nil ?_
  have v : s₂.gpr .eax = fw s cntSlot - 1 := by rw [u₂.gpr, u₁.gpr]; rfl
  have m₃ : s₃.mem = s.mem.writeW (wordAddr (s.gpr .ebp) cntSlot) (fw s cntSlot - 1) := by
    rw [u₃.mem, u₂.mem, u₁.mem, v]
  have b₃ : s₃.gpr .ebp = s.gpr .ebp := by rw [u₃.gpr]; exact b₂
  refine ⟨?_, ?_, fun j hj hne => ?_, b₃, by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
    by rw [m₃]; exact stFw_frame h (k := cntSlot) (by decide) (by decide) _⟩
  · rw [fw_write h m₃ b₃ (by decide) (by decide), ite_eq_left rfl]
  · rw [u₃.zf, z₂, u₁.gpr]; rfl
  · rw [fw_write h m₃ b₃ (by decide) hj, ite_eq_right hne]

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) {Sb P : BitVec 32} (hs : Sched s Sb)
    (hk₁ : KeyAt Sb P) (hk₂ : KeyAt Sb (P + δ d)) (hP : fw s kpSlot = P) :
    WP isa (.block (roundPair d)) s fun s' =>
      (∀ x < 64, words s' x = roundW .ab (keyW s.mem (P + δ d))
        (roundW .ba (keyW s.mem P) (words s)) x) ∧
      fw s' kpSlot = P + δ d + δ d ∧ fw s' cntSlot = fw s cntSlot - 1 ∧
      s'.zf = some (fw s cntSlot - 1 == 0) ∧ Kept 82 s s' := by
  rw [roundPair_eq, WP.block_append_iff]
  refine WP.mono (round_ok d .ba h hs hk₁ hP) fun s₁ ⟨w₁, p₁, k₁⟩ => ?_
  have h₁ : Room s₁ := k₁.room h
  rw [WP.block_append_iff]
  refine WP.mono (round_ok d .ab h₁ (k₁.sched hs) hk₂ p₁) fun s₂ ⟨w₂, p₂, k₂⟩ => ?_
  have k₁₂ : Kept 81 s s₂ := k₁.trans k₂
  have h₂ : Room s₂ := k₁₂.room h
  refine WP.mono (countDown_ok h₂) fun s₃ ⟨c₃, z₃, o₃, k₃⟩ => ?_
  have c₂ : fw s₂ cntSlot = fw s cntSlot := k₁₂.fw h (by decide) (by decide)
  refine ⟨fun x hx => ?_, ?_, by rw [c₃, c₂], by rw [z₃, c₂], (k₁₂.mono (by decide)).trans k₃⟩
  · have : words s₃ x = words s₂ x := by
      rw [words, o₃ _ (by unfold spills wsWords; omega_using [hx]) (by unfold spills cntSlot; omega_using [hx])]
      rfl
    rw [this, w₂ x hx, keyW_frame hs hk₂ (by decide) k₁.frame]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · rw [o₃ _ (by decide) (by decide), p₂]

/-! ## A pass -/

/-- The word of the component that is round `r`'s key. -/
def ix (d : Direction) (r : Nat) : Nat := if d = .encrypt then r else 15 - r

theorem kaddr : ∀ c < 3, ∀ d : Direction, ∀ r < 16,
    BitVec.ofNat 32 (keyOff c d) + BitVec.ofNat 32 r * δ d = BitVec.ofNat 32 (8 * (16 * c + ix d r)) := by
  intro c hc d r hr
  cases d
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 32 (keyOff c .encrypt) + BitVec.ofNat 32 r * δ .encrypt =
      BitVec.ofNat 32 (8 * (16 * c + ix .encrypt r))) c hc r hr
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 32 (keyOff c .decrypt) + BitVec.ofNat 32 r * δ .decrypt =
      BitVec.ofNat 32 (8 * (16 * c + ix .decrypt r))) c hc r hr

theorem kptr_succ (a₀ δ : BitVec 32) (r : Nat) :
    a₀ + BitVec.ofNat 32 r * δ + δ = a₀ + BitVec.ofNat 32 (r + 1) * δ := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul]
  exact congrArg (fun t => a₀ + (BitVec.ofNat 32 r * δ + t)) (BitVec.one_mul δ).symm

/-- The keys of a pass: those at `P + r δ`. -/
def keyOf (m : Mem) (P δ : BitVec 32) (r : Nat) : BitVec 48 := keyW m (P + BitVec.ofNat 32 r * δ)

/-- The pass's first key's pointer. -/
def passP (Sb : BitVec 32) (c : Nat) (d : Direction) : BitVec 32 := Sb + BitVec.ofNat 32 (keyOff c d)

theorem ix_lt (d : Direction) {r : Nat} (hr : r < 16) : ix d r < 16 := by
  unfold ix; split <;> omega_arith

theorem passKeyAt (Sb : BitVec 32) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    KeyAt Sb (passP Sb c d + BitVec.ofNat 32 r * δ d) := by
  have := ix_lt d hr
  refine ⟨16 * c + ix d r, by omega_using [hc, this], ?_⟩
  rw [passP, BitVec.add_assoc, kaddr c hc d r hr]

theorem keyOf_pass (m : Mem) {Sb : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) {c : Nat} (hc : c < 3)
    (d : Direction) {r : Nat} (hr : r < 16) :
    keyOf m (passP Sb c d) (δ d) r =
      roundKey (componentSchedule (scheduleAt m (Sb.setWidth 64)) c) d r := by
  have hi := ix_lt d hr
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl,
    componentSchedule_readW m _ _ _ hc hi, keyOf, keyW, passP, BitVec.add_assoc, kaddr c hc d r hr]
  exact congrArg (fun a => (m.readW a 64).setWidth 48) (addr_eq (by omega_using [hf, hc, hi]))

/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (Sb : BitVec 32) (c : Nat) (d : Direction) (m : Nat) (s : State) :
    Prop where
  le : m ≤ 8
  ptr : fw s kpSlot = passP Sb c d + BitVec.ofNat 32 (2 * m) * δ d
  cnt : fw s cntSlot = BitVec.ofNat 32 (8 - m)
  wds : ∀ x < 64, words s x =
    VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP Sb c d) (δ d)) m (words s₀) x
  kept : Kept 82 s₀ s

theorem pair_step {s₀ : State} (h₀ : Room s₀) {Sb : BitVec 32} (hs₀ : Sched s₀ Sb) {c : Nat}
    (hc : c < 3) {d : Direction} {m : Nat} (hm : m < 8) {s : State} (I : PairInv s₀ Sb c d m s) :
    WP isa (.block (roundPair d)) s fun s' =>
      PairInv s₀ Sb c d (m + 1) s' ∧ s'.zf = some (decide (m + 1 = 8)) := by
  have h : Room s := I.kept.room h₀
  have hs : Sched s Sb := I.kept.sched hs₀
  have hk₁ := passKeyAt Sb hc d (r := 2 * m) (by omega_using [hm])
  have hk₂ := passKeyAt Sb hc d (r := 2 * m + 1) (by omega_using [hm])
  rw [← kptr_succ] at hk₂
  refine WP.mono (roundPair_ok d h hs hk₁ hk₂ I.ptr) fun s' ⟨w, p80, p81, pz, k⟩ => ?_
  have rk : ∀ r < 16, keyW s.mem (passP Sb c d + BitVec.ofNat 32 r * δ d) =
      keyW s₀.mem (passP Sb c d + BitVec.ofNat 32 r * δ d) := fun r hr =>
    keyW_frame hs₀ (passKeyAt Sb hc d hr) (by decide) I.kept.frame
  have cnt : fw s cntSlot - 1 = BitVec.ofNat 32 (8 - (m + 1)) := by
    rw [I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 32 (8 - m) - 1 = BitVec.ofNat 32 (8 - (m + 1))) m hm
  refine ⟨⟨by omega_using [hm], ?_, by rw [p81, cnt], fun x hx => ?_, I.kept.trans k⟩, ?_⟩
  · rw [p80, kptr_succ, kptr_succ]; congr 3
  · have e : passP Sb c d + BitVec.ofNat 32 (2 * m) * δ d + δ d =
        passP Sb c d + BitVec.ofNat 32 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega_using [hm]), rk _ (by omega_using [hm])]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · rw [pz, cnt]
    exact congrArg some
      ((by decide : ∀ m < 8, (BitVec.ofNat 32 (8 - (m + 1)) == 0) = decide (m + 1 = 8)) m hm)

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) {Sb : BitVec 32} (hs₀ : Sched s₀ Sb) {c : Nat}
    (hc : c < 3) (d : Direction) {s : State} (I : PairInv s₀ Sb c d 0 s) :
    WP isa (.loop (.block (roundPair d)) .ne) s (PairInv s₀ Sb c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ Sb c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  refine WP.mono (pair_step h₀ hs₀ hc hm J) fun v' ⟨J', z⟩ => ?_
  rw [eval_ne, z]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], 8 - (m + 1), by omega_using [hm, hn], m + 1, by omega_using [hm, e], rfl, J'⟩

theorem passStart_ok (c : Nat) (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32}
    (hS : fw s schedSlot = Sb) :
    WP isa (.block (passStart c d)) s (PairInv s Sb c d 0) := by
  unfold passStart
  refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h (by decide)) fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebp = s.gpr .ebp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stm (B := s.gpr .ebp) b₂ (by rw [u₂.wr, u₁.wr]; exact slot_in h (by decide)) fun s₃ u₃ => ?_
  have p : s₂.gpr .eax = passP Sb c d := by rw [u₂.gpr, u₁.gpr, passP, ← hS]; rfl
  have m₃ : s₃.mem = s.mem.writeW (wordAddr (s.gpr .ebp) kpSlot) (passP Sb c d) := by
    rw [u₃.mem, u₂.mem, u₁.mem, p]
  have k₃ : Kept 82 s s₃ := ⟨by rw [u₃.gpr]; exact b₂,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], by rw [m₃]; exact stFw_frame h (k := kpSlot) (by decide) (by decide) _⟩
  have h₃ : Room s₃ := k₃.room h
  refine wp_movi fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .ebp = s₃.gpr .ebp := u₄.other _ (by decide)
  refine wp_stm (B := s₃.gpr .ebp) b₄ (by rw [u₄.wr]; exact slot_in h₃ (by decide)) fun s₅ u₅ =>
    WP.block_nil ?_
  have m₅ : s₅.mem = s₃.mem.writeW (wordAddr (s₃.gpr .ebp) cntSlot) (8 : BitVec 32) := by
    rw [u₅.mem, u₄.mem, u₄.gpr]
  have k₅ : Kept 82 s₃ s₅ := ⟨by rw [u₅.gpr]; exact b₄, by rw [u₅.gpr, u₄.other _ (by decide)],
    by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr],
    by rw [m₅]; exact stFw_frame h₃ (k := cntSlot) (by decide) (by decide) _⟩
  have z : BitVec.ofNat 32 (2 * 0) * δ d = 0#32 := by cases d <;> decide
  have f : ∀ j, j < wsWords → fw s₅ j =
      if j = cntSlot then 8 else if j = kpSlot then passP Sb c d else fw s j := by
    intro j hj
    rw [fw_write h₃ m₅ k₅.ebp (by decide) hj]
    by_cases e : j = cntSlot
    · rw [ite_eq_left e, ite_eq_left e]
    rw [ite_eq_right e, ite_eq_right e, fw_write h m₃ k₃.ebp (by decide) hj]
  refine ⟨by decide, ?_, ?_, fun x hx => ?_, k₃.trans k₅⟩
  · rw [f kpSlot (by decide), z, BitVec.add_zero]; rfl
  · rw [f cntSlot (by decide)]; rfl
  · rw [words, f _ (by unfold spills wsWords; omega_using [hx]),
      ite_eq_right (by unfold spills cntSlot; omega_using [hx]),
      ite_eq_right (by unfold spills kpSlot; omega_using [hx])]
    rfl

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32}
    (hs : Sched s Sb) (hS : fw s schedSlot = Sb) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x =
        passW (componentSchedule (scheduleAt s.mem (Sb.setWidth 64)) c) d (words s) x) ∧
      Kept 82 s s' := by
  unfold pass
  apply WP.seq
  refine WP.mono (passStart_ok c d h hS) fun s₁ I0 => ?_
  apply WP.seq
  refine WP.mono (pairLoop_ok h hs hc d I0) fun v J => ?_
  have hv : Room v := J.kept.room h
  obtain ⟨v', run, w, g, sp, rd, wr, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, J.kept.trans ⟨g, sp, rd, wr, headR_mono (by decide) f⟩⟩
  rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
  refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
  rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8
    (fun r hr => keyOf_pass _ hs.fit hc d hr)]

/-! ## The three passes -/

theorem scheduleAt_frame {s : State} {Sb : BitVec 32} (hs : Sched s Sb) {n : Nat} (hn : n ≤ wsWords)
    {m : Mem} (hf : Frame [headR s n] s.mem m) :
    scheduleAt m (Sb.setWidth 64) = scheduleAt s.mem (Sb.setWidth 64) :=
  VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

theorem passes_ok (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32} (hs : Sched s Sb)
    (hS : fw s schedSlot = Sb) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (Sb.setWidth 64)) d (words s) x) ∧
      Kept 82 s s' := by
  have step : ∀ (c : Nat) (_ : c < 3) (d' : Direction) {u : State}, Kept 82 s u →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (Sb.setWidth 64)) c) d' (words u) x) → Kept 82 u u' → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u ku Q hQ
    have hu : Room u := ku.room h
    have hsu : Sched u Sb := ku.sched hs
    refine WP.mono (pass_ok c hc d' hu hsu ((ku.fw h (by decide) (by decide)).trans hS))
      fun u' ⟨w, k⟩ => hQ u' ?_ k
    rw [scheduleAt_frame hs (by decide) ku.frame] at w; exact w
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ (Kept.refl _ _) fun u₁ w₁ k₁ => ?_
    apply WP.seq
    refine step _ (by decide) _ k₁ fun u₂ w₂ k₂ => ?_
    refine step _ (by decide) _ (k₁.trans k₂) fun u₃ w₃ k₃ => ⟨fun x hx => ?_, (k₁.trans k₂).trans k₃⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.X86.Bitsliced
