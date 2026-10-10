import VerifiedGarbage.Proof.TripleDes.X86.RoundLit
import VerifiedGarbage.Proof.TripleDes.X86.Linear
import VerifiedGarbage.Impl.TripleDes.X86.Sbox
import VerifiedGarbage.Impl.TripleDes.X86.Permutation
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-! ## `RoundCheck` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

noncomputable def inputLiterals : Array (Prog isa) :=
  #[input0.lit, input1.lit, input2.lit, input3.lit, input4.lit, input5.lit, input6.lit, input7.lit]
noncomputable def outputLiterals : Array (Prog isa) :=
  #[output0.lit, output1.lit, output2.lit, output3.lit, output4.lit, output5.lit, output6.lit, output7.lit]
def inputCfg : Cfg := { base := .ebp, slots := 128, ext := .edx, exts := 2 }
def inputEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .edi then some (inWord 0) else none, slot := fun _ => none }
def inputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 32 + (47 - k)]
  else []
def inputPost (i : Nat) (e : Env (Nat × Nat)) : Bool :=
  linSlotPost 128 7 ((List.range 6).map fun j => (16 + j, inputBits i j)) e

theorem input_check : ∀ i < 8,
    check (lanes 32 7) inputCfg (linExt 1)
      (instrs (inputLiterals.getD i (.block []))) inputEnv (inputPost i) = true := by
  decide +kernel

def outputCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }
def outputEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .esi then some (inWord 4) else none,
    slot := fun k => if 16 ≤ k ∧ k < 20 then some (inWord (k - 16)) else none }
def outputBits (i p : Nat) : List Nat :=
  [128 + p] ++ (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then [32 * j] else []
def outputPost (i : Nat) (e : Env (Nat × Nat)) : Bool :=
  linPost 8 [(.esi, outputBits i)] e
theorem output_check : ∀ i < 8,
    check (lanes 32 8) outputCfg (fun _ => none)
      (instrs (outputLiterals.getD i (.block []))) outputEnv (outputPost i) = true := by
  decide +kernel
end VG.Proof.TripleDes.X86

end

/-! ## `RoundInput` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem inputLiteral_eq : ∀ i < 8,
    inputLiterals.getD i (.block []) = .block (sboxInputBits i)
  | 0, _ => input0.lit_eq.symm
  | 1, _ => input1.lit_eq.symm
  | 2, _ => input2.lit_eq.symm
  | 3, _ => input3.lit_eq.symm
  | 4, _ => input4.lit_eq.symm
  | 5, _ => input5.lit_eq.symm
  | 6, _ => input6.lit_eq.symm
  | 7, _ => input7.lit_eq.symm
  | n + 8, h => by omega

theorem inputEnv_eq : inputEnv = linEnv [(.edi, 0)] := by
  unfold inputEnv linEnv
  congr 1
  funext r; cases r <;> rfl

def roundInputs (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then s.gpr .edi
  else s.mem.readW (wordAddr (s.gpr .edx) (i - 1)) 32

theorem roundInput_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok inputCfg s) :
    ∃ s', runBlock isa (sboxInputBits i) s = some s' ∧
      (∀ j < 6, ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p =
          xorBits (roundInputs s) (inputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, ((sboxInputBits i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) ∧ Frame [slotRegion inputCfg s] s.mem s'.mem := by
  have h := input_check i hi
  rw [inputLiteral_eq i hi] at h
  change check _ _ _ (sboxInputBits i) inputEnv (inputPost i) = true at h
  rw [inputEnv_eq] at h
  obtain ⟨s', run, out, rd, wr, keep, frame⟩ :=
    linear_slots_ok h hok (roundInputs s) (fun r k hk => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨by decide, rfl⟩) (fun j hj => by
        refine ⟨?_, ?_⟩
        · simp only [inputCfg] at hj; omega
        · simp only [inputCfg, roundInputs, Nat.add_eq_zero_iff, Nat.one_ne_zero,
            false_and, ite_false, Nat.add_sub_cancel_left])
  refine ⟨s', run, fun j hj p hp => ?_, rd, wr, keep, frame⟩
  exact out (16 + j) (inputBits i j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
end VG.Proof.TripleDes.X86

end

/-! ## `RoundOutput` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem outputLiteral_eq : ∀ i < 8,
    outputLiterals.getD i (.block []) = .block (sboxOutputs i)
  | 0, _ => output0.lit_eq.symm
  | 1, _ => output1.lit_eq.symm
  | 2, _ => output2.lit_eq.symm
  | 3, _ => output3.lit_eq.symm
  | 4, _ => output4.lit_eq.symm
  | 5, _ => output5.lit_eq.symm
  | 6, _ => output6.lit_eq.symm
  | 7, _ => output7.lit_eq.symm
  | n + 8, h => by omega

def roundOutputs (s : State) (i : Nat) : BitVec 32 :=
  if i = 4 then s.gpr .esi
  else s.mem.readW (wordAddr (s.gpr .ebp) (16 + i)) 32

theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok outputCfg s) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 32, (s'.gpr .esi).getLsbD p =
        xorBits (roundOutputs s) (outputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, ((sboxOutputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) ∧ Frame [slotRegion outputCfg s] s.mem s'.mem := by
  have h := output_check i hi
  rw [outputLiteral_eq i hi] at h
  change check _ _ _ (sboxOutputs i) outputEnv (outputPost i) = true at h
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ h
  have hrel : Rel (LaneRel 8 (assign (roundOutputs s) 256)) outputCfg
      (fun _ => none) outputEnv s := by
    refine ⟨fun r a h => ?_, fun j a hj h => ?_, fun _ _ _ h => by cases h⟩
    · simp only [outputEnv] at h
      split at h
      · rename_i hr; subst r; cases h
        have hr := inWord_rel (roundOutputs s) (i := 4) (k := 8) (by decide)
        exact hr
      · cases h
    · simp only [outputEnv] at h
      split at h
      · rename_i hb; cases h
        have heq : 16 + (j - 16) = j := by omega
        have hne : j - 16 ≠ 4 := by omega
        have hr := inWord_rel (roundOutputs s) (i := j - 16) (k := 8) (by omega)
        simpa only [roundOutputs, hne, ite_false, heq, outputCfg] using hr
      · cases h
  obtain ⟨s', hs', post⟩ := run lanes_sound hok hrel he
  have ho := List.all_eq_true.mp hpost (.esi, outputBits i) (by simp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at ho
  refine ⟨s', hs', ?_, post.rd, post.wr,
    fun r hr => post.other r (by simp [hr]), post.frame⟩
  exact outWord_rel (fun p hp a ha => ho.2 p hp a ha) (post.rel.reg .esi _ ho.1)
end VG.Proof.TripleDes.X86

end

/-! ## `Lit` -/

section

namespace VG.Impl.TripleDes.X86

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

materialize_code initialPermutation
materialize_code finalPermutation
materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.X86

end

/-! ## `Sbox` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]
noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])
def sboxCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun _ => none,
    slot := fun k => if 16 ≤ k ∧ k < 22 then some (inputTable (k - 16)) else none }
def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.slot (16 + j) == some (outputTable i j)
theorem sbox_check : ∀ i < 8,
    check (table 32 64) sboxCfg (fun _ => none) (instrs (sboxLiteral i))
      sboxEnv (sboxPost i) = true := by
  lit_decide

def sboxWrites : List Reg := [.eax, .ebx, .ecx, .edx]
theorem sbox_preserves : ∀ i < 8,
    [Reg.esp, .ebp, .esi, .edi].all
      (fun r => (instrs (sboxLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p
theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k =
      (s.mem.readW (wordAddr (s.gpr .ebp) (16 + k)) 32).getLsbD p := by
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

/-- Every output bit, including allocated spills and memory operands. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p =
        (Spec.TripleDes.sBox i (inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral i) = sboxCode i := by rw [sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.slot (16 + j) = some (outputTable i j) := by
    intro j hj
    exact beq_iff_eq.mp (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
  have key : ∀ p < 32, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (inputAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨(fun _ _ h => by cases h), ?_,
      (fun _ _ _ h => by cases h)⟩ he
    intro k a hk h
    simp only [sboxEnv] at h
    split at h
    · rename_i hb
      cases h
      have hk6 : k - 16 < 6 := by omega
      have heq : 16 + (k - 16) = k := by omega
      simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
        inputAt_bit s p (k - 16) hk6, heq, sboxCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.slot (16 + j) _ (by simp [sboxCfg]; omega) (hout j hj)
    have hb := p₁.base
    simp only [TableRel, outputTable, testBit_tableOf, (inputAt s p).isLt,
      decide_true, Bool.true_and, sboxCfg] at h hb
    rw [hb, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.esp, .ebp, .esi, .edi] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]
end VG.Proof.TripleDes.X86

end
