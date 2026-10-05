import VerifiedGarbage.Impl.TripleDes.Arm.Sbox
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.TripleDes.Arm.Block
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Impl.TripleDes.Arm.Permutation
import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Arm.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Rc2.Arm.Key
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rc2.Arm.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.SboxTable`. -/
section

/-!
The code of the eight S-boxes as literals (`materialize_table`): the
literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read it rather than run the register
allocator that writes it again.
-/

namespace VG

materialize_table Impl.TripleDes.Arm.sboxCode 8

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.RoundLit`. -/
section

namespace VG.Impl.TripleDes.Arm

open VG.Arm

materialize_code sboxInputs0 := (.block (sboxInputs 0) : Prog isa)
materialize_code sboxInputs1 := (.block (sboxInputs 1) : Prog isa)
materialize_code sboxInputs2 := (.block (sboxInputs 2) : Prog isa)
materialize_code sboxInputs3 := (.block (sboxInputs 3) : Prog isa)
materialize_code sboxInputs4 := (.block (sboxInputs 4) : Prog isa)
materialize_code sboxInputs5 := (.block (sboxInputs 5) : Prog isa)
materialize_code sboxInputs6 := (.block (sboxInputs 6) : Prog isa)
materialize_code sboxInputs7 := (.block (sboxInputs 7) : Prog isa)
materialize_code sboxOutputs0 := (.block (sboxOutputs 0) : Prog isa)
materialize_code sboxOutputs1 := (.block (sboxOutputs 1) : Prog isa)
materialize_code sboxOutputs2 := (.block (sboxOutputs 2) : Prog isa)
materialize_code sboxOutputs3 := (.block (sboxOutputs 3) : Prog isa)
materialize_code sboxOutputs4 := (.block (sboxOutputs 4) : Prog isa)
materialize_code sboxOutputs5 := (.block (sboxOutputs 5) : Prog isa)
materialize_code sboxOutputs6 := (.block (sboxOutputs 6) : Prog isa)
materialize_code sboxOutputs7 := (.block (sboxOutputs 7) : Prog isa)

end VG.Impl.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Lit`. -/
section

namespace VG.Impl.TripleDes.Arm

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

end VG.Impl.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Sbox`. -/
section

/-!
# DES S-box machine-code correctness

Untrusted. The kernel checks each allocated scalar circuit on all 64
inputs, then the sound truth-table evaluator lifts that check to every
bit position of arbitrary 32-bit words. This verifies both the circuits
and the allocator's output, including spills.
-/

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])

def sboxCfg : Cfg := { base := .r2, slots := 128, ext := .r2, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => q k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.reg (q j) == some (outputTable i j)

theorem sbox_check : ∀ i < 8,
    VG.Arm.Straight.check (table 32 64) VG.Proof.TripleDes.Arm.sboxCfg (fun _ => none) (instrs (VG.Proof.TripleDes.Arm.sboxLiteral i))
      VG.Proof.TripleDes.Arm.sboxEnv (VG.Proof.TripleDes.Arm.sboxPost i) = true := by
  lit_decide

def sboxWrites : List Reg := [.r4, .r5, .r6, .r7, .r8, .r12, .lr]

theorem sbox_preserves : ∀ i < 8,
    [Reg.r0, .r1, .r2, .r3, .r9, .r10, .r11].all
      (fun r => (instrs (VG.Proof.TripleDes.Arm.sboxLiteral i)).all fun op => dstOf op != some r) = true := by
  decide +kernel

def inputAt (s : VG.Arm.State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.gpr (q j)).getLsbD p

theorem inputAt_bit (s : VG.Arm.State) (p k : Nat) (hk : k < 6) :
    (VG.Proof.TripleDes.Arm.inputAt s p).toNat.testBit k = (s.gpr (q k)).getLsbD p := by
  simp only [VG.Proof.TripleDes.Arm.inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxLiteral_eq : ∀ i < 8, VG.Proof.TripleDes.Arm.sboxLiteral i = .block (sboxCode i)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

/-- Every S-box output bit, for arbitrary input words and any readable/
writable scratch state. Only the fixed scratch region can change. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : VG.Arm.State} (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 32, (s'.gpr (q j)).getLsbD p =
        (Spec.TripleDes.sBox i (VG.Proof.TripleDes.Arm.inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ VG.Proof.TripleDes.Arm.sboxWrites → s'.gpr r = s.gpr r) ∧
      VG.Frame [slotRegion VG.Proof.TripleDes.Arm.sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (VG.Proof.TripleDes.Arm.sboxLiteral i) = sboxCode i := by rw [VG.Proof.TripleDes.Arm.sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (VG.Proof.TripleDes.Arm.sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.reg (q j) = some (outputTable i j) := by
    intro j hj
    have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    exact beq_iff_eq.mp h
  have key : ∀ p < 32, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (VG.Proof.TripleDes.Arm.inputAt s p).toNat) VG.Proof.TripleDes.Arm.sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => dstOf op != some r) = false) := by
    intro p hp
    have hc := (VG.Proof.TripleDes.Arm.inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩ he
    simp only [VG.Proof.TripleDes.Arm.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      VG.Proof.TripleDes.Arm.inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel, outputTable, testBit_tableOf, (VG.Proof.TripleDes.Arm.inputAt s p).isLt,
      decide_true, Bool.true_and] at h
    rw [BitVec.ofNat_toNat] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.r0, .r1, .r2, .r3, .r9, .r10, .r11] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (VG.Proof.TripleDes.Arm.sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Round`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm

noncomputable def sboxInputsLiterals : Array (Prog isa) :=
  #[sboxInputs0.lit, sboxInputs1.lit, sboxInputs2.lit, sboxInputs3.lit, sboxInputs4.lit, sboxInputs5.lit, sboxInputs6.lit, sboxInputs7.lit]

noncomputable def sboxInputsLiteral (i : Nat) : Prog isa :=
  sboxInputsLiterals.getD i (.block [])

noncomputable def sboxOutputsLiterals : Array (Prog isa) :=
  #[sboxOutputs0.lit, sboxOutputs1.lit, sboxOutputs2.lit, sboxOutputs3.lit, sboxOutputs4.lit, sboxOutputs5.lit, sboxOutputs6.lit, sboxOutputs7.lit]

noncomputable def sboxOutputsLiteral (i : Nat) : Prog isa :=
  sboxOutputsLiterals.getD i (.block [])

def roundInputCfg : Cfg := { base := .r2, slots := 0, ext := .r0, exts := 2 }
def roundInputRegs : List (Reg × Nat) := [(.r11, 0)]

def roundInputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 32 + (47 - k)]
  else []

def roundInputPost (i : Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 6).map fun j => (q j, VG.Proof.TripleDes.Arm.roundInputBits i j)

theorem roundInput_check : ∀ i < 8,
    VG.Arm.Straight.check (lanes 32 7) VG.Proof.TripleDes.Arm.roundInputCfg (linExt 1) (instrs (VG.Proof.TripleDes.Arm.sboxInputsLiteral i))
      (linEnv VG.Proof.TripleDes.Arm.roundInputRegs) (linPost 7 (VG.Proof.TripleDes.Arm.roundInputPost i)) = true := by
  decide +kernel

def roundOutputCfg : Cfg := { base := .r2, slots := 0, ext := .r2, exts := 0 }
def roundOutputRegs : List (Reg × Nat) :=
  [(.r10, 0)] ++ (List.range 4).map fun j => (q j, j + 1)

def roundOutputBits (i p : Nat) : List Nat :=
  [p] ++ ((List.range 4).filterMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then some (32 * (j + 1)) else none)

theorem roundOutput_check : ∀ i < 8,
    VG.Arm.Straight.check (lanes 32 9) VG.Proof.TripleDes.Arm.roundOutputCfg (linExt 5) (instrs (VG.Proof.TripleDes.Arm.sboxOutputsLiteral i))
      (linEnv VG.Proof.TripleDes.Arm.roundOutputRegs) (linPost 9 [(.r10, VG.Proof.TripleDes.Arm.roundOutputBits i)]) = true := by
  decide +kernel

theorem sboxInputsLiteral_eq : ∀ i < 8,
    VG.Proof.TripleDes.Arm.sboxInputsLiteral i = .block (sboxInputs i)
  | 0, _ => sboxInputs0.lit_eq.symm
  | 1, _ => sboxInputs1.lit_eq.symm
  | 2, _ => sboxInputs2.lit_eq.symm
  | 3, _ => sboxInputs3.lit_eq.symm
  | 4, _ => sboxInputs4.lit_eq.symm
  | 5, _ => sboxInputs5.lit_eq.symm
  | 6, _ => sboxInputs6.lit_eq.symm
  | 7, _ => sboxInputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundInputCfg_ok (s : VG.Arm.State)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) : Ok VG.Proof.TripleDes.Arm.roundInputCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.Arm.roundInputCfg] at hk
  · exact hread
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega
  · intro k hk; simp [VG.Proof.TripleDes.Arm.roundInputCfg] at hk

/-- The extraction block reads just one round key and forms six Boolean
input words. It does not change memory, access permissions or other registers. -/
theorem roundInput_ok (i : Nat) (hi : i < 8) (s : VG.Arm.State)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      (∀ j < 6, ∀ p < 32, (s'.gpr (q j)).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .r11
          else s.mem.readW (wordAddr (s.gpr .r0) (k - 1)) 32) (VG.Proof.TripleDes.Arm.roundInputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := VG.Proof.TripleDes.Arm.roundInput_check i hi
  rw [VG.Proof.TripleDes.Arm.sboxInputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 32 := fun k =>
    if k = 0 then s.gpr .r11 else s.mem.readW (wordAddr (s.gpr .r0) (k - 1)) 32
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (VG.Proof.TripleDes.Arm.roundInputCfg_ok s hread) W (fun r k h => by
      simp only [VG.Proof.TripleDes.Arm.roundInputRegs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩) (fun j hj => by
      have hb : j < 2 := hj
      refine ⟨by omega, ?_⟩
      simp only [W, Nat.add_eq_zero_iff, Nat.one_ne_zero, false_and, ite_false, Nat.add_sub_cancel_left, VG.Proof.TripleDes.Arm.roundInputCfg])
  refine ⟨s', hs', fun j hj p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out (q j) (VG.Proof.TripleDes.Arm.roundInputBits i j)
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.Arm.roundInputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 32) (a : Nat) (ha : a < 32) :
    bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

def keyWord (s : VG.Arm.State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .r0) 1) 32 ++ s.mem.readW (wordAddr (s.gpr .r0) 0) 32

theorem bitOf_key (s : VG.Arm.State) (a : Nat) (ha : a < 64) :
    bitOf (fun k => if k = 0 then s.gpr .r11 else
      s.mem.readW (wordAddr (s.gpr .r0) (k - 1)) 32) (32 + a) =
    (VG.Proof.TripleDes.Arm.keyWord s).getLsbD a := by
  simp only [bitOf, VG.Proof.TripleDes.Arm.keyWord, BitVec.getLsbD_append]
  by_cases h : a < 32
  · have hd : (32 + a) / 32 = 1 := by omega
    simp only [h, ite_true, hd, Nat.add_mod_left, Nat.mod_eq_of_lt h]
    rfl
  · have hd : (32 + a) / 32 = 2 := by omega
    have hm : (32 + a) % 32 = a - 32 := by omega
    simp only [h, ite_false, hd, hm]
    rfl

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((Spec.TripleDes.permute Spec.TripleDes.expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 32) (k : BitVec 64) :
    (VG.Proof.TripleDes.Arm.roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
      (r.getLsbD (32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1) ^^
        k.getLsbD (47 - (6 * i + 5 - j))) := by
  have ht : 6 * (7 - i) + j < 48 := by omega
  have heq : 48 - 1 - (6 * (7 - i) + j) = 6 * i + 5 - j := by omega
  have hkey : 6 * (7 - i) + j = 47 - (6 * i + 5 - j) := by omega
  have hsource : 32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 := by
    have hb : ∀ t < 48, 1 ≤ Spec.TripleDes.expansion.getD t 1 := by decide +kernel
    have hpos : 6 * i + 5 - j < 48 := by omega
    have := hb _ hpos
    omega
  simp only [VG.Proof.TripleDes.Arm.roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [VG.Proof.TripleDes.permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : VG.Arm.State)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      VG.Proof.TripleDes.Arm.inputAt s' 0 = VG.Proof.TripleDes.Arm.roundChunk i ((s.gpr .r11).setWidth 32)
        ((VG.Proof.TripleDes.Arm.keyWord s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := VG.Proof.TripleDes.Arm.roundInput_ok i hi s hread
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.Proof.TripleDes.Arm.inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  rw [bits j hj 0 (by decide), VG.Proof.TripleDes.Arm.roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := VG.Proof.TripleDes.Arm.roundInput_bounds i hi j hj
  simp only [VG.Proof.TripleDes.Arm.roundInputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    VG.Proof.TripleDes.Arm.bitOf_low _ _ hr, VG.Proof.TripleDes.Arm.bitOf_key s _ hk, ite_true]

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if VG.Proof.TripleDes.Arm.boxSource p / 4 = i then
    b.getLsbD (3 - VG.Proof.TripleDes.Arm.boxSource p % 4) else false

theorem roundOutputBits_shape : ∀ i < 8, ∀ p < 32,
    VG.Proof.TripleDes.Arm.roundOutputBits i p = [p] ++
      (if p < 32 ∧ VG.Proof.TripleDes.Arm.boxSource p / 4 = i then
        [32 * (4 - VG.Proof.TripleDes.Arm.boxSource p % 4)] else []) := by
  decide +kernel

theorem sboxOutputsLiteral_eq : ∀ i < 8,
    VG.Proof.TripleDes.Arm.sboxOutputsLiteral i = .block (sboxOutputs i)
  | 0, _ => sboxOutputs0.lit_eq.symm
  | 1, _ => sboxOutputs1.lit_eq.symm
  | 2, _ => sboxOutputs2.lit_eq.symm
  | 3, _ => sboxOutputs3.lit_eq.symm
  | 4, _ => sboxOutputs4.lit_eq.symm
  | 5, _ => sboxOutputs5.lit_eq.symm
  | 6, _ => sboxOutputs6.lit_eq.symm
  | 7, _ => sboxOutputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundOutputCfg_ok (s : VG.Arm.State) : Ok VG.Proof.TripleDes.Arm.roundOutputCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.Arm.roundOutputCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.Arm.roundOutputCfg] at hk
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega
  · intro k hk; simp [VG.Proof.TripleDes.Arm.roundOutputCfg] at hk

/-- Deposit the four low S-box bits into L, at P's fixed destinations. -/
theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : VG.Arm.State) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 32, (s'.gpr .r10).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .r10 else s.gpr (q (k - 1)))
          (VG.Proof.TripleDes.Arm.roundOutputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := VG.Proof.TripleDes.Arm.roundOutput_check i hi
  rw [VG.Proof.TripleDes.Arm.sboxOutputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 32 := fun k =>
    if k = 0 then s.gpr .r10 else s.gpr (q (k - 1))
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (VG.Proof.TripleDes.Arm.roundOutputCfg_ok s) W (fun r k h => by
      simp only [VG.Proof.TripleDes.Arm.roundOutputRegs, List.mem_append, List.mem_singleton,
        Prod.mk.injEq, List.mem_map, List.mem_range] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨j, hj, heq⟩
      · exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by omega, ?_⟩
        simp [W]) (fun j hj => by simp [VG.Proof.TripleDes.Arm.roundOutputCfg] at hj)
  refine ⟨s', hs', fun p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out .r10 (VG.Proof.TripleDes.Arm.roundOutputBits i) (by simp) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.Arm.roundOutputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem bitOf_word (W : Nat → BitVec 32) (j : Nat) :
    bitOf W (32 * j) = (W j).getLsbD 0 := by
  simp [bitOf]

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : VG.Arm.State) (b : BitVec 4)
    (hb : ∀ j < 4, (s.gpr (q j)).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .r10 = s.gpr .r10 ^^^ (VG.Proof.TripleDes.Arm.boxPiece i b).zeroExtend 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := VG.Proof.TripleDes.Arm.roundOutput_ok i hi s
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, VG.Proof.TripleDes.Arm.roundOutputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and]
  simp only [List.cons_append, List.nil_append, xorBits_cons, VG.Proof.TripleDes.Arm.bitOf_low _ _ hp, ite_true]
  by_cases h : p < 32 ∧ VG.Proof.TripleDes.Arm.boxSource p / 4 = i
  · simp only [h]
    have hj : 3 - VG.Proof.TripleDes.Arm.boxSource p % 4 < 4 := by omega
    simp
    rw [VG.Proof.TripleDes.Arm.bitOf_word]
    have hn : 4 - VG.Proof.TripleDes.Arm.boxSource p % 4 ≠ 0 := by omega
    have heq : 4 - VG.Proof.TripleDes.Arm.boxSource p % 4 - 1 = 3 - VG.Proof.TripleDes.Arm.boxSource p % 4 := by omega
    simp only [hn, ite_false, heq]
    rw [hb _ hj]
    simp only [VG.Proof.TripleDes.Arm.boxPiece, getLsbD_ofBits, h.1, h.2, decide_true, Bool.true_and, ite_true]
  · have hs : VG.Proof.TripleDes.Arm.boxSource p / 4 ≠ i := by omega
    simp only [hs, ite_false, xorBits_nil, VG.Proof.TripleDes.Arm.boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and, and_false]

def roundKept : List Reg := [.r0, .r1, .r2, .r3, .r9, .r11]

theorem roundInput_keeps : ∀ i < 8, (.r10 :: VG.Proof.TripleDes.Arm.roundKept).all
    (fun r => (instrs (VG.Proof.TripleDes.Arm.sboxInputsLiteral i)).all fun op => dstOf op != some r) = true := by
  decide +kernel

theorem roundOutput_keeps : ∀ i < 8, roundKept.all
    (fun r => (instrs (VG.Proof.TripleDes.Arm.sboxOutputsLiteral i)).all fun op => dstOf op != some r) = true := by
  decide +kernel

theorem roundInput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ .r10 :: VG.Proof.TripleDes.Arm.roundKept) :
    (sboxInputs i).all (fun op => dstOf op != some r) = true := by
  have h := List.all_eq_true.mp (VG.Proof.TripleDes.Arm.roundInput_keeps i hi) r hr
  rw [VG.Proof.TripleDes.Arm.sboxInputsLiteral_eq i hi] at h
  exact h

theorem roundOutput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ VG.Proof.TripleDes.Arm.roundKept) :
    (sboxOutputs i).all (fun op => dstOf op != some r) = true := by
  have h := List.all_eq_true.mp (VG.Proof.TripleDes.Arm.roundOutput_keeps i hi) r hr
  rw [VG.Proof.TripleDes.Arm.sboxOutputsLiteral_eq i hi] at h
  exact h

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Spills`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def spillRegion (s : VG.Arm.State) : Region := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 60, 388⟩
def spillSafe : Instr → Bool
  | .mov d _ | .dp _ d _ _ | .ldr d _ _ => d != .r2
  | .str _ n off => decide (n = .r2 ∧ 60 ≤ off ∧ off + 4 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (VG.Proof.TripleDes.Arm.sboxLiteral i)).all VG.Proof.TripleDes.Arm.spillSafe = true := by decide +kernel

theorem write_frame (s : VG.Arm.State) (d : Reg) (v : BitVec 32) (hd : d ≠ .r2) :
    (s.setReg d v).gpr .r2 = s.gpr .r2 ∧ VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem (s.setReg d v).mem :=
  ⟨gpr_setReg_of_ne _ _ (Ne.symm hd), by rw [mem_setReg]; exact Frame.refl _ _⟩

theorem spillStep_frame (i : Instr) (s s' : VG.Arm.State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (h : VG.Proof.TripleDes.Arm.spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .r2 = s.gpr .r2 ∧ VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [VG.Proof.TripleDes.Arm.spillSafe, Bool.false_eq_true] at h
  case mov d op2 =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact VG.Proof.TripleDes.Arm.write_frame _ _ _ hd
  case dp op d n op2 =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact VG.Proof.TripleDes.Arm.write_frame _ _ _ hd
  case ldr d n off =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact VG.Proof.TripleDes.Arm.write_frame _ _ _ hd
  case str t n off =>
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    simp only [State.store32] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    rw [addr_add (by omega_using [fit, hhi])]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr (s.gpr .r2)) (by omega) (by omega) (by decide))

theorem spillBlock_frame (is : List Instr) (s s' : VG.Arm.State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (hsafe : is.all VG.Proof.TripleDes.Arm.spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .r2 = s.gpr .r2 ∧ VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  induction is generalizing s with
  | nil =>
    rw [runBlock_nil] at he
    obtain rfl := Option.some.inj he
    exact ⟨rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hsafe
    rw [runBlock_cons] at he
    change (exec i s).bind (runBlock isa is) = some s' at he
    obtain ⟨s₁, hi, hrest⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hg, hf⟩ := VG.Proof.TripleDes.Arm.spillStep_frame i s s₁ fit hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ (by rw [hg]; exact fit) hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : VG.Proof.TripleDes.Arm.spillRegion s₁ = VG.Proof.TripleDes.Arm.spillRegion s := by simp only [VG.Proof.TripleDes.Arm.spillRegion, hg]
    rw [hr] at hf'
    exact hf'

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : VG.Arm.State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  have h := VG.Proof.TripleDes.Arm.spillSafe_check i hi
  rw [VG.Proof.TripleDes.Arm.sboxLiteral_eq i hi] at h
  exact (VG.Proof.TripleDes.Arm.spillBlock_frame _ _ _ fit h he).2
end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Box`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm

theorem runBoxes_append (a b : List Instr) (s : VG.Arm.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- One complete DES S-box contribution, including E/key input extraction,
the Boolean circuit, and P output placement. -/
theorem box_ok (i : Nat) (hi : i < 8) (s : VG.Arm.State) (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .r10 = s.gpr .r10 ^^^
        (VG.Proof.TripleDes.Arm.boxPiece i (Spec.TripleDes.sBox i
          (VG.Proof.TripleDes.Arm.roundChunk i ((s.gpr .r11).setWidth 32)
            ((VG.Proof.TripleDes.Arm.keyWord s).setWidth 48)))).zeroExtend 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ VG.Proof.TripleDes.Arm.roundKept, s'.gpr r = s.gpr r) ∧
      VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, sp₁, mem₁, keep₁⟩ := VG.Proof.TripleDes.Arm.roundInput_chunk i hi s hread
  have kept₁ : ∀ r ∈ .r10 :: VG.Proof.TripleDes.Arm.roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (VG.Proof.TripleDes.Arm.roundInput_keep i hi r hr)
  have hok₁ : Ok VG.Proof.TripleDes.Arm.sboxCfg s₁ := hok.congr
    (kept₁ .r2 (by decide)) (kept₁ .r2 (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, sp₂, keep₂, _⟩ := VG.Proof.TripleDes.Arm.sbox_ok i hi hok₁
  have hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
      (Spec.TripleDes.sBox i (VG.Proof.TripleDes.Arm.roundChunk i ((s.gpr .r11).setWidth 32)
        ((VG.Proof.TripleDes.Arm.keyWord s).setWidth 48))).getLsbD j := by
    intro j hj
    rw [bits j hj 0 (by decide), chunk]
  obtain ⟨s₃, run₃, value, rd₃, wr₃, sp₃, mem₃, keep₃⟩ := VG.Proof.TripleDes.Arm.roundOutput_piece i hi s₂ _ hbits
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_, ?_⟩
  · simp only [box, VG.Proof.TripleDes.Arm.runBoxes_append, run₁, Option.bind_some, run₂, run₃]
  · rw [value, keep₂ .r10 (by decide), kept₁ .r10 (by decide)]
  · intro r hr
    rw [keep₃ r (VG.Proof.TripleDes.Arm.roundOutput_keep i hi r hr), keep₂ r ?_, kept₁ r (List.mem_cons_of_mem _ hr)]
    revert hr; cases r <;> decide
  · have hf := VG.Proof.TripleDes.Arm.sbox_spillFrame i hi s₁ s₂ hok₁.slots run₂
    have hregion : VG.Proof.TripleDes.Arm.spillRegion s₁ = VG.Proof.TripleDes.Arm.spillRegion s := by
      simp only [VG.Proof.TripleDes.Arm.spillRegion, kept₁ .r2 (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.RoundFunction`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Bitslice VG.Spec.TripleDes

theorem boxSource_shape : ∀ j < 32,
    7 - (32 - p.getD (31 - j) 1) / 4 = VG.Proof.TripleDes.Arm.boxSource j / 4 ∧
    (32 - p.getD (31 - j) 1) % 4 = 3 - VG.Proof.TripleDes.Arm.boxSource j % 4 ∧
    VG.Proof.TripleDes.Arm.boxSource j / 4 < 8 := by
  decide +kernel

theorem boxPiece_round_bit (i : Nat) (r : BitVec 32) (k : BitVec 48)
    (j : Nat) (hj : j < 32) :
    (VG.Proof.TripleDes.Arm.boxPiece i (sBox i (VG.Proof.TripleDes.Arm.roundChunk i r k))).getLsbD j =
      if VG.Proof.TripleDes.Arm.boxSource j / 4 = i then (roundFunction r k).getLsbD j else false := by
  simp only [VG.Proof.TripleDes.Arm.boxPiece, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  by_cases heq : VG.Proof.TripleDes.Arm.boxSource j / 4 = i
  · simp only [heq, ite_true]
    rw [VG.Proof.TripleDes.roundFunction_bit r k j hj]
    obtain ⟨hidx, hbit, _⟩ := VG.Proof.TripleDes.Arm.boxSource_shape j hj
    simp only [hidx, hbit, heq, VG.Proof.TripleDes.Arm.roundChunk]
  · simp only [heq, ite_false]

theorem foldl_xor_bits (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) (j : Nat) :
    (xs.foldl (fun out i => out ^^^ f i) a).getLsbD j =
      xs.foldl (fun out i => out ^^ (f i).getLsbD j) (a.getLsbD j) := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons, ih, BitVec.getLsbD_xor]

theorem select_xor : ∀ n < 8, ∀ b : Bool,
    (List.range 8).foldl (fun out i => out ^^ (if n = i then b else false)) false = b := by
  decide +kernel

/-- The eight S-box contributions give the standard DES round function. -/
theorem boxPieces_eq_roundFunction (r : BitVec 32) (k : BitVec 48) :
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.Arm.boxPiece i (sBox i (VG.Proof.TripleDes.Arm.roundChunk i r k)))
      (0 : BitVec 32) = roundFunction r k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hfold : (fun (out : Bool) i => out ^^
      (VG.Proof.TripleDes.Arm.boxPiece i (sBox i (VG.Proof.TripleDes.Arm.roundChunk i r k))).getLsbD j) =
      (fun out i => out ^^ (if VG.Proof.TripleDes.Arm.boxSource j / 4 = i then
        (roundFunction r k).getLsbD j else false)) := by
    funext out i
    exact congrArg (fun b => out ^^ b) (VG.Proof.TripleDes.Arm.boxPiece_round_bit i r k j hj)
  have hbits := VG.Proof.TripleDes.Arm.foldl_xor_bits (List.range 8)
    (fun i => VG.Proof.TripleDes.Arm.boxPiece i (sBox i (VG.Proof.TripleDes.Arm.roundChunk i r k))) 0 j
  have hz : (0 : BitVec 32).getLsbD j = false := by
    change (BitVec.ofNat 32 0).getLsbD j = false
    exact BitVec.getLsbD_zero
  have hinit := congrArg (fun b : Bool => (List.range 8).foldl
    (fun out i => out ^^ (VG.Proof.TripleDes.Arm.boxPiece i (sBox i (VG.Proof.TripleDes.Arm.roundChunk i r k))).getLsbD j) b) hz
  have hchange := congrArg
    (fun f : Bool → Nat → Bool => (List.range 8).foldl f false) hfold
  exact hbits.trans (hinit.trans (hchange.trans (VG.Proof.TripleDes.Arm.select_xor _ (VG.Proof.TripleDes.Arm.boxSource_shape j hj).2.2 _)))

theorem foldl_xor_start (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) :
    xs.foldl (fun out i => out ^^^ f i) a =
      a ^^^ xs.foldl (fun out i => out ^^^ f i) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons]
    have hz : (0 : BitVec 32) ^^^ f i = f i := BitVec.zero_xor
    rw [hz, ih (a ^^^ f i), ih (f i)]
    exact BitVec.xor_assoc _ _ _

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.RoundBody`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  (VG.Proof.TripleDes.Arm.boxPiece i (Spec.TripleDes.sBox i
    (VG.Proof.TripleDes.Arm.roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 32

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : VG.Arm.State) (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg s)
    (hr : s.gpr .r11 = r) (hk : VG.Proof.TripleDes.Arm.keyWord s = k)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .r10 = indices.foldl (fun out i => out ^^^ VG.Proof.TripleDes.Arm.contribution r k i) (s.gpr .r10) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ VG.Proof.TripleDes.Arm.roundKept, s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.Arm.box_ok i hi s hok hread
    have hregion : VG.Proof.TripleDes.Arm.spillRegion s₁ = VG.Proof.TripleDes.Arm.spillRegion s := by
      simp only [VG.Proof.TripleDes.Arm.spillRegion, keep₁ .r2 (by decide)]
    have hr₁ : s₁.gpr .r11 = r := (keep₁ .r11 (by decide)).trans hr
    have hword (j : Nat) (hj : j < 2) :
        s₁.mem.readW (wordAddr (s₁.gpr .r0) j) 32 = s.mem.readW (wordAddr (s.gpr .r0) j) 32 := by
      rw [keep₁ .r0 (by decide)]
      apply frame₁.readW (r := ⟨wordAddr (s.gpr .r0) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj) (by decide)
    have hk₁ : VG.Proof.TripleDes.Arm.keyWord s₁ = k := by
      unfold VG.Proof.TripleDes.Arm.keyWord
      rw [hword 0 (by decide), hword 1 (by decide)]
      exact hk
    have hread₁ : ∀ j < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .r0) j) 4 := by
      rw [rd₁, wr₁, keep₁ .r0 (by decide)]
      exact hread
    have hsep₁ : ∀ j < 2, (⟨wordAddr (s₁.gpr .r0) j, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s₁) := by
      rw [keep₁ .r0 (by decide), hregion]
      exact hsep
    have hok₁ : Ok VG.Proof.TripleDes.Arm.sboxCfg s₁ := hok.congr
      (keep₁ .r2 (by decide)) (keep₁ .r2 (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, sp₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, VG.Proof.TripleDes.Arm.runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .r10 = s.gpr .r10 ^^^ VG.Proof.TripleDes.Arm.contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.Arm.contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [VG.Proof.TripleDes.Arm.foldl_xor_start]
  exact congrArg (l ^^^ ·) (by
    simpa only [VG.Proof.TripleDes.Arm.contribution, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq] using
      VG.Proof.TripleDes.Arm.boxPieces_eq_roundFunction r (k.setWidth 48))

def roundOuterKept : List Reg := [.r0, .r1, .r2, .r3, .r9]

theorem swapHalves_ok (s : VG.Arm.State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r10 = s.gpr .r11 ∧ s'.gpr .r11 = s.gpr .r10 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ VG.Proof.TripleDes.Arm.roundOuterKept, s'.gpr q = s.gpr q) := by
  open VG.Arm.RegUpd in
  refine ⟨_, by
    simp only [swapHalves, VG.Impl.TripleDes.Arm.rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · simp only [mem_setReg]
  · intro q hq
    have hneq : q ≠ .lr ∧ q ≠ .r10 ∧ q ≠ .r11 := by revert hq; cases q <;> decide
    simp only [gpr_setReg, hneq.1, hneq.2.1, hneq.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : VG.Arm.State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : VG.Proof.TripleDes.Arm.keyWord s = k) (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ VG.Proof.TripleDes.Arm.roundOuterKept, s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.Arm.boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := VG.Proof.TripleDes.Arm.swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [roundBody, VG.Proof.TripleDes.Arm.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r11 (by decide)).trans hr)
  · rw [right, value, VG.Proof.TripleDes.Arm.contributions_roundFunction, hl]
  · intro q hq
    have hq' : q ∈ VG.Proof.TripleDes.Arm.roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.RoundStep`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (gpr_subFlags mem_subFlags)

def roundStepKept : List Reg := [.r1, .r2, .r3]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = s.gpr .r9 - 1 ∧
      s'.z = ((s.gpr .r9 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r0 → s'.gpr r = s.gpr r) := by
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, ite_true, reduceCtorEq, ite_false, runBlock_cons,
      exec, Op2.eval, encodable, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    z_setReg, subFlags, rd_setReg, wr_setReg, sp_setReg, mem_setReg]
  all_goals try rfl
  all_goals
    intro r hr₁ hr₂
    simp only [hr₁, hr₂, ite_false]

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : VG.Proof.TripleDes.Arm.keyWord s = k) (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s))
    (hcount : s.gpr .r9 = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    VG.Proof.TripleDes.Arm.roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, z₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := VG.Proof.TripleDes.Arm.roundAdvance_ok d s₁
  obtain ⟨hsub, hzero⟩ := VG.Proof.TripleDes.Arm.countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .r9 = BitVec.ofNat 32 n := (keep₁ .r9 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [VG.Proof.TripleDes.Arm.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r10 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r11 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r0 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.Arm.eval .ne s₂ = _
    simp only [VG.Arm.eval, z₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ VG.Proof.TripleDes.Arm.roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .r9 ∧ q ≠ .r0 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Loop`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : BitVec 32) (direction : Direction) (j : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (8 * (if direction = .encrypt then j else 15 - j))

def readKey (m : Mem) (ptr : BitVec 32) : BitVec 64 :=
  m.readW (wordAddr ptr 1) 32 ++ m.readW (wordAddr ptr 0) 32

theorem readKey_frame {m m' : Mem} {ptr : BitVec 32} {regions : List Region}
    (hf : VG.Frame regions m m')
    (sep : ∀ j < 2, ∀ r ∈ regions, (⟨wordAddr ptr j, 4⟩ : Region).Disjoint r) :
    VG.Proof.TripleDes.Arm.readKey m' ptr = VG.Proof.TripleDes.Arm.readKey m ptr := by
  exact congrArg₂ (fun hi lo : BitVec 32 => hi ++ lo)
    (hf.readW (a := wordAddr ptr 1) (w := 32) (r := ⟨wordAddr ptr 1, 4⟩)
      (Region.contains_self _ _) (sep 1 (by decide)) (by decide))
    (hf.readW (a := wordAddr ptr 0) (w := 32) (r := ⟨wordAddr ptr 0, 4⟩)
      (Region.contains_self _ _) (sep 0 (by decide)) (by decide))

theorem keyAddr_step (base : BitVec 32) (direction : Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then VG.Proof.TripleDes.Arm.keyAddr base direction j + 8
      else VG.Proof.TripleDes.Arm.keyAddr base direction j - 8) = VG.Proof.TripleDes.Arm.keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · change base + BitVec.ofNat 32 (8 * (15 - j)) - BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (15 - (j + 1)))
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

def endPointer (base : BitVec 32) (d : Direction) : BitVec 32 :=
  if d = .encrypt then base + 128 else base - 8

theorem keyAddr_end (base : BitVec 32) (d : Direction) :
    (if d = .encrypt then VG.Proof.TripleDes.Arm.keyAddr base d 15 + 8 else VG.Proof.TripleDes.Arm.keyAddr base d 15 - 8) = VG.Proof.TripleDes.Arm.endPointer base d := by
  cases d <;> simp only [VG.Proof.TripleDes.Arm.endPointer, VG.Proof.TripleDes.Arm.keyAddr, reduceCtorEq, ite_true, ite_false, Nat.reduceSub, Nat.reduceMul]
  · change base + BitVec.ofNat 32 120 + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 128
    rw [Offset.add_ofNat_add_ofNat]
  · rw [BitVec.add_zero]

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r10 = (roundPrefix keys direction (16 - n) v).1
  right : s.gpr .r11 = (roundPrefix keys direction (16 - n) v).2
  counter : s.gpr .r9 = BitVec.ofNat 32 n
  pointer : s.gpr .r0 = VG.Proof.TripleDes.Arm.keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).1
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).2
  counter : s.gpr .r9 = 0
  pointer : s.gpr .r0 = VG.Proof.TripleDes.Arm.endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg origin)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion origin))
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.Arm.readKey origin.mem (VG.Proof.TripleDes.Arm.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : VG.Proof.TripleDes.Arm.LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ VG.Proof.TripleDes.Arm.LoopPost keys direction base origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, VG.Proof.TripleDes.Arm.LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : VG.Proof.TripleDes.Arm.spillRegion s = VG.Proof.TripleDes.Arm.spillRegion origin := by
    simp only [VG.Proof.TripleDes.Arm.spillRegion, hs.regs .r2 (by decide)]
  have hokS : Ok VG.Proof.TripleDes.Arm.sboxCfg s := hok.congr
    (hs.regs .r2 (by decide)) (hs.regs .r2 (by decide)) hs.rd hs.wr
  have hreadS : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) t) 4 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hsepS : ∀ t < 2, (⟨wordAddr (s.gpr .r0) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s) := by
    rw [hs.pointer, hwork]; exact hsep _ hj
  have hk : (VG.Proof.TripleDes.Arm.keyWord s).setWidth 48 = roundKey keys direction (16 - n) := by
    change (VG.Proof.TripleDes.Arm.readKey s.mem (s.gpr .r0)).setWidth 48 = _
    rw [hs.pointer]
    have hmem := VG.Proof.TripleDes.Arm.readKey_frame hs.frame (ptr := VG.Proof.TripleDes.Arm.keyAddr base direction (16 - n))
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep _ hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, sp, regs, frame⟩ :=
    VG.Proof.TripleDes.Arm.roundStep_ok direction s _ _ (VG.Proof.TripleDes.Arm.keyWord s) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r10 = (roundPrefix keys direction (16 - (n - 1)) v).1 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r11 = (roundPrefix keys direction (16 - (n - 1)) v).2 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key)) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, by
        rw [ptr, hs.pointer]
        exact VG.Proof.TripleDes.Arm.keyAddr_end base direction, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, VG.Proof.TripleDes.Arm.keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = VG.Proof.TripleDes.Arm.keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion origin))
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.Arm.readKey origin.mem (VG.Proof.TripleDes.Arm.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (VG.Proof.TripleDes.Arm.LoopPost keys direction base origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := VG.Proof.TripleDes.Arm.LoopPost keys direction base origin v) (VG.Proof.TripleDes.Arm.LoopInv keys direction base origin v)
    (VG.Proof.TripleDes.Arm.loopStep keys direction base origin v hok hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.PassStart`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def startPointer (ptr : BitVec 32) (offset : Int) : BitVec 32 :=
  if offset < 0 then ptr - BitVec.ofNat 32 offset.natAbs else ptr + BitVec.ofNat 32 offset.natAbs

theorem passOffset_encodable : ∀ offset ∈ ([0, 120, 136, 376, -120, -136] : List Int),
    encodable (BitVec.ofNat 32 offset.natAbs) = true := by decide +kernel

theorem passStart_ok (offset : Int) (s : State)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true) :
    ∃ s', runBlock isa (passStart offset) s = some s' ∧
      s'.gpr .r0 = VG.Proof.TripleDes.Arm.startPointer (s.gpr .r0) offset ∧ s'.gpr .r9 = 16 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r9 → s'.gpr r = s.gpr r) := by
  by_cases h : offset < 0
  all_goals refine ⟨(s.setReg .r0 (VG.Proof.TripleDes.Arm.startPointer (s.gpr .r0) offset)).setReg .r9 16, by
    simp only [passStart, h, ite_true, ite_false, runBlock_cons, exec, Op2.eval, ho, ite_true,
      Option.map_some, imm, runStep_some, VG.Proof.TripleDes.Arm.startPointer]
    rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals try simp only [gpr_setReg, VG.Proof.TripleDes.Arm.startPointer, h, ite_true, ite_false, reduceCtorEq]
  all_goals try rfl
  all_goals
    intro r hr₀ hr₉
    simp only [hr₀, hr₉, ite_false]
end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Pass`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).2
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).1
  pointer : s.gpr .r0 = VG.Proof.TripleDes.Arm.endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = VG.Proof.TripleDes.Arm.keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion origin))
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.Arm.readKey origin.mem (VG.Proof.TripleDes.Arm.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      (.block swapHalves)) origin (VG.Proof.TripleDes.Arm.PassPost keys direction base origin v) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.Arm.roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, sp, mem, regs⟩ := VG.Proof.TripleDes.Arm.swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, (regs .r0 (by decide)).trans hs.pointer,
    rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, ?_, ?_⟩
  · intro q hq
    have hkeep : ∀ r ∈ VG.Proof.TripleDes.Arm.roundStepKept, r ∈ VG.Proof.TripleDes.Arm.roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


theorem pass_ok (offset : Int) (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.Arm.sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : VG.Proof.TripleDes.Arm.startPointer (origin.gpr .r0) offset =
      VG.Proof.TripleDes.Arm.keyAddr base direction 0)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion origin))
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.Arm.readKey origin.mem (VG.Proof.TripleDes.Arm.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass offset direction) origin (VG.Proof.TripleDes.Arm.PassPost keys direction base origin v) := by
  obtain ⟨s, run, ptr, count, mem, rd, wr, sp, regs⟩ := VG.Proof.TripleDes.Arm.passStart_ok offset origin ho
  have hbase : s.gpr .r2 = origin.gpr .r2 := regs .r2 (by decide) (by decide)
  have hwork : VG.Proof.TripleDes.Arm.spillRegion s = VG.Proof.TripleDes.Arm.spillRegion origin := by simp only [VG.Proof.TripleDes.Arm.spillRegion, hbase]
  have hkeysS : ∀ j < 16, (VG.Proof.TripleDes.Arm.readKey s.mem (VG.Proof.TripleDes.Arm.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j := by rw [mem]; exact hkeys
  have hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t) 4 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s) := by
    rw [hwork]; exact hsep
  have htail := VG.Proof.TripleDes.Arm.roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .r10 (by decide) (by decide)).trans hl)
    ((regs .r11 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) count hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.pointer, hs.rd.trans rd, hs.wr.trans wr, hs.sp.trans sp, ?_, ?_⟩
  · intro q hq
    have hneq : ∀ r ∈ VG.Proof.TripleDes.Arm.roundStepKept, r ≠ .r9 ∧ r ≠ .r0 := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).2 (hneq q hq).1)
  · have hf := hs.frame
    rw [hwork, mem] at hf
    exact hf

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.WordState`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .r10 = ((x >>> 32).setWidth 32)
  right : s.gpr .r11 = (x.setWidth 32)

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {base : BitVec 32} {origin s : State} {x : BitVec 64}
    (hs : VG.Proof.TripleDes.Arm.PassPost keys direction base origin ((x >>> 32).setWidth 32, x.setWidth 32) s) :
    VG.Proof.TripleDes.Arm.WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32) = halves.2 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_left halves.2 halves.1)
  have hright : ((desCore keys direction x).setWidth 32) = halves.1 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_right halves.2 halves.1)
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Ready`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok VG.Proof.TripleDes.Arm.sboxCfg s
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (VG.Proof.TripleDes.Arm.readKey s.mem (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : VG.Proof.TripleDes.Arm.Ready keys base s) (hbase : t.gpr .r2 = s.gpr .r2)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem t.mem) : VG.Proof.TripleDes.Arm.Ready keys base t := by
  have hwork : VG.Proof.TripleDes.Arm.spillRegion t = VG.Proof.TripleDes.Arm.spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := VG.Proof.TripleDes.Arm.readKey_frame hf (ptr := VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion origin] origin.mem s.mem

theorem Stable.refl (s : State) : VG.Proof.TripleDes.Arm.Stable s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : State} (hs : VG.Proof.TripleDes.Arm.Stable s t) (ht : VG.Proof.TripleDes.Arm.Stable t u) : VG.Proof.TripleDes.Arm.Stable s u := by
  have hwork : VG.Proof.TripleDes.Arm.spillRegion t = VG.Proof.TripleDes.Arm.spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) (hs.regs .r2 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (offset : Int)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (hptr : VG.Proof.TripleDes.Arm.startPointer (s.gpr .r0) offset = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d 0)
    (hready : VG.Proof.TripleDes.Arm.Ready keys base s) (hword : VG.Proof.TripleDes.Arm.WordState x s) :
    WP isa (pass offset d) s (fun t => VG.Proof.TripleDes.Arm.WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      VG.Proof.TripleDes.Arm.Ready keys base t ∧ VG.Proof.TripleDes.Arm.Stable s t ∧ t.gpr .r0 = VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base c) d) := by
  apply WP.mono (VG.Proof.TripleDes.Arm.pass_ok offset ho (keys c) d (VG.Proof.TripleDes.Arm.componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr (ht.regs .r2 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩, ht.pointer⟩

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Body`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (o₀ o₁ o₂ : Int)
    (e₀ : encodable (BitVec.ofNat 32 o₀.natAbs) = true)
    (e₁ : encodable (BitVec.ofNat 32 o₁.natAbs) = true)
    (e₂ : encodable (BitVec.ofNat 32 o₂.natAbs) = true)
    (p₀ : VG.Proof.TripleDes.Arm.startPointer (s.gpr .r0) o₀ = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c₀) d₀ 0)
    (p₁ : VG.Proof.TripleDes.Arm.startPointer (VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base c₀) d₀) o₁ = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c₁) d₁ 0)
    (p₂ : VG.Proof.TripleDes.Arm.startPointer (VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base c₁) d₁) o₂ = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c₂) d₂ 0)
    (hready : VG.Proof.TripleDes.Arm.Ready keys base s) (hword : VG.Proof.TripleDes.Arm.WordState x s) :
    WP isa (.seq (pass o₀ d₀) (.seq (pass o₁ d₁) (pass o₂ d₂))) s
      (fun t => VG.Proof.TripleDes.Arm.WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        VG.Proof.TripleDes.Arm.Ready keys base t ∧ VG.Proof.TripleDes.Arm.Stable s t ∧ t.gpr .r0 = VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base c₂) d₂) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.Arm.pass_word_ok keys base s x c₀ h₀ d₀ o₀ e₀ p₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.Arm.pass_word_ok keys base s₁ _ c₁ h₁ d₁ o₁ e₁
    (by rw [hs₁.2.2.2]; exact p₁) hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (VG.Proof.TripleDes.Arm.pass_word_ok keys base s₂ _ c₂ h₂ d₂ o₂ e₂
    (by rw [hs₂.2.2.2]; exact p₂) hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1,
    hs₁.2.2.1.trans (hs₂.2.2.1.trans hs₃.2.2.1), hs₃.2.2.2⟩

theorem passPointers (base : BitVec 32) :
    VG.Proof.TripleDes.Arm.startPointer base 0 = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base 0) .encrypt 0 ∧
    VG.Proof.TripleDes.Arm.startPointer (VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base 0) .encrypt) 120 = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base 1) .decrypt 0 ∧
    VG.Proof.TripleDes.Arm.startPointer (VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base 1) .decrypt) 136 = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base 2) .encrypt 0 ∧
    VG.Proof.TripleDes.Arm.startPointer base 376 = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base 2) .decrypt 0 ∧
    VG.Proof.TripleDes.Arm.startPointer (VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base 2) .decrypt) (-120) = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base 1) .encrypt 0 ∧
    VG.Proof.TripleDes.Arm.startPointer (VG.Proof.TripleDes.Arm.endPointer (VG.Proof.TripleDes.Arm.componentBase base 1) .encrypt) (-136) = VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base 0) .decrypt 0 := by
  simp only [VG.Proof.TripleDes.Arm.startPointer, VG.Proof.TripleDes.Arm.endPointer, VG.Proof.TripleDes.Arm.componentBase, VG.Proof.TripleDes.Arm.keyAddr,
    Int.reduceLT, Int.natAbs_neg, ite_true, ite_false, reduceCtorEq,
    Nat.reduceMul, Nat.reduceSub]
  repeat' constructor <;> bv_omega

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hptr : s.gpr .r0 = base)
    (hready : VG.Proof.TripleDes.Arm.Ready keys base s) (hword : VG.Proof.TripleDes.Arm.WordState x s) :
    WP isa (blockBody direction) s
      (fun t => VG.Proof.TripleDes.Arm.WordState (VG.Proof.TripleDes.Arm.blockCore keys direction x) t ∧ VG.Proof.TripleDes.Arm.Ready keys base t ∧ VG.Proof.TripleDes.Arm.Stable s t ∧
        t.gpr .r0 = (if direction = .encrypt then base + 384 else base - 8)) := by
  obtain ⟨p₀, p₁, p₂, p₃, p₄, p₅⟩ := VG.Proof.TripleDes.Arm.passPointers base
  cases direction
  · apply WP.mono (VG.Proof.TripleDes.Arm.threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt 0 120 136 (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₀) p₁ p₂ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change base + BitVec.ofNat 32 256 + BitVec.ofNat 32 128 = base + BitVec.ofNat 32 384
    rw [Offset.add_ofNat_add_ofNat]
  · apply WP.mono (VG.Proof.TripleDes.Arm.threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt 376 (-120) (-136) (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₃) p₄ p₅ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change (base + 0) - 8 = base - 8
    exact congrArg (· - (8 : BitVec 32)) (BitVec.add_zero base)
end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Permutation`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm

def permutationCfg : Cfg := { base := .r2, slots := 0, ext := .r2, exts := 0 }
def permutationInputs (lo hi : Reg) : List (Reg × Nat) := [(lo, 0), (hi, 1)]
def permutationBits {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit start p : Nat) : List Nat :=
  if p < dstSplit ∧ start + p < m then
    let source := n - positions.getD (m - 1 - (start + p)) 1
    [if source < srcSplit then source else 32 + source - srcSplit]
  else []
def permutationOutputs {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit : Nat) (lo hi : Reg) :
    List (Reg × (Nat → List Nat)) :=
  [(lo, VG.Proof.TripleDes.Arm.permutationBits positions n srcSplit dstSplit 0),
   (hi, VG.Proof.TripleDes.Arm.permutationBits positions n srcSplit (m - dstSplit) dstSplit)]

theorem initialPermutation_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.TripleDes.Arm.permutationCfg (linExt 2) (instrs initialPermutation.lit)
      (linEnv (VG.Proof.TripleDes.Arm.permutationInputs .r5 .r4)) (linPost 6 (VG.Proof.TripleDes.Arm.permutationOutputs Spec.TripleDes.ip 64 32 32 .r11 .r10)) = true := by
  decide +kernel

theorem finalPermutation_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.TripleDes.Arm.permutationCfg (linExt 2) (instrs finalPermutation.lit)
      (linEnv (VG.Proof.TripleDes.Arm.permutationInputs .r11 .r10)) (linPost 6 (VG.Proof.TripleDes.Arm.permutationOutputs Spec.TripleDes.fp 64 32 32 .r5 .r4)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.TripleDes.Arm.permutationCfg (linExt 2) (instrs keyPermutation1.lit)
      (linEnv (VG.Proof.TripleDes.Arm.permutationInputs .r5 .r4)) (linPost 6 (VG.Proof.TripleDes.Arm.permutationOutputs Spec.TripleDes.pc1 64 32 28 .r11 .r10)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.TripleDes.Arm.permutationCfg (linExt 2) (instrs keyPermutation2.lit)
      (linEnv (VG.Proof.TripleDes.Arm.permutationInputs .r11 .r10)) (linPost 6 (VG.Proof.TripleDes.Arm.permutationOutputs Spec.TripleDes.pc2 56 28 32 .r4 .r5)) = true := by
  decide +kernel

def packedInput (n split : Nat) (lo hi : BitVec 32) : BitVec n :=
  ((hi.setWidth (n - split)) ++ lo.setWidth split).setWidth n

theorem packedInput_bit (n split : Nat) (lo hi : BitVec 32) (k : Nat)
    (hk : k < n) (hs : split ≤ n) :
    (VG.Proof.TripleDes.Arm.packedInput n split lo hi).getLsbD k =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split) := by
  simp only [VG.Proof.TripleDes.Arm.packedInput, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : k < split
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · have hb : k - split < n - split := by omega
    simp only [h, ite_false, hb, decide_true, Bool.true_and]

theorem permutationBits_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split width start : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32)
    (hw : width + start ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (lo hi : BitVec 32) (p : Nat) (hp : p < 32) :
    xorBits (fun i => if i = 0 then lo else hi)
      (VG.Proof.TripleDes.Arm.permutationBits positions n split width start p) =
    (((Spec.TripleDes.permute positions (VG.Proof.TripleDes.Arm.packedInput n split lo hi) >>> start).setWidth width).setWidth 32).getLsbD p := by
  simp only [BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
  by_cases hw' : p < width
  · have hm : start + p < m := by omega
    simp only [hw', decide_true, Bool.true_and]
    have hk : m - 1 - (start + p) < m := by omega
    obtain ⟨hb, ht⟩ := bounds _ hk
    have hn' : n - positions.getD (m - 1 - (start + p)) 1 < n := by omega
    rw [VG.Proof.TripleDes.permute_bit positions _ hn _ hm, VG.Proof.TripleDes.Arm.packedInput_bit _ _ _ _ _ hn' hs]
    simp only [VG.Proof.TripleDes.Arm.permutationBits, hw', hm, and_self, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false]
    let k := n - positions.getD (m - 1 - (start + p)) 1
    change bitOf (fun i => if i = 0 then lo else hi) (if k < split then k else 32 + k - split) =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split)
    by_cases h : k < split
    · have h32 : k < 32 := by omega
      simp only [h, ite_true, bitOf, Nat.div_eq_of_lt h32, Nat.mod_eq_of_lt h32]
    · have h32 : k - split < 32 := by change n - positions.getD (m - 1 - (start + p)) 1 < n at hn'; dsimp [k]; omega
      have he : 32 + k - split = 32 * 1 + (k - split) := by omega
      simp only [h, ite_false, he, VG.Arm.Straight.bitOf_word _ _ _ h32]
      rfl
  · simp only [hw', decide_false, Bool.false_and, VG.Proof.TripleDes.Arm.permutationBits, false_and, ite_false, xorBits_nil]

theorem permutationCfg_ok (s : VG.Arm.State) : Ok VG.Proof.TripleDes.Arm.permutationCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.Arm.permutationCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.Arm.permutationCfg] at hk
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega
  · intro k hk; simp [VG.Proof.TripleDes.Arm.permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split dstSplit : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32) (hd : dstSplit ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (srcLo srcHi dstLo dstHi : Reg) (is : List Instr)
    (hchk : VG.Arm.Straight.check (lanes 32 6) VG.Proof.TripleDes.Arm.permutationCfg (linExt 2) is
      (linEnv (VG.Proof.TripleDes.Arm.permutationInputs srcLo srcHi))
      (linPost 6 (VG.Proof.TripleDes.Arm.permutationOutputs positions n split dstSplit dstLo dstHi)) = true)
    (s : VG.Arm.State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dstLo = ((Spec.TripleDes.permute positions
        (VG.Proof.TripleDes.Arm.packedInput n split (s.gpr srcLo) (s.gpr srcHi))).setWidth dstSplit).setWidth 32 ∧
      s'.gpr dstHi = ((Spec.TripleDes.permute positions
        (VG.Proof.TripleDes.Arm.packedInput n split (s.gpr srcLo) (s.gpr srcHi)) >>> dstSplit).setWidth (m - dstSplit)).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => dstOf op != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr srcLo else s.gpr srcHi
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ :=
    linear_ok hchk (VG.Proof.TripleDes.Arm.permutationCfg_ok s) W (fun r i h => by
      simp only [VG.Proof.TripleDes.Arm.permutationInputs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [VG.Proof.TripleDes.Arm.permutationCfg] at hj)
  refine ⟨s', hs', ?_, ?_, rd, wr, sp, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstLo (VG.Proof.TripleDes.Arm.permutationBits positions n split dstSplit 0) (by simp [VG.Proof.TripleDes.Arm.permutationOutputs]) p hp
    rw [h]
    have hbits := VG.Proof.TripleDes.Arm.permutationBits_ok positions hn split dstSplit 0 hs hlo hhi (by omega) bounds (s.gpr srcLo) (s.gpr srcHi) p hp
    simpa only [BitVec.ushiftRight_zero] using hbits
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstHi (VG.Proof.TripleDes.Arm.permutationBits positions n split (m - dstSplit) dstSplit)
      (by simp [VG.Proof.TripleDes.Arm.permutationOutputs]) p hp
    rw [h]
    exact VG.Proof.TripleDes.Arm.permutationBits_ok positions hn split (m - dstSplit) dstSplit hs hlo hhi
      (by omega) bounds _ _ p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.Arm.permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Bytes`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt m p) = rev (m.readW p 32) ++ rev (m.readW (p + 4) 32) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, rev_readW, rev_readW]
  simp only [VG.Proof.TripleDes.catBlock, VG.Spec.TripleDes.blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero,
    show (1 : Addr) + 1 = 2 from by decide,
    show (2 : Addr) + 1 = 3 from by decide,
    show (4 : Addr) + 1 = 5 from by decide,
    show (5 : Addr) + 1 = 6 from by decide,
    show (6 : Addr) + 1 = 7 from by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [BitVec.getLsbD_append, ite_eq_left, ite_eq_right,
      Nat.sub_sub] <;> rfl

theorem packed28 (c d : BitVec 28) :
    VG.Proof.TripleDes.Arm.packedInput 56 28 (d.setWidth 32) (c.setWidth 32) = c ++ d := by
  simp only [VG.Proof.TripleDes.Arm.packedInput, BitVec.setWidth_setWidth_of_le _ (by decide : 28 ≤ 32),
    BitVec.setWidth_eq]

theorem byteRev64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (byteRev64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have cases8 : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases cases8 i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [byteRev64, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
    BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]

theorem blockAt_writeW (m : Mem) (p : Addr) (x : BitVec 64) :
    VG.Spec.TripleDes.blockAt (m.writeW p (byteRev64 x)) p = VG.Spec.TripleDes.encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, VG.Spec.TripleDes.encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact VG.Proof.TripleDes.Arm.byteRev64_byte x i hi

theorem revPair (l r : BitVec 32) : rev r ++ rev l = byteRev64 (l ++ r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [rev, byteRev64, BitVec.getLsbD_append,
      BitVec.getLsbD_extractLsb', ite_eq_left, ite_eq_right, Nat.sub_sub] <;>
    congr 2 <;> omega

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Initial`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm

theorem initial_raw_ok (s : VG.Arm.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 32 32 .r11 .r10 .r5 .r4 .r12 .r9) s = some s' ∧
      s'.gpr .r11 = (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r4 ++ s.gpr .r5)).setWidth 32 ∧
      s'.gpr .r10 = ((Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r4 ++ s.gpr .r5)) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    VG.Proof.TripleDes.Arm.fixedPermutation_ok Spec.TripleDes.ip (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) VG.Proof.TripleDes.ip_bounds
      .r5 .r4 .r11 .r10 (instrs initialPermutation.lit) VG.Proof.TripleDes.Arm.initialPermutation_check s
  have hcode : permuteCode Spec.TripleDes.ip 64 32 32 .r11 .r10 .r5 .r4 .r12 .r9 = instrs initialPermutation.lit :=
    congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, ?_, rd, wr, sp, mem, regs⟩
  · simpa only [VG.Proof.TripleDes.Arm.packedInput, BitVec.setWidth_eq] using lo
  · simpa only [VG.Proof.TripleDes.Arm.packedInput, BitVec.setWidth_eq] using hi


theorem final_raw_ok (s : VG.Arm.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 32 32 .r5 .r4 .r11 .r10 .r12 .r9) s = some s' ∧
      s'.gpr .r5 = (Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r10 ++ s.gpr .r11)).setWidth 32 ∧
      s'.gpr .r4 = ((Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r10 ++ s.gpr .r11)) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    VG.Proof.TripleDes.Arm.fixedPermutation_ok Spec.TripleDes.fp (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) VG.Proof.TripleDes.fp_bounds
      .r11 .r10 .r5 .r4 (instrs finalPermutation.lit) VG.Proof.TripleDes.Arm.finalPermutation_check s
  have hcode : permuteCode Spec.TripleDes.fp 64 32 32 .r5 .r4 .r11 .r10 .r12 .r9 = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, ?_, rd, wr, sp, mem, regs⟩
  · simpa only [VG.Proof.TripleDes.Arm.packedInput, BitVec.setWidth_eq] using lo
  · simpa only [VG.Proof.TripleDes.Arm.packedInput, BitVec.setWidth_eq] using hi

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.BlockIO`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def loadKept : List Reg := [.r0, .r1, .r2, .r3]

theorem readDataWords_ok (s : VG.Arm.State) (offset : Nat) (ho : offset + 4 < 4096)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    ∃ s', runBlock isa [.ldr .r4 .r1 offset, .ldr .r5 .r1 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] s = some s' ∧
      s'.gpr .r4 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 32) ∧
      s'.gpr .r5 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 4 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 4 := by
    simpa only [Nat.mul_one] using hr 1 (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show offset < 4096 from by omega, h0, show offset + 4 < 4096 from ho, ite_true, State.load32,
      gpr_setReg, reduceCtorEq, ite_false, rd_setReg, wr_setReg, h1,
      Option.map_some, mem_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r h4 h5; simp only [gpr_setReg, h4, h5, ite_false]


theorem blockLoad_ok (s : VG.Arm.State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hread : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa VG.Impl.TripleDes.Arm.blockLoad s = some s' ∧
      s'.gpr .r10 = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))) >>> 32).setWidth 32 ∧
      s'.gpr .r11 = (Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ VG.Proof.TripleDes.Arm.loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, hi₁, lo₁, mem₁, rd₁, wr₁, sp₁, reg₁⟩ := VG.Proof.TripleDes.Arm.readDataWords_ok s 0 (by decide)
    (by simpa only [Nat.zero_add] using hread)
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := VG.Proof.TripleDes.Arm.initial_raw_ok s₁
  have input : s₁.gpr .r4 ++ s₁.gpr .r5 =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))) := by
    rw [hi₁, lo₁, VG.Proof.TripleDes.Arm.decodeBlock_readW]
    simp only [BitVec.add_zero, Nat.zero_add]
    rw [addr_add (by omega_using [fit])]
    rfl
  rw [input] at lo₂ hi₂
  refine ⟨s₂, ?_, hi₂, lo₂, mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · rw [VG.Impl.TripleDes.Arm.blockLoad, VG.Proof.TripleDes.Arm.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact sp₂.trans sp₁
  · intro r hr
    have checks : ∀ r ∈ VG.Proof.TripleDes.Arm.loadKept,
        ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true := by decide +kernel
    have unused : ∀ r ∈ VG.Proof.TripleDes.Arm.loadKept, r ≠ .r4 ∧ r ≠ .r5 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr).1 (unused r hr).2)

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Save`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (slotsOf)

theorem blockSave_eq : blockSave = (slotsOf VG.Impl.TripleDes.Arm.savedRegs).map (fun p => Instr.str p.1 .r2 p.2) := by
  rw [blockSave, slotsOf, List.map_map]; rfl

theorem blockRestore_eq : blockRestore = (slotsOf VG.Impl.TripleDes.Arm.savedRegs).map (fun p => Instr.ldr p.1 .r2 p.2) := by
  rw [blockRestore, slotsOf, List.map_map]; rfl

theorem slots_ok : Spill.Slots 0 36 (slotsOf VG.Impl.TripleDes.Arm.savedRegs) := by decide

theorem slot_index : ∀ p ∈ slotsOf VG.Impl.TripleDes.Arm.savedRegs, ∃ i < 9, p.2 = 4 * i := by decide

def Saved (original current : State) : Prop :=
  Spill.Saved current.mem (State.addr (current.gpr .r2)) original.gpr (slotsOf VG.Impl.TripleDes.Arm.savedRegs)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  sp : current.sp = original.sp
  saved : VG.Proof.TripleDes.Arm.Saved original current
  frame : VG.Frame [⟨State.addr (original.gpr .r2), 36⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockSave) s (VG.Proof.TripleDes.Arm.SavePost s) := by
  rw [VG.Proof.TripleDes.Arm.blockSave_eq, ← List.append_nil (List.map _ _)]
  refine Spill.save_ok _ s _ (fun p hp => ?_) (WP.block_nil ⟨rfl, rfl, rfl, rfl,
    Spill.saveMem_saved _ _ _ _ VG.Proof.TripleDes.Arm.slots_ok, Spill.saveMem_frame _ _ _ (by decide) _ (by decide)⟩)
  obtain ⟨i, hi, he⟩ := VG.Proof.TripleDes.Arm.slot_index p hp
  exact ⟨by omega, by omega, he ▸ hw i hi⟩

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ VG.Impl.TripleDes.Arm.savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.Arm.Keep VG.Impl.TripleDes.Arm.savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : VG.Proof.TripleDes.Arm.Saved original s)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (VG.Proof.TripleDes.Arm.RestorePost original s) := by
  rw [VG.Proof.TripleDes.Arm.blockRestore_eq, ← List.append_nil (List.map _ _)]
  have hregs : (slotsOf VG.Impl.TripleDes.Arm.savedRegs).map Prod.fst = VG.Impl.TripleDes.Arm.savedRegs := by decide
  refine Spill.restoreList_ok _ s _ (by decide) (fun p hp => ?_)
    fun s' hl ho hm hrd hwr hsp => WP.block_nil ⟨?_, ⟨fun r hr => ho r (hregs ▸ hr), hm, hrd, hwr⟩, hsp⟩
  · obtain ⟨i, hi, he⟩ := VG.Proof.TripleDes.Arm.slot_index p hp
    have hne : ∀ p ∈ slotsOf VG.Impl.TripleDes.Arm.savedRegs, p.1 ≠ .r2 := by decide
    exact ⟨hne p hp, by omega, by omega, he ▸ hread i hi⟩
  · exact Spill.restored_of (hsaved.restored hl) fun r hr => hregs ▸ hr

theorem Saved.congr {original s t : State} (hs : VG.Proof.TripleDes.Arm.Saved original s)
    (hbase : t.gpr .r2 = s.gpr .r2) (hf : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s] s.mem t.mem) :
    VG.Proof.TripleDes.Arm.Saved original t := by
  unfold VG.Proof.TripleDes.Arm.Saved; rw [hbase]
  exact Spill.Saved.frame hs VG.Proof.TripleDes.Arm.slots_ok hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Head`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨State.addr (s.gpr .r2), 36⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok VG.Proof.TripleDes.Arm.sboxCfg s
  scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  pointer : s.gpr .r0 = base
  saveRead : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  saveWrite : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  dataRead : ∀ t < 2, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4
  dataSeparate : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) t) 4
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (VG.Proof.TripleDes.Arm.readKey s.mem (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : VG.Proof.TripleDes.Arm.WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1))))) s
  ready : VG.Proof.TripleDes.Arm.Ready keys base s
  saved : VG.Proof.TripleDes.Arm.Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.loadKept, s.gpr q = original.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.Arm.saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hp : VG.Proof.TripleDes.Arm.HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : VG.Frame [VG.Proof.TripleDes.Arm.saveRegion s] s.mem t.mem) : VG.Proof.TripleDes.Arm.Ready keys base t := by
  have hbase : t.gpr .r2 = s.gpr .r2 := congrFun hg .r2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show VG.Proof.TripleDes.Arm.spillRegion t = VG.Proof.TripleDes.Arm.spillRegion s from
      congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hm := VG.Proof.TripleDes.Arm.readKey_frame hf (ptr := VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : VG.Proof.TripleDes.Arm.HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (VG.Proof.TripleDes.Arm.HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (VG.Proof.TripleDes.Arm.blockSave_ok s hp.scratchFit hp.saveWrite)
  intro s₁ hs₁
  have hready := VG.Proof.TripleDes.Arm.ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  have hread₁ : ∀ t < 2, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (State.addr (s₁.gpr .r1)) =
      Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ :=
    VG.Proof.TripleDes.Arm.blockLoad_ok s₁ (by rw [hs₁.gpr]; exact hp.dataFit) hread₁
  have hframe : VG.Frame [VG.Proof.TripleDes.Arm.spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .r2 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .r2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.WordStore`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [VG.Proof.TripleDes.Arm.getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem readW_pair (m : Mem) (p : Addr) :
    m.readW (p + 4) 32 ++ m.readW p 32 = m.readW p 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases hlo : i < 32
  · rw [ite_eq_left hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hlo, hi, decide_true, Bool.true_and]
    rw [VG.Proof.TripleDes.Arm.getLsbD_read m 4 p i (by omega), VG.Proof.TripleDes.Arm.getLsbD_read m 8 p i (by omega)]
  · rw [ite_eq_right hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hi,
      show i - 32 < 32 by omega, decide_true, Bool.true_and]
    rw [VG.Proof.TripleDes.Arm.getLsbD_read m 4 (p + 4) (i - 32) (by omega), VG.Proof.TripleDes.Arm.getLsbD_read m 8 p i (by omega)]
    have ha : 4 + (i - 32) / 8 = i / 8 := by omega
    have hb : (i - 32) % 8 = i % 8 := by omega
    rw [hb]
    exact congrArg (fun q => (m q).getLsbD (i % 8))
      ((VG.Offset.add_ofNat_add_ofNat p 4 ((i - 32) / 8)).trans
        (congrArg (fun j => p + BitVec.ofNat 64 j) ha))

theorem writeW_pair (m : Mem) (p : Addr) (lo hi : BitVec 32) :
    (m.writeW p lo).writeW (p + 4) hi = m.writeW p (hi ++ lo) := by
  funext a
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  by_cases hhi : (a - (p + 4)).toNat < 4
  · have he : (a - p).toNat = (a - (p + 4)).toNat + 4 := by bv_omega
    have hb : (a - p).toNat < 8 := by omega
    rw [ite_eq_left hhi, ite_eq_left hb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp (disch := omega) only [ite_eq_right, he]
    apply congrArg (fun b => decide (i < 8) && b)
    apply congrArg hi.getLsbD
    omega
  · rw [ite_eq_right hhi]
    by_cases hlo : (a - p).toNat < 4
    · have hb : (a - p).toNat < 8 := by omega
      rw [ite_eq_left hlo, ite_eq_left hb]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi'
      simp (disch := omega) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
        ite_eq_left]
    · have hb : ¬ (a - p).toNat < 8 := by bv_omega
      rw [ite_eq_right hlo, ite_eq_right hb]

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Store`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def storeTail (d : VG.Spec.TripleDes.Direction) : List Instr :=
  [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r1 0, .str .r5 .r1 4,
    .dp (if d = .encrypt then .sub else .add) .r0 .r0
      (.imm (if d = .encrypt then 384 else 8))]

theorem storeTail_ok (d : VG.Spec.TripleDes.Direction) (s : VG.Arm.State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (VG.Proof.TripleDes.Arm.storeTail d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (s.gpr .r4 ++ s.gpr .r5)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) 4 := by
    simpa only [Nat.mul_zero] using hw 0 (by decide)
  have h1 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 4)) 4 := by
    simpa only [Nat.mul_one] using hw 1 (by decide)
  cases d <;> refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, VG.Proof.TripleDes.Arm.storeTail,
      runBlock_cons, runStep_some, exec, State.store32, h0, h1,
      Op2.eval, gpr_setReg, mem_setReg, wr_setReg]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    rd_setReg, wr_setReg, sp_setReg]
  all_goals try
    simp only [mem_setReg, BitVec.add_zero]
    rw [addr_add (by omega_using [fit])]
    exact (VG.Proof.TripleDes.Arm.writeW_pair s.mem _ _ _).trans (congrArg (s.mem.writeW _) (VG.Proof.TripleDes.Arm.revPair _ _))
  all_goals
    intro r h0 h4 h5
    simp only [h0, h4, h5, ite_false]

theorem blockStore_ok (d : VG.Spec.TripleDes.Direction) (s : VG.Arm.State) (l r : BitVec 32)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (VG.Impl.TripleDes.Arm.blockStore d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ VG.Proof.TripleDes.Arm.loadKept, q ≠ .r0 → s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := VG.Proof.TripleDes.Arm.final_raw_ok s
  rw [hl, hr] at lo₁ hi₁
  have keeps : ∀ q ∈ VG.Proof.TripleDes.Arm.loadKept, s₁.gpr q = s.gpr q := by
    intro q hq
    have checks : ∀ q ∈ VG.Proof.TripleDes.Arm.loadKept,
        ((instrs finalPermutation.lit).all fun op => dstOf op != some q) = true := by decide +kernel
    exact reg₁ q (checks q hq)
  have fit₁ : (s₁.gpr .r1).toNat + 8 ≤ 2 ^ 32 := by rw [keeps .r1 (by decide)]; exact fit
  have hw₁ : ∀ t < 2, InRegions s₁.wr (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [wr₁, keeps .r1 (by decide)]; exact hw
  obtain ⟨s₂, run₂, mem₂, ptr₂, rd₂, wr₂, sp₂, reg₂⟩ := VG.Proof.TripleDes.Arm.storeTail_ok d s₁ fit₁ hw₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [VG.Impl.TripleDes.Arm.blockStore, ← VG.Proof.TripleDes.Arm.storeTail, VG.Proof.TripleDes.Arm.runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [mem₂, mem₁, keeps .r1 (by decide), hi₁, lo₁, VG.Proof.TripleDes.halves_append]
  · rw [ptr₂, keeps .r0 (by decide)]
  · intro q hq h0
    have unused : ∀ q ∈ VG.Proof.TripleDes.Arm.loadKept, q ≠ .r4 ∧ q ≠ .r5 := by decide
    exact (reg₂ q h0 (unused q hq).1 (unused q hq).2).trans (keeps q hq)

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Tail`. -/
section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

structure TailPost (original origin : State) (d : Direction) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (origin.gpr .r1)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ VG.Impl.TripleDes.Arm.savedRegs, s.gpr r = original.gpr r
  pointer : s.gpr .r0 = (if d = .encrypt then origin.gpr .r0 - 384 else origin.gpr .r0 + 8)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s.gpr q = origin.gpr q
  frame : VG.Frame [⟨State.addr (origin.gpr .r1), 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (d : Direction) (x : BitVec 64)
    (hword : VG.Proof.TripleDes.Arm.WordState x s) (hsaved : VG.Proof.TripleDes.Arm.Saved original s)
    (scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hsavedRead : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4)
    (hsep : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (VG.Proof.TripleDes.Arm.saveRegion s)) :
    WP isa (.block (blockStore d ++ blockRestore)) s (VG.Proof.TripleDes.Arm.TailPost original s d x) := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, mem₁, ptr₁, rd₁, wr₁, sp₁, reg₁⟩ := VG.Proof.TripleDes.Arm.blockStore_ok d s
    ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right dataFit hwrite
  rw [VG.Proof.TripleDes.halves_append] at mem₁
  have regs₁ : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s₁.gpr q = s.gpr q := by
    intro q hq
    have incl : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, q ∈ VG.Proof.TripleDes.Arm.loadKept ∧ q ≠ .r0 := by decide
    exact reg₁ q (incl q hq).1 (incl q hq).2
  have frame₁ : VG.Frame [⟨State.addr (s.gpr .r1), 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have saved₁ : VG.Proof.TripleDes.Arm.Saved original s₁ := by
    unfold VG.Proof.TripleDes.Arm.Saved; rw [regs₁ .r2 (by decide)]
    exact Spill.Saved.frame hsaved VG.Proof.TripleDes.Arm.slots_ok frame₁ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hsep.sub_right (Offset.sub_base _ (by decide))).symm
  have reads₁ : ∀ i < 9, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [rd₁, wr₁, regs₁ .r2 (by decide)]; exact hsavedRead
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (VG.Proof.TripleDes.Arm.blockRestore_ok original s₁ saved₁
    (by rw [regs₁ .r2 (by decide)]; exact scratchFit) reads₁)
  intro s₂ hs₂
  refine ⟨?_, hs₂.saved, ?_, hs₂.keep.rd.trans rd₁, hs₂.keep.wr.trans wr₁,
    hs₂.sp.trans sp₁, ?_, ?_⟩
  · rw [hs₂.keep.mem, mem₁]
    exact VG.Proof.TripleDes.Arm.blockAt_writeW s.mem _ _
  · exact (hs₂.keep.reg .r0 (by decide)).trans ptr₁
  · intro q hq
    have unused : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, q ∉ VG.Impl.TripleDes.Arm.savedRegs := by decide
    exact (hs₂.keep.reg q (unused q hq)).trans (regs₁ q hq)
  · rw [hs₂.keep.mem]; exact frame₁

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Block`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (VG.Proof.TripleDes.Arm.blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      VG.Proof.TripleDes.Arm.blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (original.gpr .r1)) =
    VG.Proof.TripleDes.Arm.blockResult keys direction (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1)))
  pointer : s.gpr .r0 = original.gpr .r0
  saved : ∀ r ∈ VG.Impl.TripleDes.Arm.savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s.gpr q = original.gpr q
  frame : VG.Frame (VG.Proof.TripleDes.Arm.blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (direction : Direction) (s : State)
    (hp : VG.Proof.TripleDes.Arm.HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (block direction) s (VG.Proof.TripleDes.Arm.BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.Arm.blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.Arm.blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction ((hs₁.regs .r0 (by decide)).trans hp.pointer) hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ VG.Proof.TripleDes.Arm.roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ VG.Proof.TripleDes.Arm.roundStepKept, r ∈ VG.Proof.TripleDes.Arm.loadKept := by decide
    exact (hs₂.2.2.1.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.1.regs .r2 (by decide)) hs₂.2.2.1.frame
  have savedRead₂ : ∀ i < 9, InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [hs₂.2.2.1.rd, hs₂.2.2.1.wr, hs₁.rd, hs₁.wr, hregs₂ .r2 (by decide)]
    exact hp.saveRead
  have hwrite₂ : ∀ t < 2, InRegions s₂.wr (State.addr (s₂.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₂.2.2.1.wr, hs₁.wr, hregs₂ .r1 (by decide)]
    exact hwrite
  apply WP.mono (VG.Proof.TripleDes.Arm.blockTail_ok s s₂ direction _ hs₂.1 saved₂
    (by rw [hregs₂ .r2 (by decide)]; exact hp.scratchFit)
    (by rw [hregs₂ .r1 (by decide)]; exact hp.dataFit) savedRead₂ hwrite₂
    (by rw [VG.Proof.TripleDes.Arm.saveRegion, hregs₂ .r1 (by decide), hregs₂ .r2 (by decide)]; exact hp.dataSeparate))
  intro s₃ hs₃
  refine ⟨?_, ?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.1.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.1.wr.trans hs₁.wr),
    hs₃.sp.trans (hs₂.2.2.1.sp.trans hs₁.sp),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .r1 (by decide)] at hresult
    exact hresult.trans (VG.Proof.TripleDes.Arm.blockResult_core keys direction _)
  · rw [hs₃.pointer, hs₂.2.2.2, hp.pointer]
    cases direction <;> simp only [reduceCtorEq, ite_true, ite_false,
      BitVec.add_sub_cancel, BitVec.sub_add_cancel]
  · have hf₁ : VG.Frame (VG.Proof.TripleDes.Arm.blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [VG.Proof.TripleDes.Arm.blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : VG.Frame (VG.Proof.TripleDes.Arm.blockRegions s) s₁.mem s₂.mem := hs₂.2.2.1.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [VG.Proof.TripleDes.Arm.blockRegions], ?_⟩
      have hbase := hs₁.regs .r2 (by decide)
      change Region.Sub ⟨State.addr (s₁.gpr .r2) + BitVec.ofNat 64 60, 388⟩ ⟨State.addr (s.gpr .r2), 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : VG.Frame (VG.Proof.TripleDes.Arm.blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .r1 (by decide)]
      exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp [VG.Proof.TripleDes.Arm.blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit`. -/
section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.Arm.roundBody
materialize_value Impl.TripleDes.Arm.blockLoad

/-! The functions. -/

materialize_code Impl.TripleDes.Arm.encryptBlock
materialize_code Impl.TripleDes.Arm.decryptBlock
materialize_code Impl.TripleDes.Arm.Key.expandKey
materialize_code Impl.TripleDes.Arm.Ecb.encrypt
materialize_code Impl.TripleDes.Arm.Ecb.decrypt

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.ConstantTime`. -/
section

/-! # Constant-time Triple DES block and key-expansion programs -/

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : VG.Arm.State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-! The analyses as summaries: the body of the loop of rounds, which each
block function runs three times (two of them in each direction), and the
block functions, which the ECB functions call. Both keep `r1`–`r3`, which
they do not write. -/

taint_summary roundEnc : taintS (Taint.ofRegs [.r0, .r1, .r2, .r9])
  (.block (roundBody ++ roundAdvance .encrypt)) keeping (Taint.ofRegs [.r1, .r2, .r3])
taint_summary roundDec : taintS (Taint.ofRegs [.r0, .r1, .r2, .r9])
  (.block (roundBody ++ roundAdvance .decrypt)) keeping (Taint.ofRegs [.r1, .r2, .r3])
taint_summary encSum : taintS (Taint.ofRegs [.r0, .r1, .r2]) VG.Impl.TripleDes.Arm.encryptBlock
  keeping (Taint.ofRegs [.r1, .r2, .r3]) using roundEnc roundDec
taint_summary decSum : taintS (Taint.ofRegs [.r0, .r1, .r2]) VG.Impl.TripleDes.Arm.decryptBlock
  keeping (Taint.ofRegs [.r1, .r2, .r3]) using roundEnc roundDec

theorem encryptBlock_constantTime (pre : VG.Arm.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2]) VG.Impl.TripleDes.Arm.encryptBlock := by
  obtain ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk (τ := Taint.ofRegs [.r0, .r1, .r2]) encSum (by decide +kernel)
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem decryptBlock_constantTime (pre : VG.Arm.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2]) VG.Impl.TripleDes.Arm.decryptBlock := by
  obtain ⟨_, h⟩ := VG.Taint.exists_check_of_sumOk (τ := Taint.ofRegs [.r0, .r1, .r2]) decSum (by decide +kernel)
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem expandKey_constantTime (pre : VG.Arm.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2, .r3]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem ecbEncrypt_constantTime (pre : VG.Arm.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2, .r3]) Ecb.encrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) Ecb.encrypt h).isSome = true := by
    taint_decide_sum [encSum, decSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

theorem ecbDecrypt_constantTime (pre : VG.Arm.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2, .r3]) Ecb.decrypt := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) Ecb.decrypt h).isSome = true := by
    taint_decide_sum [encSum, decSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_ h
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp.2

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.Pre`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 512 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    VG.Proof.TripleDes.Arm.blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))
  pub := VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : VG.Proof.TripleDes.Arm.selectedRound d j < 16 := by
  cases d <;> simp only [VG.Proof.TripleDes.Arm.selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : BitVec 32) (c : Nat) (d : Direction) (j : Nat) :
    VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j = base + BitVec.ofNat 32 (8 * (16 * c + VG.Proof.TripleDes.Arm.selectedRound d j)) := by
  unfold VG.Proof.TripleDes.Arm.keyAddr VG.Proof.TripleDes.Arm.componentBase VG.Proof.TripleDes.Arm.selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

theorem keyWordAddress (base : BitVec 32) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (c j t : Nat) (hc : c < 3) (hj : j < 16) (ht : t < 2) (d : Direction) :
    wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) t =
      State.addr base + BitVec.ofNat 64 (8 * (16 * c + VG.Proof.TripleDes.Arm.selectedRound d j) + 4 * t) := by
  have bound := VG.Proof.TripleDes.Arm.selectedRound_bound d j hj
  rw [wordAddr, VG.Proof.TripleDes.Arm.keyAddr_component, Offset.add_ofNat_add_ofNat,
    addr_add (by omega_using [fit, hc, bound, ht])]

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    VG.Proof.TripleDes.Arm.readKey m (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase base c) d j) =
      m.readW (State.addr base + BitVec.ofNat 64 (8 * (16 * c + VG.Proof.TripleDes.Arm.selectedRound d j))) 64 := by
  rw [VG.Proof.TripleDes.Arm.readKey, VG.Proof.TripleDes.Arm.keyWordAddress base fit c j 1 hc hj (by decide) d,
    VG.Proof.TripleDes.Arm.keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact VG.Proof.TripleDes.Arm.readW_pair m _

theorem headPre_of_contract (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.Arm.blockContract d).pre s) :
    VG.Proof.TripleDes.Arm.HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))))
      (s.gpr .r0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, keyFit, dataFit, scratchFit⟩ := hs
  have scratchWrites : ∀ i < 128, InRegions s.wr (wordAddr (s.gpr .r2) i) 4 := by
    intro i hi
    rw [wordAddr, addr_add (by omega_using [scratchFit, hi]), hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have scratchSaveWrites : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have scratchSaveReads : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := scratchSaveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have spills : Ok VG.Proof.TripleDes.Arm.sboxCfg s := by
    refine ⟨scratchWrites, ?_, scratchFit, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (VG.Proof.TripleDes.Arm.keyAddr (VG.Proof.TripleDes.Arm.componentBase (s.gpr .r0) c) direction j) t, 4⟩
        ⟨State.addr (s.gpr .r0), 384⟩ := by
    intro c hc direction j hj t ht
    rw [VG.Proof.TripleDes.Arm.keyWordAddress _ keyFit c j t hc hj ht direction]
    have bound := VG.Proof.TripleDes.Arm.selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, bound, ht])
  have workSub : Region.Sub (VG.Proof.TripleDes.Arm.spillRegion s) ⟨State.addr (s.gpr .r2), 512⟩ :=
    Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (VG.Proof.TripleDes.Arm.saveRegion s) ⟨State.addr (s.gpr .r2), 512⟩ :=
    Region.sub_prefix (by decide)
  refine ⟨spills, by omega_using [scratchFit], dataFit, rfl, scratchSaveReads,
    scratchSaveWrites, ?_, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [addr_add (by omega_using [dataFit, ht]), hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  · intro c hc direction j hj t ht
    rw [VG.Proof.TripleDes.Arm.keyWordAddress _ keyFit c j t hc hj ht direction, hrd, hwr]
    have bound := VG.Proof.TripleDes.Arm.selectedRound_bound direction j hj
    exact ⟨⟨State.addr (s.gpr .r0), 384⟩, by simp,
      Offset.contains_base _ (by omega_using [hc, bound, ht]) (by omega_using [hc, bound, ht])⟩
  · intro c hc direction j hj t ht
    exact (keySep.sub_left (keySub c hc direction j hj t ht)).sub_right workSub
  · intro c hc direction j hj t ht
    exact (keySep.sub_left (keySub c hc direction j hj t ht)).sub_right saveSub
  · intro c hc direction j hj
    rw [VG.Proof.TripleDes.Arm.readKey_component s.mem _ keyFit c j hc hj direction]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (State.addr (s.gpr .r0)) c
      (VG.Proof.TripleDes.Arm.selectedRound direction j) hc (VG.Proof.TripleDes.Arm.selectedRound_bound direction j hj)).symm

end VG.Proof.TripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.Arm.VerifiedBlock`. -/
section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.Arm.blockContract d).pre s) :
    WP isa (block d) s (fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧ (VG.Proof.TripleDes.Arm.blockContract d).post s s') := by
  have hp := VG.Proof.TripleDes.Arm.headPre_of_contract d s hs
  have hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    intro t ht
    have fit := hs.2.2.2.2.2.1
    rw [addr_add (by omega_using [fit, ht]), hs.2.1]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  apply WP.mono (VG.Proof.TripleDes.Arm.block_ok (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r0) d s hp hwrite)
  intro s' hpost
  refine ⟨⟨?_, hpost.sp⟩, hpost.result⟩
  intro r hr
  have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ VG.Proof.TripleDes.Arm.roundStepKept := by decide
  rcases hkeep r hr with h | h
  · exact hpost.saved r h
  · exact hpost.regs r h

theorem encrypt_correct (s : State) (hs : (VG.Proof.TripleDes.Arm.blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.TripleDes.Arm.blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.Arm.block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.TripleDes.Arm.blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.TripleDes.Arm.blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.Arm.block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha.1, ha.2⟩, hp⟩

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem publicRegs_three (s t : State) : VG.Proof.TripleDes.Arm.PublicRegs [.r0, .r1, .r2] s t ↔
    s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 := by
  simp [VG.Proof.TripleDes.Arm.PublicRegs]

theorem encrypt_verified : Verified target encryptBlock (Spec.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.Arm.encrypt_correct
    (VG.Proof.TripleDes.Arm.encryptBlock_constantTime _) ?_
  sig_implies [Spec.TripleDes.encryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr,
    VG.Proof.TripleDes.Arm.blockContract, VG.Proof.TripleDes.Arm.publicRegs_three, VG.Proof.TripleDes.Arm.blockResult] [satState] using VG.Proof.TripleDes.Arm.satState

theorem decrypt_verified : Verified target decryptBlock (Spec.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.Arm.decrypt_correct
    (VG.Proof.TripleDes.Arm.decryptBlock_constantTime _) ?_
  sig_implies [Spec.TripleDes.decryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr,
    VG.Proof.TripleDes.Arm.blockContract, VG.Proof.TripleDes.Arm.publicRegs_three, VG.Proof.TripleDes.Arm.blockResult] [satState] using VG.Proof.TripleDes.Arm.satState

end VG.Proof.TripleDes.Arm

end
