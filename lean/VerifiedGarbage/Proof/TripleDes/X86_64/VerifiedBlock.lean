import VerifiedGarbage.Impl.TripleDes.X86_64.Sbox
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Impl.TripleDes.X86_64.Permutation
import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Rc2.X86_64.Block
import VerifiedGarbage.Impl.TripleDes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.SboxTable`. -/
section

/-!
The code of the eight S-boxes as literals (`materialize_table`): the
literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read it rather than run the register
allocator that writes it again.
-/

namespace VG

materialize_table Impl.TripleDes.X86_64.sboxCode 8

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.RoundLit`. -/
section

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

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

end VG.Impl.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Lit`. -/
section

namespace VG.Impl.TripleDes.X86_64

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

end VG.Impl.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Sbox`. -/
section

/-!
# DES S-box machine-code correctness

Untrusted. The kernel checks each allocated scalar circuit on all 64
inputs, then the sound truth-table evaluator lifts that check to every
bit position of arbitrary 64-bit words. This verifies both the circuits
and the allocator's output, including spills.
-/

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])

def sboxCfg : Cfg := { base := .rdx, slots := 64, ext := .rdx, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => q k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.reg (q j) == some (outputTable i j)

theorem sbox_check : ∀ i < 8,
    VG.X86_64.Straight.check (table 64 64) VG.Proof.TripleDes.X86_64.sboxCfg (fun _ => none) (instrs (VG.Proof.TripleDes.X86_64.sboxLiteral i))
      VG.Proof.TripleDes.X86_64.sboxEnv (VG.Proof.TripleDes.X86_64.sboxPost i) = true := by
  lit_decide

def sboxWrites : List Reg := [.rax, .rcx, .r8, .r9, .r10, .r11, .rbx, .rbp, .r14, .r15]

theorem sbox_preserves : ∀ i < 8,
    [Reg.rdi, .rsi, .rdx, .rsp, .r12, .r13].all
      (fun r => (instrs (VG.Proof.TripleDes.X86_64.sboxLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

def inputAt (s : VG.X86_64.State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.gpr (q j)).getLsbD p

theorem inputAt_bit (s : VG.X86_64.State) (p k : Nat) (hk : k < 6) :
    (VG.Proof.TripleDes.X86_64.inputAt s p).toNat.testBit k = (s.gpr (q k)).getLsbD p := by
  simp only [VG.Proof.TripleDes.X86_64.inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxLiteral_eq : ∀ i < 8, VG.Proof.TripleDes.X86_64.sboxLiteral i = .block (sboxCode i)
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
theorem sbox_ok (i : Nat) (hi : i < 8) {s : VG.X86_64.State} (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        (Spec.TripleDes.sBox i (VG.Proof.TripleDes.X86_64.inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ VG.Proof.TripleDes.X86_64.sboxWrites → s'.gpr r = s.gpr r) ∧
      VG.Frame [slotRegion VG.Proof.TripleDes.X86_64.sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (VG.Proof.TripleDes.X86_64.sboxLiteral i) = sboxCode i := by rw [VG.Proof.TripleDes.X86_64.sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (VG.Proof.TripleDes.X86_64.sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.reg (q j) = some (outputTable i j) := by
    intro j hj
    have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (VG.Proof.TripleDes.X86_64.inputAt s p).toNat) VG.Proof.TripleDes.X86_64.sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (VG.Proof.TripleDes.X86_64.inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩ he
    simp only [VG.Proof.TripleDes.X86_64.sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      VG.Proof.TripleDes.X86_64.inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel, outputTable, testBit_tableOf, (VG.Proof.TripleDes.X86_64.inputAt s p).isLt,
      decide_true, Bool.true_and] at h
    rw [BitVec.ofNat_toNat] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.rdi, .rsi, .rdx, .rsp, .r12, .r13] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (VG.Proof.TripleDes.X86_64.sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Round`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64

noncomputable def sboxInputsLiterals : Array (Prog isa) :=
  #[sboxInputs0.lit, sboxInputs1.lit, sboxInputs2.lit, sboxInputs3.lit, sboxInputs4.lit, sboxInputs5.lit, sboxInputs6.lit, sboxInputs7.lit]

noncomputable def sboxInputsLiteral (i : Nat) : Prog isa :=
  sboxInputsLiterals.getD i (.block [])

noncomputable def sboxOutputsLiterals : Array (Prog isa) :=
  #[sboxOutputs0.lit, sboxOutputs1.lit, sboxOutputs2.lit, sboxOutputs3.lit, sboxOutputs4.lit, sboxOutputs5.lit, sboxOutputs6.lit, sboxOutputs7.lit]

noncomputable def sboxOutputsLiteral (i : Nat) : Prog isa :=
  sboxOutputsLiterals.getD i (.block [])

def roundInputCfg : Cfg := { base := .rdx, slots := 0, ext := .rdi, exts := 1 }
def roundInputRegs : List (Reg × Nat) := [(.r13, 0)]

def roundInputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 64 + (47 - k)]
  else []

def roundInputPost (i : Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 6).map fun j => (q j, VG.Proof.TripleDes.X86_64.roundInputBits i j)

theorem roundInput_check : ∀ i < 8,
    VG.X86_64.Straight.check (lanes 64 7) VG.Proof.TripleDes.X86_64.roundInputCfg (linExt 1) (instrs (VG.Proof.TripleDes.X86_64.sboxInputsLiteral i))
      (linEnv VG.Proof.TripleDes.X86_64.roundInputRegs) (linPost 7 (VG.Proof.TripleDes.X86_64.roundInputPost i)) = true := by
  decide +kernel

def roundOutputCfg : Cfg := { base := .rdx, slots := 0, ext := .rdx, exts := 0 }
def roundOutputRegs : List (Reg × Nat) :=
  [(.r12, 0)] ++ (List.range 4).map fun j => (q j, j + 1)

def roundOutputBits (i p : Nat) : List Nat :=
  [p] ++ ((List.range 4).filterMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then some (64 * (j + 1)) else none)

theorem roundOutput_check : ∀ i < 8,
    VG.X86_64.Straight.check (lanes 64 9) VG.Proof.TripleDes.X86_64.roundOutputCfg (linExt 5) (instrs (VG.Proof.TripleDes.X86_64.sboxOutputsLiteral i))
      (linEnv VG.Proof.TripleDes.X86_64.roundOutputRegs) (linPost 9 [(.r12, VG.Proof.TripleDes.X86_64.roundOutputBits i)]) = true := by
  decide +kernel

theorem sboxInputsLiteral_eq : ∀ i < 8,
    VG.Proof.TripleDes.X86_64.sboxInputsLiteral i = .block (sboxInputs i)
  | 0, _ => sboxInputs0.lit_eq.symm
  | 1, _ => sboxInputs1.lit_eq.symm
  | 2, _ => sboxInputs2.lit_eq.symm
  | 3, _ => sboxInputs3.lit_eq.symm
  | 4, _ => sboxInputs4.lit_eq.symm
  | 5, _ => sboxInputs5.lit_eq.symm
  | 6, _ => sboxInputs6.lit_eq.symm
  | 7, _ => sboxInputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundInputCfg_ok (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) : Ok VG.Proof.TripleDes.X86_64.roundInputCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.roundInputCfg] at hk
  · intro k hk
    have hk0 : k = 0 := by simp only [VG.Proof.TripleDes.X86_64.roundInputCfg] at hk; omega
    subst k
    simpa only [VG.Proof.TripleDes.X86_64.roundInputCfg, wordAddr, Nat.mul_zero,
      BitVec.add_zero] using hread
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.roundInputCfg] at hk

/-- The extraction block reads just one round key and forms six Boolean
input words. It does not change memory, access permissions or other registers. -/
theorem roundInput_ok (i : Nat) (hi : i < 8) (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      (∀ j < 6, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .r13
          else s.mem.readW (s.gpr .rdi) 64) (VG.Proof.TripleDes.X86_64.roundInputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := VG.Proof.TripleDes.X86_64.roundInput_check i hi
  rw [VG.Proof.TripleDes.X86_64.sboxInputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k = 0 then s.gpr .r13 else s.mem.readW (s.gpr .rdi) 64
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ := linear_ok hchk
    (VG.Proof.TripleDes.X86_64.roundInputCfg_ok s hread) W (fun r k h => by
      simp only [VG.Proof.TripleDes.X86_64.roundInputRegs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩) (fun j hj => by
      have hj0 : j = 0 := by simp only [VG.Proof.TripleDes.X86_64.roundInputCfg] at hj; omega
      subst j
      exact ⟨by decide, by simp [W, wordAddr, VG.Proof.TripleDes.X86_64.roundInputCfg]⟩)
  refine ⟨s', hs', fun j hj p hp => ?_, rd, wr, ?_, keep⟩
  · exact out (q j) (VG.Proof.TripleDes.X86_64.roundInputBits i j)
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.X86_64.roundInputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 64 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 64) (a : Nat) (ha : a < 64) :
    bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

theorem bitOf_next (W : Nat → BitVec 64) (a : Nat) (ha : a < 64) :
    bitOf W (64 + a) = (W 1).getLsbD a := by
  have hd : (64 + a) / 64 = 1 := by omega
  simp only [bitOf, hd, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((Spec.TripleDes.permute Spec.TripleDes.expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 64) (k : BitVec 64) :
    (VG.Proof.TripleDes.X86_64.roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
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
  simp only [VG.Proof.TripleDes.X86_64.roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [VG.Proof.TripleDes.permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      VG.Proof.TripleDes.X86_64.inputAt s' 0 = VG.Proof.TripleDes.X86_64.roundChunk i ((s.gpr .r13).setWidth 32)
        ((s.mem.readW (s.gpr .rdi) 64).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, mem, keep⟩ := VG.Proof.TripleDes.X86_64.roundInput_ok i hi s hread
  refine ⟨s', run, ?_, rd, wr, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.Proof.TripleDes.X86_64.inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  rw [bits j hj 0 (by decide), VG.Proof.TripleDes.X86_64.roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := VG.Proof.TripleDes.X86_64.roundInput_bounds i hi j hj
  simp only [VG.Proof.TripleDes.X86_64.roundInputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    VG.Proof.TripleDes.X86_64.bitOf_low _ _ hr, VG.Proof.TripleDes.X86_64.bitOf_next _ _ hk, ite_true]
  rfl

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if VG.Proof.TripleDes.X86_64.boxSource p / 4 = i then
    b.getLsbD (3 - VG.Proof.TripleDes.X86_64.boxSource p % 4) else false

theorem roundOutputBits_shape : ∀ i < 8, ∀ p < 64,
    VG.Proof.TripleDes.X86_64.roundOutputBits i p = [p] ++
      (if p < 32 ∧ VG.Proof.TripleDes.X86_64.boxSource p / 4 = i then
        [64 * (4 - VG.Proof.TripleDes.X86_64.boxSource p % 4)] else []) := by
  decide +kernel

theorem sboxOutputsLiteral_eq : ∀ i < 8,
    VG.Proof.TripleDes.X86_64.sboxOutputsLiteral i = .block (sboxOutputs i)
  | 0, _ => sboxOutputs0.lit_eq.symm
  | 1, _ => sboxOutputs1.lit_eq.symm
  | 2, _ => sboxOutputs2.lit_eq.symm
  | 3, _ => sboxOutputs3.lit_eq.symm
  | 4, _ => sboxOutputs4.lit_eq.symm
  | 5, _ => sboxOutputs5.lit_eq.symm
  | 6, _ => sboxOutputs6.lit_eq.symm
  | 7, _ => sboxOutputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundOutputCfg_ok (s : VG.X86_64.State) : Ok VG.Proof.TripleDes.X86_64.roundOutputCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.roundOutputCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.roundOutputCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.roundOutputCfg] at hk

/-- Deposit the four low S-box bits into L, at P's fixed destinations. -/
theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : VG.X86_64.State) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 64, (s'.gpr .r12).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .r12 else s.gpr (q (k - 1)))
          (VG.Proof.TripleDes.X86_64.roundOutputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := VG.Proof.TripleDes.X86_64.roundOutput_check i hi
  rw [VG.Proof.TripleDes.X86_64.sboxOutputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k = 0 then s.gpr .r12 else s.gpr (q (k - 1))
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ := linear_ok hchk
    (VG.Proof.TripleDes.X86_64.roundOutputCfg_ok s) W (fun r k h => by
      simp only [VG.Proof.TripleDes.X86_64.roundOutputRegs, List.mem_append, List.mem_singleton,
        Prod.mk.injEq, List.mem_map, List.mem_range] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨j, hj, heq⟩
      · exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by omega, ?_⟩
        simp [W]) (fun j hj => by simp [VG.Proof.TripleDes.X86_64.roundOutputCfg] at hj)
  refine ⟨s', hs', fun p hp => ?_, rd, wr, ?_, keep⟩
  · exact out .r12 (VG.Proof.TripleDes.X86_64.roundOutputBits i) (by simp) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.X86_64.roundOutputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem bitOf_word (W : Nat → BitVec 64) (j : Nat) :
    bitOf W (64 * j) = (W j).getLsbD 0 := by
  simp [bitOf]

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : VG.X86_64.State) (b : BitVec 4)
    (hb : ∀ j < 4, (s.gpr (q j)).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .r12 = s.gpr .r12 ^^^ (VG.Proof.TripleDes.X86_64.boxPiece i b).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, mem, keep⟩ := VG.Proof.TripleDes.X86_64.roundOutput_ok i hi s
  refine ⟨s', run, ?_, rd, wr, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, VG.Proof.TripleDes.X86_64.roundOutputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and]
  simp only [List.cons_append, List.nil_append, xorBits_cons, VG.Proof.TripleDes.X86_64.bitOf_low _ _ hp, ite_true]
  by_cases h : p < 32 ∧ VG.Proof.TripleDes.X86_64.boxSource p / 4 = i
  · simp only [h]
    have hj : 3 - VG.Proof.TripleDes.X86_64.boxSource p % 4 < 4 := by omega
    simp
    rw [VG.Proof.TripleDes.X86_64.bitOf_word]
    have hn : 4 - VG.Proof.TripleDes.X86_64.boxSource p % 4 ≠ 0 := by omega
    have heq : 4 - VG.Proof.TripleDes.X86_64.boxSource p % 4 - 1 = 3 - VG.Proof.TripleDes.X86_64.boxSource p % 4 := by omega
    simp only [hn, ite_false, heq]
    rw [hb _ hj]
    simp only [VG.Proof.TripleDes.X86_64.boxPiece, getLsbD_ofBits, h.1, h.2, decide_true, Bool.true_and, ite_true]
  · simp only [h, ite_false, xorBits_nil]
    simp only [VG.Proof.TripleDes.X86_64.boxPiece, getLsbD_ofBits]
    by_cases hp32 : p < 32
    · have hs : VG.Proof.TripleDes.X86_64.boxSource p / 4 ≠ i := by omega
      simp only [hp32, decide_true, Bool.true_and, hs, ite_false]
    · simp only [hp32, decide_false, Bool.false_and]

def roundKept : List Reg := [.rdi, .rsi, .rdx, .rsp, .r13]

theorem roundInput_keeps : ∀ i < 8, (.r12 :: VG.Proof.TripleDes.X86_64.roundKept).all
    (fun r => (instrs (VG.Proof.TripleDes.X86_64.sboxInputsLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem roundOutput_keeps : ∀ i < 8, roundKept.all
    (fun r => (instrs (VG.Proof.TripleDes.X86_64.sboxOutputsLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem roundInput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ .r12 :: VG.Proof.TripleDes.X86_64.roundKept) :
    (sboxInputs i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (VG.Proof.TripleDes.X86_64.roundInput_keeps i hi) r hr
  rw [VG.Proof.TripleDes.X86_64.sboxInputsLiteral_eq i hi] at h
  exact h

theorem roundOutput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ VG.Proof.TripleDes.X86_64.roundKept) :
    (sboxOutputs i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (VG.Proof.TripleDes.X86_64.roundOutput_keeps i hi) r hr
  rw [VG.Proof.TripleDes.X86_64.sboxOutputsLiteral_eq i hi] at h
  exact h

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Spills`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

def spillRegion (s : VG.X86_64.State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 64, 384⟩

def spillSafe : Instr → Bool
  | .mov d _ | .movImm64 d _ => d != .rdx
  | .alu .and d _ | .alu .xor d _ => d != .rdx
  | .store m _ => decide (m.base = .rdx ∧ m.index = none ∧
      64 ≤ m.disp ∧ m.disp + 8 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (VG.Proof.TripleDes.X86_64.sboxLiteral i)).all VG.Proof.TripleDes.X86_64.spillSafe = true := by decide +kernel

theorem spillStep_frame (i : Instr) (s s' : VG.X86_64.State)
    (h : VG.Proof.TripleDes.X86_64.spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .rdx = s.gpr .rdx ∧ VG.Frame [VG.Proof.TripleDes.X86_64.spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [VG.Proof.TripleDes.X86_64.spillSafe, Bool.false_eq_true] at h
  case mov d src =>
    have hd : .rdx ≠ d := by intro heq; subst d; simp at h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact ⟨by simp only [gpr_setReg, hd, ite_false], by
      simp only [mem_setReg]; exact Frame.refl _ _⟩
  case movImm64 d v =>
    have hd : .rdx ≠ d := by intro heq; subst d; simp at h
    simp only [exec, Option.some.injEq] at he
    subst s'
    exact ⟨by simp only [gpr_setReg, hd, ite_false], by
      simp only [mem_setReg]; exact Frame.refl _ _⟩
  case alu op d src =>
    cases op <;> simp only [Bool.false_eq_true] at h
    all_goals
      have hd : .rdx ≠ d := by intro heq; subst d; simp at h
      simp only [exec, execAlu, Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨v, _, rfl⟩ := he
      exact ⟨by simp only [gpr_setReg, gpr_arithFlags, hd, ite_false], by
        simp only [mem_setReg, mem_arithFlags]; exact Frame.refl _ _⟩
  case store m r =>
    obtain ⟨hb, hi, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec, State.store64] at he
    split at he
    · simp only [Option.some.injEq] at he
      subst s'
      refine ⟨rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_⟩
      have hnat : m.disp = (m.disp.toNat : Int) := by omega
      simp only [State.ea, hi, hb]
      rw [hnat, BitVec.ofInt_natCast]
      exact Offset.contains (s.gpr .rdx) (by omega) (by omega) (by decide)
    · cases he

theorem spillBlock_frame (is : List Instr) (s s' : VG.X86_64.State)
    (hsafe : is.all VG.Proof.TripleDes.X86_64.spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .rdx = s.gpr .rdx ∧ VG.Frame [VG.Proof.TripleDes.X86_64.spillRegion s] s.mem s'.mem := by
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
    obtain ⟨hg, hf⟩ := VG.Proof.TripleDes.X86_64.spillStep_frame i s s₁ hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : VG.Proof.TripleDes.X86_64.spillRegion s₁ = VG.Proof.TripleDes.X86_64.spillRegion s := by simp only [VG.Proof.TripleDes.X86_64.spillRegion, hg]
    rw [hr] at hf'
    exact hf'

/-- The saved registers and round counter in scratch slots 0–7 are
outside the S-box's frame, as are the key schedule and block data. -/
theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : VG.X86_64.State)
    (he : runBlock isa (sboxCode i) s = some s') :
    VG.Frame [VG.Proof.TripleDes.X86_64.spillRegion s] s.mem s'.mem := by
  have h := VG.Proof.TripleDes.X86_64.spillSafe_check i hi
  rw [VG.Proof.TripleDes.X86_64.sboxLiteral_eq i hi] at h
  exact (VG.Proof.TripleDes.X86_64.spillBlock_frame _ _ _ h he).2

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Box`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64

theorem runBoxes_append (a b : List Instr) (s : VG.X86_64.State) :
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
theorem box_ok (i : Nat) (hi : i < 8) (s : VG.X86_64.State) (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .r12 = s.gpr .r12 ^^^
        (VG.Proof.TripleDes.X86_64.boxPiece i (Spec.TripleDes.sBox i
          (VG.Proof.TripleDes.X86_64.roundChunk i ((s.gpr .r13).setWidth 32)
            ((s.mem.readW (s.gpr .rdi) 64).setWidth 48)))).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ VG.Proof.TripleDes.X86_64.roundKept, s'.gpr r = s.gpr r) ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, mem₁, keep₁⟩ := VG.Proof.TripleDes.X86_64.roundInput_chunk i hi s hread
  have kept₁ : ∀ r ∈ .r12 :: VG.Proof.TripleDes.X86_64.roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (VG.Proof.TripleDes.X86_64.roundInput_keep i hi r hr)
  have hok₁ : Ok VG.Proof.TripleDes.X86_64.sboxCfg s₁ := hok.congr
    (kept₁ .rdx (by decide)) (kept₁ .rdx (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, keep₂, _⟩ := VG.Proof.TripleDes.X86_64.sbox_ok i hi hok₁
  have hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
      (Spec.TripleDes.sBox i (VG.Proof.TripleDes.X86_64.roundChunk i ((s.gpr .r13).setWidth 32)
        ((s.mem.readW (s.gpr .rdi) 64).setWidth 48))).getLsbD j := by
    intro j hj
    rw [bits j hj 0 (by decide), chunk]
  obtain ⟨s₃, run₃, value, rd₃, wr₃, mem₃, keep₃⟩ := VG.Proof.TripleDes.X86_64.roundOutput_piece i hi s₂ _ hbits
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_, ?_⟩
  · simp only [box, VG.Proof.TripleDes.X86_64.runBoxes_append, run₁, Option.bind_some, run₂, run₃]
  · rw [value, keep₂ .r12 (by decide), kept₁ .r12 (by decide)]
  · intro r hr
    rw [keep₃ r (VG.Proof.TripleDes.X86_64.roundOutput_keep i hi r hr), keep₂ r ?_, kept₁ r (List.mem_cons_of_mem _ hr)]
    revert hr; cases r <;> decide
  · have hf := VG.Proof.TripleDes.X86_64.sbox_spillFrame i hi s₁ s₂ run₂
    have hregion : VG.Proof.TripleDes.X86_64.spillRegion s₁ = VG.Proof.TripleDes.X86_64.spillRegion s := by
      simp only [VG.Proof.TripleDes.X86_64.spillRegion, kept₁ .rdx (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.RoundFunction`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.Bitslice VG.Spec.TripleDes

theorem boxSource_shape : ∀ j < 32,
    7 - (32 - p.getD (31 - j) 1) / 4 = VG.Proof.TripleDes.X86_64.boxSource j / 4 ∧
    (32 - p.getD (31 - j) 1) % 4 = 3 - VG.Proof.TripleDes.X86_64.boxSource j % 4 ∧
    VG.Proof.TripleDes.X86_64.boxSource j / 4 < 8 := by
  decide +kernel

theorem boxPiece_round_bit (i : Nat) (r : BitVec 32) (k : BitVec 48)
    (j : Nat) (hj : j < 32) :
    (VG.Proof.TripleDes.X86_64.boxPiece i (sBox i (VG.Proof.TripleDes.X86_64.roundChunk i r k))).getLsbD j =
      if VG.Proof.TripleDes.X86_64.boxSource j / 4 = i then (roundFunction r k).getLsbD j else false := by
  simp only [VG.Proof.TripleDes.X86_64.boxPiece, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  by_cases heq : VG.Proof.TripleDes.X86_64.boxSource j / 4 = i
  · simp only [heq, ite_true]
    rw [VG.Proof.TripleDes.roundFunction_bit r k j hj]
    obtain ⟨hidx, hbit, _⟩ := VG.Proof.TripleDes.X86_64.boxSource_shape j hj
    simp only [hidx, hbit, heq, VG.Proof.TripleDes.X86_64.roundChunk]
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
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86_64.boxPiece i (sBox i (VG.Proof.TripleDes.X86_64.roundChunk i r k)))
      (0 : BitVec 32) = roundFunction r k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hfold : (fun (out : Bool) i => out ^^
      (VG.Proof.TripleDes.X86_64.boxPiece i (sBox i (VG.Proof.TripleDes.X86_64.roundChunk i r k))).getLsbD j) =
      (fun out i => out ^^ (if VG.Proof.TripleDes.X86_64.boxSource j / 4 = i then
        (roundFunction r k).getLsbD j else false)) := by
    funext out i
    exact congrArg (fun b => out ^^ b) (VG.Proof.TripleDes.X86_64.boxPiece_round_bit i r k j hj)
  have hbits := VG.Proof.TripleDes.X86_64.foldl_xor_bits (List.range 8)
    (fun i => VG.Proof.TripleDes.X86_64.boxPiece i (sBox i (VG.Proof.TripleDes.X86_64.roundChunk i r k))) 0 j
  have hz : (0 : BitVec 32).getLsbD j = false := by
    change (BitVec.ofNat 32 0).getLsbD j = false
    exact BitVec.getLsbD_zero
  have hinit := congrArg (fun b : Bool => (List.range 8).foldl
    (fun out i => out ^^ (VG.Proof.TripleDes.X86_64.boxPiece i (sBox i (VG.Proof.TripleDes.X86_64.roundChunk i r k))).getLsbD j) b) hz
  have hchange := congrArg
    (fun f : Bool → Nat → Bool => (List.range 8).foldl f false) hfold
  exact hbits.trans (hinit.trans (hchange.trans (VG.Proof.TripleDes.X86_64.select_xor _ (VG.Proof.TripleDes.X86_64.boxSource_shape j hj).2.2 _)))

theorem foldl_xor_start (xs : List Nat) (f : Nat → BitVec 64) (a : BitVec 64) :
    xs.foldl (fun out i => out ^^^ f i) a =
      a ^^^ xs.foldl (fun out i => out ^^^ f i) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons]
    have hz : (0 : BitVec 64) ^^^ f i = f i := BitVec.zero_xor
    rw [hz, ih (a ^^^ f i), ih (f i)]
    exact BitVec.xor_assoc _ _ _

theorem foldl_xor_extend (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) :
    xs.foldl (fun out i => out ^^^ (f i).setWidth 64) (a.setWidth 64) =
      (xs.foldl (fun out i => out ^^^ f i) a).setWidth 64 := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [← BitVec.setWidth_xor]
    exact ih _

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64

def contribution (r k : BitVec 64) (i : Nat) : BitVec 64 :=
  (VG.Proof.TripleDes.X86_64.boxPiece i (Spec.TripleDes.sBox i
    (VG.Proof.TripleDes.X86_64.roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 64

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r k : BitVec 64) (s : VG.X86_64.State) (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg s)
    (hr : s.gpr .r13 = r) (hk : s.mem.readW (s.gpr .rdi) 64 = k)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8)
    (hsep : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .r12 = indices.foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86_64.contribution r k i) (s.gpr .r12) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ VG.Proof.TripleDes.X86_64.roundKept, s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.X86_64.box_ok i hi s hok hread
    have hregion : VG.Proof.TripleDes.X86_64.spillRegion s₁ = VG.Proof.TripleDes.X86_64.spillRegion s := by
      simp only [VG.Proof.TripleDes.X86_64.spillRegion, keep₁ .rdx (by decide)]
    have hr₁ : s₁.gpr .r13 = r := (keep₁ .r13 (by decide)).trans hr
    have hk₁ : s₁.mem.readW (s₁.gpr .rdi) 64 = k := by
      rw [keep₁ .rdi (by decide)]
      refine Eq.trans (frame₁.readW (r := ⟨s.gpr .rdi, 8⟩) ?_ ?_ (by decide)) hk
      · simp [Region.Contains]
      · intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact hsep
    have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi) 8 := by
      rw [rd₁, wr₁, keep₁ .rdi (by decide)]
      exact hread
    have hsep₁ : (⟨s₁.gpr .rdi, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.spillRegion s₁) := by
      rw [keep₁ .rdi (by decide), hregion]
      exact hsep
    have hok₁ : Ok VG.Proof.TripleDes.X86_64.sboxCfg s₁ := hok.congr
      (keep₁ .rdx (by decide)) (keep₁ .rdx (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, VG.Proof.TripleDes.X86_64.runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .r12 = s.gpr .r12 ^^^ VG.Proof.TripleDes.X86_64.contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r k : BitVec 64) (l : BitVec 64) :
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86_64.contribution r k i) l =
      l ^^^ (Spec.TripleDes.roundFunction (r.setWidth 32) (k.setWidth 48)).zeroExtend 64 := by
  rw [VG.Proof.TripleDes.X86_64.foldl_xor_start]
  have hf := VG.Proof.TripleDes.X86_64.foldl_xor_extend (List.range 8)
    (fun i => VG.Proof.TripleDes.X86_64.boxPiece i (Spec.TripleDes.sBox i
      (VG.Proof.TripleDes.X86_64.roundChunk i (r.setWidth 32) (k.setWidth 48)))) 0
  have hz : (0 : BitVec 32).setWidth 64 = 0 := BitVec.setWidth_zero 64 32
  have hinit := congrArg (fun b : BitVec 64 =>
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86_64.contribution r k i) b) hz
  have hg := congrArg (BitVec.setWidth 64)
    (VG.Proof.TripleDes.X86_64.boxPieces_eq_roundFunction (r.setWidth 32) (k.setWidth 48))
  exact congrArg (fun x => l ^^^ x) ((hinit.symm.trans hf).trans hg)

def roundOuterKept : List Reg := [.rdi, .rsi, .rdx, .rsp]

theorem swapHalves_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r12 = s.gpr .r13 ∧ s'.gpr .r13 = s.gpr .r12 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ q ∈ VG.Proof.TripleDes.X86_64.roundOuterKept, s'.gpr q = s.gpr q) := by
  open VG.X86_64.RegUpd in
  refine ⟨_, by
    simp only [swapHalves, VG.Impl.TripleDes.X86_64.rr, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, Option.map_some, gpr_setReg]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg]; rfl
  · simp only [gpr_setReg]; rfl
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [mem_setReg]
  · intro q hq
    have hneq : q ≠ .rax ∧ q ≠ .r12 ∧ q ≠ .r13 := by
      revert hq; cases q <;> decide
    simp only [gpr_setReg, hneq.1, hneq.2.1, hneq.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : VG.X86_64.State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .rdi) 64 = k) (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8)
    (hsep : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r12 = r.setWidth 64 ∧
      s'.gpr .r13 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ VG.Proof.TripleDes.X86_64.roundOuterKept, s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.X86_64.boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r.setWidth 64) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, mem₂, keep₂⟩ := VG.Proof.TripleDes.X86_64.swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [roundBody, VG.Proof.TripleDes.X86_64.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r13 (by decide)).trans hr)
  · rw [right, value, VG.Proof.TripleDes.X86_64.contributions_roundFunction, hl]
    have hwidth : (r.setWidth 64).setWidth 32 = r := by simp
    rw [hwidth]
    exact BitVec.setWidth_xor.symm
  · intro q hq
    have hq' : q ∈ VG.Proof.TripleDes.X86_64.roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.PassSteps`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

def countAddr (s : VG.X86_64.State) : Addr := s.gpr .rdx + BitVec.ofNat 64 56

theorem roundCountAdvance_ok (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8)
    (hwrite : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8) :
    ∃ s', runBlock isa roundCountAdvance s = some s' ∧
      s'.mem = s.mem.writeW (VG.Proof.TripleDes.X86_64.countAddr s) (s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold VG.Proof.TripleDes.X86_64.countAddr at hread hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 56) = BitVec.ofNat 64 56 := rfl
  refine ⟨_, by
    simp only [roundCountAdvance, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, VG.Impl.TripleDes.X86_64.memOp, hoff, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [zf_setReg, zf_arithFlags]
    rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

theorem pointerAdvance_ok (direction : Spec.TripleDes.Direction) (s : VG.X86_64.State) :
    ∃ s', runBlock isa
      [.alu (if direction = .encrypt then .add else .sub) .rdi (.imm 8)] s = some s' ∧
      s'.gpr .rdi = (if direction = .encrypt then s.gpr .rdi + 8 else s.gpr .rdi - 8) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) := by
  cases direction <;>
    refine ⟨_, by
      simp only [runBlock_cons, exec, execAlu, readSrc,
        Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try exact gpr_setReg_self _ _ _
  all_goals try simp only [mem_setReg, mem_arithFlags]
  all_goals try simp only [rd_setReg, rd_arithFlags]
  all_goals try simp only [wr_setReg, wr_arithFlags]
  all_goals
    intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) == 0) = decide (n = 1) := by
  decide +kernel

theorem countWrite_frame (m : Mem) (p : Addr) (v : BitVec 64) :
    VG.Frame [⟨p, 8⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

theorem roundAdvance_ok (direction : Spec.TripleDes.Direction) (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8)
    (hwrite : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8) :
    ∃ s', runBlock isa (roundAdvance direction) s = some s' ∧
      s'.gpr .rdi = (if direction = .encrypt then s.gpr .rdi + 8 else s.gpr .rdi - 8) ∧
      s'.mem = s.mem.writeW (VG.Proof.TripleDes.X86_64.countAddr s) (s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, ptr₁, mem₁, rd₁, wr₁, keep₁⟩ := VG.Proof.TripleDes.X86_64.pointerAdvance_ok direction s
  have haddr : VG.Proof.TripleDes.X86_64.countAddr s₁ = VG.Proof.TripleDes.X86_64.countAddr s := by
    simp only [VG.Proof.TripleDes.X86_64.countAddr, keep₁ .rdx (by decide)]
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (VG.Proof.TripleDes.X86_64.countAddr s₁) 8 := by
    rw [rd₁, wr₁, haddr]; exact hread
  have hwrite₁ : InRegions s₁.wr (VG.Proof.TripleDes.X86_64.countAddr s₁) 8 := by
    rw [wr₁, haddr]; exact hwrite
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ := VG.Proof.TripleDes.X86_64.roundCountAdvance_ok s₁ hread₁ hwrite₁
  refine ⟨s₂, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩
  · simp only [roundAdvance, VG.Proof.TripleDes.X86_64.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .rdi (by decide)).trans ptr₁
  · rw [mem₂, mem₁, haddr]
  · rw [flag₂, mem₁, haddr]
  · exact fun r hrax hrdi => (keep₂ r hrax).trans (keep₁ r hrdi)

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.RoundStep`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64

def workRegion (s : VG.X86_64.State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 56, 392⟩

theorem count_spill_disjoint (s : VG.X86_64.State) :
    (⟨VG.Proof.TripleDes.X86_64.countAddr s, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.spillRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem spill_sub_work (s : VG.X86_64.State) : Region.Sub (VG.Proof.TripleDes.X86_64.spillRegion s) (VG.Proof.TripleDes.X86_64.workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem count_sub_work (s : VG.X86_64.State) : Region.Sub ⟨VG.Proof.TripleDes.X86_64.countAddr s, 8⟩ (VG.Proof.TripleDes.X86_64.workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem roundStep_ok (direction : Spec.TripleDes.Direction) (s : VG.X86_64.State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .rdi) 64 = k) (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8)
    (hsep : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.spillRegion s))
    (hcount : s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 = BitVec.ofNat 64 n)
    (hcountRead : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8)
    (hcountWrite : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance direction) s = some s' ∧
      s'.gpr .r12 = r.setWidth 64 ∧
      s'.gpr .r13 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .rdi = (if direction = .encrypt then s.gpr .rdi + 8 else s.gpr .rdi - 8) ∧
      s'.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s') 64 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.rsi, .rdx, .rsp], s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.X86_64.workRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, keep₁, frame₁⟩ :=
    VG.Proof.TripleDes.X86_64.roundBody_ok s l r k hl hr hk hok hread hsep
  have haddr : VG.Proof.TripleDes.X86_64.countAddr s₁ = VG.Proof.TripleDes.X86_64.countAddr s := by
    simp only [VG.Proof.TripleDes.X86_64.countAddr, keep₁ .rdx (by decide)]
  have hcount₁ : s₁.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s₁) 64 = BitVec.ofNat 64 n := by
    rw [haddr]
    refine Eq.trans (frame₁.readW (r := ⟨VG.Proof.TripleDes.X86_64.countAddr s, 8⟩) ?_ ?_ (by decide)) hcount
    · exact Region.contains_self _ _
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact VG.Proof.TripleDes.X86_64.count_spill_disjoint s
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (VG.Proof.TripleDes.X86_64.countAddr s₁) 8 := by
    rw [rd₁, wr₁, haddr]; exact hcountRead
  have hwrite₁ : InRegions s₁.wr (VG.Proof.TripleDes.X86_64.countAddr s₁) 8 := by
    rw [wr₁, haddr]; exact hcountWrite
  obtain ⟨s₂, run₂, ptr₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ :=
    VG.Proof.TripleDes.X86_64.roundAdvance_ok direction s₁ hread₁ hwrite₁
  have hcountAddr₂ : VG.Proof.TripleDes.X86_64.countAddr s₂ = VG.Proof.TripleDes.X86_64.countAddr s₁ := by
    simp only [VG.Proof.TripleDes.X86_64.countAddr, keep₂ .rdx (by decide) (by decide)]
  have hwork : VG.Proof.TripleDes.X86_64.workRegion s₁ = VG.Proof.TripleDes.X86_64.workRegion s := by
    simp only [VG.Proof.TripleDes.X86_64.workRegion, keep₁ .rdx (by decide)]
  obtain ⟨hsub, hzero⟩ := VG.Proof.TripleDes.X86_64.countDown_rules n hn' hn
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [VG.Proof.TripleDes.X86_64.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r12 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r13 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .rdi (by decide)]
  · rw [hcountAddr₂, mem₂, Mem.readW_writeW_self64, hcount₁, hsub]
  · change VG.X86_64.eval .ne s₂ = some (decide (n ≠ 1))
    simp only [VG.X86_64.eval, flag₂, hcount₁, hzero, Option.map_some]
    simp
  · intro q hq
    have hq' : q ∈ VG.Proof.TripleDes.X86_64.roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .rax ∧ q ≠ .rdi := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · have hf₁ : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion s] s.mem s₁.mem := frame₁.sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, VG.Proof.TripleDes.X86_64.spill_sub_work s⟩)
    have hf₂ := VG.Proof.TripleDes.X86_64.countWrite_frame s₁.mem (VG.Proof.TripleDes.X86_64.countAddr s₁) (s₁.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s₁) 64 - 1)
    have hf₂' : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion s₁] s₁.mem s₂.mem := by
      rw [mem₂]
      exact hf₂.sub (by
        intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact ⟨_, List.mem_singleton_self _, VG.Proof.TripleDes.X86_64.count_sub_work s₁⟩)
    rw [hwork] at hf₂'
    exact hf₁.trans hf₂'

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Loop`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : VG.Spec.TripleDes.Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

theorem keyAddr_step (base : Addr) (direction : VG.Spec.TripleDes.Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then VG.Proof.TripleDes.X86_64.keyAddr base direction j + 8
      else VG.Proof.TripleDes.X86_64.keyAddr base direction j - 8) = VG.Proof.TripleDes.X86_64.keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega)
  · change base + BitVec.ofNat 64 (8 * (15 - j)) - BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (15 - (j + 1)))
    rw [Offset.add_ofNat_sub _ (by omega)]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega)

structure LoopInv (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction) (base : Addr)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : VG.X86_64.State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r12 = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 = BitVec.ofNat 64 n
  pointer : s.gpr .rdi = VG.Proof.TripleDes.X86_64.keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32) (s : VG.X86_64.State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).2.setWidth 64
  counter : s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 = 0
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction) (base : Addr)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg origin)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨VG.Proof.TripleDes.X86_64.keyAddr base direction j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : VG.X86_64.State) (hs : VG.Proof.TripleDes.X86_64.LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ VG.Proof.TripleDes.X86_64.LoopPost keys direction origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, VG.Proof.TripleDes.X86_64.LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have haddr : VG.Proof.TripleDes.X86_64.countAddr s = VG.Proof.TripleDes.X86_64.countAddr origin := by
    simp only [VG.Proof.TripleDes.X86_64.countAddr, hs.regs .rdx (by decide)]
  have hwork : VG.Proof.TripleDes.X86_64.workRegion s = VG.Proof.TripleDes.X86_64.workRegion origin := by
    simp only [VG.Proof.TripleDes.X86_64.workRegion, hs.regs .rdx (by decide)]
  have hokS : Ok VG.Proof.TripleDes.X86_64.sboxCfg s := hok.congr
    (hs.regs .rdx (by decide)) (hs.regs .rdx (by decide)) hs.rd hs.wr
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hsepS : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.spillRegion s) := by
    rw [hs.pointer]
    intro a ha hb
    apply hsep _ hj a ha
    rw [← hwork]
    exact VG.Proof.TripleDes.X86_64.spill_sub_work s a hb
  have hreadCountS : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8 := by
    rw [hs.rd, hs.wr, haddr]; exact hcountRead
  have hwriteCountS : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8 := by
    rw [hs.wr, haddr]; exact hcountWrite
  have hk : (s.mem.readW (s.gpr .rdi) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer]
    have hmem := hs.frame.readW (a := VG.Proof.TripleDes.X86_64.keyAddr base direction (16 - n)) (w := 64)
      (r := ⟨VG.Proof.TripleDes.X86_64.keyAddr base direction (16 - n), 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact hsep _ hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, regs, frame⟩ :=
    VG.Proof.TripleDes.X86_64.roundStep_ok direction s _ _ (s.mem.readW (s.gpr .rdi) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter hreadCountS hwriteCountS
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r12 = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r13 = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
      rw [ptr, hs.pointer, VG.Proof.TripleDes.X86_64.keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction) (base : Addr)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.gpr .rdi = VG.Proof.TripleDes.X86_64.keyAddr base direction 0)
    (hcount : origin.mem.readW (VG.Proof.TripleDes.X86_64.countAddr origin) 64 = BitVec.ofNat 64 16)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨VG.Proof.TripleDes.X86_64.keyAddr base direction j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (VG.Proof.TripleDes.X86_64.LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := VG.Proof.TripleDes.X86_64.LoopPost keys direction origin v) (VG.Proof.TripleDes.X86_64.LoopInv keys direction base origin v)
    (VG.Proof.TripleDes.X86_64.loopStep keys direction base origin v hok hcountRead hcountWrite hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.PassStart`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def savedKeyAddr (s : VG.X86_64.State) : Addr := s.gpr .rdx + BitVec.ofNat 64 48

def passOffset (component : Nat) (direction : VG.Spec.TripleDes.Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_signExtend (component : Nat) (hc : component < 3) (direction : VG.Spec.TripleDes.Direction) :
    (BitVec.ofNat 32 (VG.Proof.TripleDes.X86_64.passOffset component direction)).signExtend 64 =
      BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset component direction) := by
  have h : ∀ c < 3,
      ((BitVec.ofNat 32 (VG.Proof.TripleDes.X86_64.passOffset c .encrypt)).signExtend 64 =
        BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset c .encrypt)) ∧
      ((BitVec.ofNat 32 (VG.Proof.TripleDes.X86_64.passOffset c .decrypt)).signExtend 64 =
        BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset c .decrypt)) := by decide +kernel
  cases direction
  · exact (h component hc).1
  · exact (h component hc).2

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : VG.Spec.TripleDes.Direction)
    (s : VG.X86_64.State) (hread : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.savedKeyAddr s) 8)
    (hwrite : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .rdi = s.mem.readW (VG.Proof.TripleDes.X86_64.savedKeyAddr s) 64 +
        BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset component direction) ∧
      s'.mem = s.mem.writeW (VG.Proof.TripleDes.X86_64.countAddr s) (BitVec.ofNat 64 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  unfold VG.Proof.TripleDes.X86_64.savedKeyAddr at hread
  unfold VG.Proof.TripleDes.X86_64.countAddr at hwrite
  have h48 : BitVec.ofInt 64 (Int.ofNat 48) = BitVec.ofNat 64 48 := rfl
  have h56 : BitVec.ofInt 64 (Int.ofNat 56) = BitVec.ofNat 64 56 := rfl
  refine ⟨_, by
    simp only [passStart, VG.Impl.TripleDes.X86_64.imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, VG.Impl.TripleDes.X86_64.memOp, h48, h56, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact congrArg (s.mem.readW (VG.Proof.TripleDes.X86_64.savedKeyAddr s) 64 + ·)
      (VG.Proof.TripleDes.X86_64.passOffset_signExtend component hc direction)
  · rfl
  · rfl
  · rfl
  · intro r hrax hrdi
    simp only [gpr_setReg, gpr_arithFlags, hrax, hrdi, ite_false]

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Pass`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32) (s : VG.X86_64.State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction) (base : Addr)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.gpr .rdi = VG.Proof.TripleDes.X86_64.keyAddr base direction 0)
    (hcount : origin.mem.readW (VG.Proof.TripleDes.X86_64.countAddr origin) 64 = BitVec.ofNat 64 16)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨VG.Proof.TripleDes.X86_64.keyAddr base direction j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      (.block swapHalves)) origin (VG.Proof.TripleDes.X86_64.PassPost keys direction origin v) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hcountRead hcountWrite hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, mem, regs⟩ := VG.Proof.TripleDes.X86_64.swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left,
    rd.trans hs.rd, wr.trans hs.wr, ?_, ?_⟩
  · intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ VG.Proof.TripleDes.X86_64.roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


/-- A complete DES pass, including its public key-pointer and counter setup. -/
theorem pass_ok (component : Nat) (hc : component < 3)
    (keys : DesSchedule) (direction : VG.Spec.TripleDes.Direction) (base : Addr)
    (origin : VG.X86_64.State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.X86_64.sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.mem.readW (VG.Proof.TripleDes.X86_64.savedKeyAddr origin) 64 +
      BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset component direction) = VG.Proof.TripleDes.X86_64.keyAddr base direction 0)
    (hsavedRead : InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.savedKeyAddr origin) 8)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (VG.Proof.TripleDes.X86_64.countAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨VG.Proof.TripleDes.X86_64.keyAddr base direction j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass component direction) origin (VG.Proof.TripleDes.X86_64.PassPost keys direction origin v) := by
  obtain ⟨s, run, ptr, mem, rd, wr, regs⟩ :=
    VG.Proof.TripleDes.X86_64.passStart_ok component hc direction origin hsavedRead hcountWrite
  have hbase : s.gpr .rdx = origin.gpr .rdx := regs .rdx (by decide) (by decide)
  have hcountAddr : VG.Proof.TripleDes.X86_64.countAddr s = VG.Proof.TripleDes.X86_64.countAddr origin := congrArg (· + BitVec.ofNat 64 56) hbase
  have hwork : VG.Proof.TripleDes.X86_64.workRegion s = VG.Proof.TripleDes.X86_64.workRegion origin := congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) hbase
  have hframe : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion origin] origin.mem s.mem := by
    rw [mem]
    apply (VG.Proof.TripleDes.X86_64.countWrite_frame origin.mem (VG.Proof.TripleDes.X86_64.countAddr origin) (BitVec.ofNat 64 16)).sub
    intro r hmem
    obtain rfl := List.mem_singleton.mp hmem
    exact ⟨VG.Proof.TripleDes.X86_64.workRegion origin, List.mem_singleton_self _, VG.Proof.TripleDes.X86_64.count_sub_work origin⟩
  have hkeysS : ∀ j < 16, (s.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j := by
    intro j hj
    have hmem := hframe.readW (a := VG.Proof.TripleDes.X86_64.keyAddr base direction j) (w := 64)
      (r := ⟨VG.Proof.TripleDes.X86_64.keyAddr base direction j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys j hj)
  have hreadS : ∀ j < 16, InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.keyAddr base direction j) 8 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, (⟨VG.Proof.TripleDes.X86_64.keyAddr base direction j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion s) := by
    rw [hwork]; exact hsep
  have hcountReadS : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8 := by
    rw [rd, wr, hcountAddr]; exact hcountRead
  have hcountWriteS : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8 := by
    rw [wr, hcountAddr]; exact hcountWrite
  have hcount : s.mem.readW (VG.Proof.TripleDes.X86_64.countAddr s) 64 = BitVec.ofNat 64 16 := by
    rw [mem, hcountAddr]
    exact Mem.readW_writeW_self64 _ _ _
  have htail := VG.Proof.TripleDes.X86_64.roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .r12 (by decide) (by decide)).trans hl)
    ((regs .r13 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) hcount hcountReadS hcountWriteS hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.rd.trans rd, hs.wr.trans wr, ?_, ?_⟩
  · intro q hq
    have hneq : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ≠ .rax ∧ r ≠ .rdi := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).1 (hneq q hq).2)
  · have hf := hs.frame
    rw [hwork] at hf
    exact hframe.trans hf

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.WordState`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : VG.X86_64.State) : Prop where
  left : s.gpr .r12 = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr .r13 = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : VG.X86_64.State} {x : BitVec 64}
    (hs : VG.Proof.TripleDes.X86_64.PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) s) :
    VG.Proof.TripleDes.X86_64.WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32).setWidth 64 = halves.2.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_left halves.2 halves.1))
  have hright : ((desCore keys direction x).setWidth 32).setWidth 64 = halves.1.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_right halves.2 halves.1))
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Ready`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : VG.X86_64.State) : Prop where
  spills : Ok VG.Proof.TripleDes.X86_64.sboxCfg s
  saved : s.mem.readW (VG.Proof.TripleDes.X86_64.savedKeyAddr s) 64 = base
  savedRead : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.savedKeyAddr s) 8
  countRead : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8
  countWrite : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8
  read : ∀ c < 3, ∀ d : VG.Spec.TripleDes.Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : VG.Spec.TripleDes.Direction, ∀ j < 16,
    (⟨VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion s)
  values : ∀ c < 3, ∀ d : VG.Spec.TripleDes.Direction, ∀ j < 16,
    (s.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem saved_work_disjoint (s : VG.X86_64.State) :
    (⟨VG.Proof.TripleDes.X86_64.savedKeyAddr s, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : VG.X86_64.State}
    (hs : VG.Proof.TripleDes.X86_64.Ready keys base s) (hbase : t.gpr .rdx = s.gpr .rdx)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion s] s.mem t.mem) : VG.Proof.TripleDes.X86_64.Ready keys base t := by
  have hsave : VG.Proof.TripleDes.X86_64.savedKeyAddr t = VG.Proof.TripleDes.X86_64.savedKeyAddr s := congrArg (· + BitVec.ofNat 64 48) hbase
  have hcount : VG.Proof.TripleDes.X86_64.countAddr t = VG.Proof.TripleDes.X86_64.countAddr s := congrArg (· + BitVec.ofNat 64 56) hbase
  have hwork : VG.Proof.TripleDes.X86_64.workRegion t = VG.Proof.TripleDes.X86_64.workRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsave]
    have hmem := hf.readW (a := VG.Proof.TripleDes.X86_64.savedKeyAddr s) (w := 64)
      (r := ⟨VG.Proof.TripleDes.X86_64.savedKeyAddr s, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact VG.Proof.TripleDes.X86_64.saved_work_disjoint s) (by decide)
    exact hmem.trans hs.saved
  · rw [hrd, hwr, hsave]; exact hs.savedRead
  · rw [hrd, hwr, hcount]; exact hs.countRead
  · rw [hwr, hcount]; exact hs.countWrite
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := hf.readW (a := VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j) (w := 64)
      (r := ⟨VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

theorem passPointer (base : Addr) (c : Nat) (d : VG.Spec.TripleDes.Direction) :
    base + BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset c d) = VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d 0 := by
  cases d
  · change base + BitVec.ofNat 64 (128 * c + 0) = base + BitVec.ofNat 64 (128 * c) + (0 : BitVec 64)
    exact (congrArg (fun n => base + BitVec.ofNat 64 n) (Nat.add_zero (128 * c))).trans
      (BitVec.add_zero (base + BitVec.ofNat 64 (128 * c))).symm
  · simp only [VG.Proof.TripleDes.X86_64.passOffset, VG.Proof.TripleDes.X86_64.keyAddr, VG.Proof.TripleDes.X86_64.componentBase, reduceCtorEq, ite_false]
    rw [Offset.add_ofNat_add_ofNat]


structure Stable (origin s : VG.X86_64.State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion origin] origin.mem s.mem

theorem Stable.refl (s : VG.X86_64.State) : VG.Proof.TripleDes.X86_64.Stable s s :=
  ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : VG.X86_64.State} (hs : VG.Proof.TripleDes.X86_64.Stable s t) (ht : VG.Proof.TripleDes.X86_64.Stable t u) : VG.Proof.TripleDes.X86_64.Stable s u := by
  have hwork : VG.Proof.TripleDes.X86_64.workRegion t = VG.Proof.TripleDes.X86_64.workRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) (hs.regs .rdx (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : VG.X86_64.State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : VG.Spec.TripleDes.Direction)
    (hready : VG.Proof.TripleDes.X86_64.Ready keys base s) (hword : VG.Proof.TripleDes.X86_64.WordState x s) :
    WP isa (pass c d) s (fun t => VG.Proof.TripleDes.X86_64.WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      VG.Proof.TripleDes.X86_64.Ready keys base t ∧ VG.Proof.TripleDes.X86_64.Stable s t) := by
  have hptr : s.mem.readW (VG.Proof.TripleDes.X86_64.savedKeyAddr s) 64 + BitVec.ofNat 64 (VG.Proof.TripleDes.X86_64.passOffset c d) =
      VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d 0 := by
    rw [hready.saved]
    exact VG.Proof.TripleDes.X86_64.passPointer base c d
  apply WP.mono (VG.Proof.TripleDes.X86_64.pass_ok c hc (keys c) d (VG.Proof.TripleDes.X86_64.componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr hready.savedRead hready.countRead hready.countWrite
    (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .rdx (by decide)) ht.rd ht.wr ht.frame,
    ht.rd, ht.wr, ht.regs, ht.frame⟩

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Body`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : Addr) (s : VG.X86_64.State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : VG.Spec.TripleDes.Direction) (hready : VG.Proof.TripleDes.X86_64.Ready keys base s) (hword : VG.Proof.TripleDes.X86_64.WordState x s) :
    WP isa (.seq (pass c₀ d₀) (.seq (pass c₁ d₁) (pass c₂ d₂))) s
      (fun t => VG.Proof.TripleDes.X86_64.WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁
        (desCore (keys c₀) d₀ x))) t ∧ VG.Proof.TripleDes.X86_64.Ready keys base t ∧ VG.Proof.TripleDes.X86_64.Stable s t) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.pass_word_ok keys base s x c₀ h₀ d₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.pass_word_ok keys base s₁ _ c₁ h₁ d₁ hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (VG.Proof.TripleDes.X86_64.pass_word_ok keys base s₂ _ c₂ h₂ d₂ hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1, hs₁.2.2.trans (hs₂.2.2.trans hs₃.2.2)⟩

def blockCore (keys : Nat → DesSchedule) (direction : VG.Spec.TripleDes.Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : VG.X86_64.State) (x : BitVec 64)
    (direction : VG.Spec.TripleDes.Direction) (hready : VG.Proof.TripleDes.X86_64.Ready keys base s) (hword : VG.Proof.TripleDes.X86_64.WordState x s) :
    WP isa (blockBody direction) s
      (fun t => VG.Proof.TripleDes.X86_64.WordState (VG.Proof.TripleDes.X86_64.blockCore keys direction x) t ∧ VG.Proof.TripleDes.X86_64.Ready keys base t ∧ VG.Proof.TripleDes.X86_64.Stable s t) := by
  cases direction
  · exact VG.Proof.TripleDes.X86_64.threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt hready hword
  · exact VG.Proof.TripleDes.X86_64.threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt hready hword

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Bytes`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt m p) = bswap64 (m.readW p 64) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, bswap64_readW]
  simp only [VG.Proof.TripleDes.catBlock, VG.Spec.TripleDes.blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero]
  rfl


theorem bswap64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (bswap64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have hcases : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases hcases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := decide) only [bswap64, extractLsb'_append_byte_hi,
      extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
      BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]


theorem blockAt_writeW (m : Mem) (p : Addr) (x : BitVec 64) :
    VG.Spec.TripleDes.blockAt (m.writeW p (bswap64 x)) p = VG.Spec.TripleDes.encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, VG.Spec.TripleDes.encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact VG.Proof.TripleDes.X86_64.bswap64_byte x i hi

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Permutation`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.TripleDes.X86_64

def permutationCfg : Cfg := { base := .rdx, slots := 0, ext := .rdx, exts := 0 }
def permutationInputs : List (Reg × Nat) := [(.rax, 0)]

def permutationBits {m : Nat} (positions : Vector Nat m) (n p : Nat) : List Nat :=
  if p < m then [n - positions.getD (m - 1 - p) 1] else []

def permutationOutputs {m : Nat} (positions : Vector Nat m) (n : Nat) :
    List (Reg × (Nat → List Nat)) := [(.rbx, VG.Proof.TripleDes.X86_64.permutationBits positions n)]

theorem initialPermutation_check :
    VG.X86_64.Straight.check (lanes 64 6) VG.Proof.TripleDes.X86_64.permutationCfg (linExt 1) (instrs initialPermutation.lit)
      (linEnv VG.Proof.TripleDes.X86_64.permutationInputs) (linPost 6 (VG.Proof.TripleDes.X86_64.permutationOutputs Spec.TripleDes.ip 64)) = true := by
  decide +kernel

theorem finalPermutation_check :
    VG.X86_64.Straight.check (lanes 64 6) VG.Proof.TripleDes.X86_64.permutationCfg (linExt 1) (instrs finalPermutation.lit)
      (linEnv VG.Proof.TripleDes.X86_64.permutationInputs) (linPost 6 (VG.Proof.TripleDes.X86_64.permutationOutputs Spec.TripleDes.fp 64)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    VG.X86_64.Straight.check (lanes 64 6) VG.Proof.TripleDes.X86_64.permutationCfg (linExt 1) (instrs keyPermutation1.lit)
      (linEnv VG.Proof.TripleDes.X86_64.permutationInputs) (linPost 6 (VG.Proof.TripleDes.X86_64.permutationOutputs Spec.TripleDes.pc1 64)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    VG.X86_64.Straight.check (lanes 64 6) VG.Proof.TripleDes.X86_64.permutationCfg (linExt 1) (instrs keyPermutation2.lit)
      (linEnv VG.Proof.TripleDes.X86_64.permutationInputs) (linPost 6 (VG.Proof.TripleDes.X86_64.permutationOutputs Spec.TripleDes.pc2 56)) = true := by
  decide +kernel

theorem permutationCfg_ok (s : VG.X86_64.State) : Ok VG.Proof.TripleDes.X86_64.permutationCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.permutationCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.permutationCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.X86_64.permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (hn64 : n ≤ 64)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (is : List Instr)
    (hchk : VG.X86_64.Straight.check (lanes 64 6) VG.Proof.TripleDes.X86_64.permutationCfg (linExt 1) is
      (linEnv VG.Proof.TripleDes.X86_64.permutationInputs) (linPost 6 (VG.Proof.TripleDes.X86_64.permutationOutputs positions n)) = true)
    (s : VG.X86_64.State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute positions ((s.gpr .rax).setWidth n)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => op.dst != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 64 := fun _ => s.gpr .rax
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ :=
    linear_ok hchk (VG.Proof.TripleDes.X86_64.permutationCfg_ok s) W (fun r i h => by
      simp only [VG.Proof.TripleDes.X86_64.permutationInputs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [VG.Proof.TripleDes.X86_64.permutationCfg] at hj)
  refine ⟨s', hs', ?_, rd, wr, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hout := out .rbx (VG.Proof.TripleDes.X86_64.permutationBits positions n) (by simp [VG.Proof.TripleDes.X86_64.permutationOutputs]) j hj
    change (s'.gpr .rbx).getLsbD j =
      ((Spec.TripleDes.permute positions ((s.gpr .rax).setWidth n)).setWidth 64).getLsbD j
    rw [BitVec.getLsbD_setWidth]
    simp only [hj, decide_true, Bool.true_and]
    rw [hout]
    by_cases hjm : j < m
    · have hk : m - 1 - j < m := by omega
      obtain ⟨hlo, hhi⟩ := bounds _ hk
      have hsource : n - positions.getD (m - 1 - j) 1 < n := by omega
      have h64 : n - positions.getD (m - 1 - j) 1 < 64 := by omega
      rw [VG.Proof.TripleDes.permute_bit positions _ hn j hjm,
        BitVec.getLsbD_setWidth]
      simp only [hsource, decide_true, Bool.true_and, VG.Proof.TripleDes.X86_64.permutationBits, hjm, ite_true,
        xorBits, List.foldr_cons, List.foldr_nil, Bool.xor_false, bitOf,
        Nat.mod_eq_of_lt h64, W]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp only [VG.Proof.TripleDes.X86_64.permutationBits, hjm, ite_false, xorBits, List.foldr_nil]
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.X86_64.permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Initial`. -/
section

namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64

theorem initial_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .rax).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) :=
  VG.Proof.TripleDes.X86_64.fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds (instrs initialPermutation.lit) VG.Proof.TripleDes.X86_64.initialPermutation_check s
end VG.Proof.TripleDes.X86_64
namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64

theorem initial_raw_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .rax) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := VG.Proof.TripleDes.X86_64.initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.X86_64

namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64
theorem final_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .rax).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) :=
  VG.Proof.TripleDes.X86_64.fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds (instrs finalPermutation.lit) VG.Proof.TripleDes.X86_64.finalPermutation_check s

theorem final_raw_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .rax) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := VG.Proof.TripleDes.X86_64.final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.BlockIO`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem readData_ok (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    ∃ s', runBlock isa
      [.mov .rax (.mem (VG.Impl.TripleDes.X86_64.memOp .rsi 0)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  have haddr : s.gpr .rsi + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .rsi :=
    BitVec.add_zero _
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
      State.ea, VG.Impl.TripleDes.X86_64.memOp, haddr, hread, ite_true, Option.map_some,
      gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg_self]
    exact (VG.Proof.TripleDes.X86_64.decodeBlock_readW s.mem (s.gpr .rsi)).symm
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

theorem splitHalves_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa [VG.Impl.TripleDes.X86_64.rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] s = some s' ∧
      s'.gpr .r12 = s.gpr .rbx >>> 32 ∧
      s'.gpr .r13 = ((s.gpr .rbx).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [VG.Impl.TripleDes.X86_64.rr, runBlock_cons, runStep_some, exec, readSrc, execShift,
      Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setReg32, gpr_setReg, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
  · exact gpr_setReg_self _ _ _
  · simp only [State.setReg32, mem_setReg, mem_setFlags]
  · simp only [State.setReg32, rd_setReg, rd_setFlags]
  · simp only [State.setReg32, wr_setReg, wr_setFlags]
  · intro r h12 h13
    simp only [State.setReg32, gpr_setReg, gpr_setFlags, h12, h13, ite_false]


theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : VG.X86_64.State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      VG.Proof.TripleDes.X86_64.runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy

theorem blockLoad_run (s s₁ s₂ s₃ : VG.X86_64.State)
    (h₁ : runBlock isa [.mov .rax (.mem (VG.Impl.TripleDes.X86_64.memOp .rsi 0)), .bswap .rax] s = some s₁)
    (h₂ : runBlock isa (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) s₁ = some s₂)
    (h₃ : runBlock isa [VG.Impl.TripleDes.X86_64.rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] s₂ = some s₃) :
    runBlock isa VG.Impl.TripleDes.X86_64.blockLoad s = some s₃ := by
  have hhead := VG.Proof.TripleDes.X86_64.runAppend_some _ _ _ _ _ h₁ h₂
  have htail := VG.Proof.TripleDes.X86_64.runAppend_some _ _ _ _ _ hhead h₃
  have hcode : VG.Impl.TripleDes.X86_64.blockLoad =
      (([.mov .rax (.mem (VG.Impl.TripleDes.X86_64.memOp .rsi 0)), .bswap .rax] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) ++
      [VG.Impl.TripleDes.X86_64.rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] := rfl
  exact (congrArg (fun is => runBlock isa is s) hcode).trans htail

theorem blockLoad_ok (s : VG.X86_64.State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    ∃ s', runBlock isa VG.Impl.TripleDes.X86_64.blockLoad s = some s' ∧
      s'.gpr .r12 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .r13 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := VG.Proof.TripleDes.X86_64.readData_ok s hread
  obtain ⟨s₂, run₂raw, word₂, rd₂, wr₂, mem₂, regs₂⟩ := VG.Proof.TripleDes.X86_64.initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := VG.Proof.TripleDes.X86_64.splitHalves_ok s₂
  have hword : s₂.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))) := by
    exact word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  refine ⟨s₃, ?_, ?_, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact VG.Proof.TripleDes.X86_64.blockLoad_run s s₁ s₂ s₃ run₁ run₂raw run₃
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans
      (VG.Proof.TripleDes.X86_64.upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hdst : (instrs initialPermutation.lit).all
        (fun op => op.dst == some Reg.rbx || op.dst == some Reg.rbp) = true := by
      decide +kernel
    have hneDst : r ≠ .rbx ∧ r ≠ .rbp := by
      have hfinite : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], q ≠ .rbx ∧ q ≠ .rbp := by decide
      exact hfinite r hr
    have hno : (instrs initialPermutation.lit).all
        (fun op => op.dst != some r) = true := by
      apply List.all_eq_true.mpr
      intro op hop
      have h := List.all_eq_true.mp hdst op hop
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · rw [h, bne_iff_ne]
        intro he
        exact hneDst.1 (Option.some.inj he).symm
      · rw [h, bne_iff_ne]
        intro he
        exact hneDst.2 (Option.some.inj he).symm
    have hne : r ≠ .rax ∧ r ≠ .r12 ∧ r ≠ .r13 := by
      have hfinite : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp],
          q ≠ .rax ∧ q ≠ .r12 ∧ q ≠ .r13 := by decide
      exact hfinite r hr
    exact (regs₃ r hne.2.1 hne.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1))


end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Save`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers and the schedule pointer, in slot order. -/
def savedReg (i : Nat) : Reg := (VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi]).getD i .rdi

theorem blockSave_eq : blockSave = VG.Proof.Rc2.X86_64.saveCode .rdx VG.Proof.TripleDes.X86_64.savedReg 7 := by
  decide +kernel

theorem blockRestore_eq : blockRestore = VG.Proof.Rc2.X86_64.restoreCode .rdx VG.Proof.TripleDes.X86_64.savedReg (List.range 7) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 7, current.mem.readW (current.gpr .rdx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (VG.Proof.TripleDes.X86_64.savedReg i)

theorem blockSave_ok (s : State)
    (hw : ∀ i < 7, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.TripleDes.X86_64.Saved s s' ∧
      VG.Frame [⟨s.gpr .rdx, 56⟩] s.mem s'.mem) := by
  rw [VG.Proof.TripleDes.X86_64.blockSave_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rdx VG.Proof.TripleDes.X86_64.savedReg 7 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 7 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 7 (by decide)

theorem savedReg_separate : ∀ i < 7, VG.Proof.TripleDes.X86_64.savedReg i ≠ .rdx := by decide +kernel

theorem blockRestore_ok (original s : State) (hsaved : VG.Proof.TripleDes.X86_64.Saved original s)
    (hread : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (fun s' =>
      (∀ r ∈ VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi], s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi]) s s') := by
  rw [VG.Proof.TripleDes.X86_64.blockRestore_eq]
  have hregs : (List.range 7).map VG.Proof.TripleDes.X86_64.savedReg = VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi] := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rdx VG.Proof.TripleDes.X86_64.savedReg (List.range 7) original.gpr
    (fun i hi => VG.Proof.TripleDes.X86_64.savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h


theorem savedSlot_work_disjoint (s : State) (i : Nat) (hi : i < 7) :
    (⟨s.gpr .rdx + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : VG.Proof.TripleDes.X86_64.Saved original s)
    (hbase : t.gpr .rdx = s.gpr .rdx) (hf : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion s] s.mem t.mem) :
    VG.Proof.TripleDes.X86_64.Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .rdx + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact VG.Proof.TripleDes.X86_64.savedSlot_work_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Head`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨s.gpr .rdx, 56⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok VG.Proof.TripleDes.X86_64.sboxCfg s
  pointer : s.gpr .rdi = base
  saveRead : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 7, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8
  countRead : InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.countAddr s) 8
  countWrite : InRegions s.wr (VG.Proof.TripleDes.X86_64.countAddr s) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8
  dataSeparate : (⟨s.gpr .rsi, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.workRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j, 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86_64.saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : VG.Proof.TripleDes.X86_64.WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .rsi)))) s
  ready : VG.Proof.TripleDes.X86_64.Ready keys base s
  saved : VG.Proof.TripleDes.X86_64.Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], s.gpr q = original.gpr q
  frame : VG.Frame [VG.Proof.TripleDes.X86_64.saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : VG.Proof.TripleDes.X86_64.HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hsaved : VG.Proof.TripleDes.X86_64.Saved s t) (hf : VG.Frame [VG.Proof.TripleDes.X86_64.saveRegion s] s.mem t.mem) :
    VG.Proof.TripleDes.X86_64.Ready keys base t := by
  have hbase : t.gpr .rdx = s.gpr .rdx := congrFun hg .rdx
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsaved 6 (by decide)).trans hp.pointer
  · rw [hrd, hwr, show VG.Proof.TripleDes.X86_64.savedKeyAddr t = VG.Proof.TripleDes.X86_64.savedKeyAddr s from congrArg (· + BitVec.ofNat 64 48) hbase]
    exact hp.saveRead 6 (by decide)
  · rw [hrd, hwr, show VG.Proof.TripleDes.X86_64.countAddr t = VG.Proof.TripleDes.X86_64.countAddr s from congrArg (· + BitVec.ofNat 64 56) hbase]
    exact hp.countRead
  · rw [hwr, show VG.Proof.TripleDes.X86_64.countAddr t = VG.Proof.TripleDes.X86_64.countAddr s from congrArg (· + BitVec.ofNat 64 56) hbase]
    exact hp.countWrite
  · rw [hrd, hwr]; exact hp.read
  · rw [show VG.Proof.TripleDes.X86_64.workRegion t = VG.Proof.TripleDes.X86_64.workRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j) (w := 64)
      (r := ⟨VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : VG.Proof.TripleDes.X86_64.HeadPre keys base s) :
    WP isa (.block (blockSave ++ blockLoad)) s (VG.Proof.TripleDes.X86_64.HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (VG.Proof.TripleDes.X86_64.blockSave_ok s hp.saveWrite)
  intro s₁ hs₁
  have hready := VG.Proof.TripleDes.X86_64.ready_afterSave hp hs₁.1 hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2.1 hs₁.2.2.2.2
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 8 := by
    rw [hs₁.2.1, hs₁.2.2.1, hs₁.1]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (s₁.gpr .rsi) =
      Spec.TripleDes.blockAt s.mem (s.gpr .rsi) := by
    rw [hs₁.1]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.2.2.2.2
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, regs₂⟩ := VG.Proof.TripleDes.X86_64.blockLoad_ok s₁ hread₁
  have hframe : VG.Frame [VG.Proof.TripleDes.X86_64.workRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .rdx (by decide)) rd₂ wr₂ hframe,
    hs₁.2.2.2.1.congr (regs₂ .rdx (by decide)) hframe,
    rd₂.trans hs₁.2.1, wr₂.trans hs₁.2.2.1, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.1 q)
  · rw [mem₂]; exact hs₁.2.2.2.2

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Store`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem packHalves_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa [VG.Impl.TripleDes.X86_64.rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] s = some s' ∧
      s'.gpr .rax = (s.gpr .r12).rotateRight 32 ^^^ s.gpr .r13 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [VG.Impl.TripleDes.X86_64.rr, runBlock_cons, runStep_some, exec, execShift,
      readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact gpr_setReg_self _ _ _
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false]

theorem storeTail_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa [.bswap .rbx, VG.Impl.TripleDes.X86_64.rr .rax .rbx] s = some s' ∧
      s'.gpr .rax = bswap64 (s.gpr .rbx) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [VG.Impl.TripleDes.X86_64.rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      Option.map_some, gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact gpr_setReg_self _ _ _
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hrax hrbx
    simp only [gpr_setReg, hrax, hrbx, ite_false]


theorem blockStore_run (s s₁ s₂ s₃ : VG.X86_64.State)
    (h₁ : runBlock isa [VG.Impl.TripleDes.X86_64.rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] s = some s₁)
    (h₂ : runBlock isa (permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) s₁ = some s₂)
    (h₃ : runBlock isa [.bswap .rbx, VG.Impl.TripleDes.X86_64.rr .rax .rbx] s₂ = some s₃) :
    runBlock isa VG.Impl.TripleDes.X86_64.blockStore s = some s₃ := by
  have hhead := VG.Proof.TripleDes.X86_64.runAppend_some _ _ _ _ _ h₁ h₂
  have htail := VG.Proof.TripleDes.X86_64.runAppend_some _ _ _ _ _ hhead h₃
  have hcode : VG.Impl.TripleDes.X86_64.blockStore =
      (([VG.Impl.TripleDes.X86_64.rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] : List Instr) ++
        permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) ++ [.bswap .rbx, VG.Impl.TripleDes.X86_64.rr .rax .rbx] := rfl
  exact (congrArg (fun is => runBlock isa is s) hcode).trans htail

theorem blockStore_ok (s : VG.X86_64.State) (l r : BitVec 32)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64) :
    ∃ s', runBlock isa VG.Impl.TripleDes.X86_64.blockStore s = some s' ∧
      s'.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := VG.Proof.TripleDes.X86_64.packHalves_ok s
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := VG.Proof.TripleDes.X86_64.final_raw_ok s₁
  obtain ⟨s₃, run₃, word₃, mem₃, rd₃, wr₃, regs₃⟩ := VG.Proof.TripleDes.X86_64.storeTail_ok s₂
  have hword : s₁.gpr .rax = l ++ r := by
    rw [hl, hr] at word₁
    exact word₁.trans (VG.Proof.TripleDes.packHalves_word l r)
  refine ⟨s₃, VG.Proof.TripleDes.X86_64.blockStore_run s s₁ s₂ s₃ run₁ run₂ run₃, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact word₃.trans (congrArg bswap64 (word₂.trans
      (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) hword)))
  · intro q hq
    have hneq : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], q ≠ .rax ∧ q ≠ .rbx ∧ q ≠ .rbp := by decide
    have hdst : (instrs finalPermutation.lit).all
        (fun op => op.dst == some Reg.rbx || op.dst == some Reg.rbp) = true := by decide +kernel
    have hno : (instrs finalPermutation.lit).all (fun op => op.dst != some q) = true := by
      apply List.all_eq_true.mpr
      intro op hop
      have h := List.all_eq_true.mp hdst op hop
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · rw [h, bne_iff_ne]
        intro he
        exact (hneq q hq).2.1 (Option.some.inj he).symm
      · rw [h, bne_iff_ne]
        intro he
        exact (hneq q hq).2.2 (Option.some.inj he).symm
    exact (regs₃ q (hneq q hq).1 (hneq q hq).2.1).trans
      ((regs₂ q hno).trans (regs₁ q (hneq q hq).1))


theorem writeData_ok (s : VG.X86_64.State) (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    ∃ s', runBlock isa [.store (VG.Impl.TripleDes.X86_64.memOp .rsi 0) .rax] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rsi) (s.gpr .rax) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have haddr : s.gpr .rsi + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .rsi := BitVec.add_zero _
  refine ⟨{ s with mem := s.mem.writeW (s.gpr .rsi) (s.gpr .rax) }, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
      State.ea, VG.Impl.TripleDes.X86_64.memOp, haddr, hwrite, ite_true], rfl, rfl, rfl, rfl⟩

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Tail`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .rsi) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi], s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : VG.Frame [⟨origin.gpr .rsi, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : VG.Proof.TripleDes.X86_64.WordState x s) (hsaved : VG.Proof.TripleDes.X86_64.Saved original s)
    (hsavedRead : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (.block (blockStore ++ blockRestore ++ ([.store (memOp .rsi 0) .rax] : List Instr)))
      s (VG.Proof.TripleDes.X86_64.TailPost original s x) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ :=
    VG.Proof.TripleDes.X86_64.blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right
  have word : s₁.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    word₁.trans (congrArg (fun v => bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp v))
      (VG.Proof.TripleDes.halves_append x))
  have saved₁ : VG.Proof.TripleDes.X86_64.Saved original s₁ := by
    intro i hi
    rw [regs₁ .rdx (by decide), mem₁]
    exact hsaved i hi
  have savedRead₁ : ∀ i < 7, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .rdx (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (VG.Proof.TripleDes.X86_64.blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hnonsaved : ∀ q ∈ [Reg.rax, .rsi, .rdx, .rsp], q ∉ VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi] := by decide
  have hrax₂ : s₂.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    (hs₂.2.reg .rax (hnonsaved .rax (by decide))).trans word
  have hregs₂ : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ [Reg.rax, .rsi, .rdx, .rsp] ∧
      r ∈ [Reg.rdi, .rsi, .rdx, .rsp] := by decide
    exact (hs₂.2.reg q (hnonsaved q (hkeep q hq).1)).trans (regs₁ q (hkeep q hq).2)
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .rsi) 8 := by
    rw [hs₂.2.wr, wr₁, hregs₂ .rsi (by decide)]
    exact hwrite
  obtain ⟨s₃, run₃, mem₃, gpr₃, rd₃, wr₃⟩ := VG.Proof.TripleDes.X86_64.writeData_ok s₂ hwrite₂
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, ?_, rd₃.trans (hs₂.2.rd.trans rd₁),
    wr₃.trans (hs₂.2.wr.trans wr₁), ?_, ?_⟩
  · rw [mem₃, hs₂.2.mem, mem₁, hregs₂ .rsi (by decide), hrax₂]
    exact VG.Proof.TripleDes.X86_64.blockAt_writeW s.mem (s.gpr .rsi) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · intro r hr
    rw [gpr₃]
    exact hs₂.1 r hr
  · intro q hq
    rw [gpr₃]
    exact hregs₂ q hq
  · rw [mem₃, hs₂.2.mem, mem₁, hregs₂ .rsi (by decide)]
    exact VG.Proof.TripleDes.X86_64.countWrite_frame s.mem (s.gpr .rsi) (s₂.gpr .rax)

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Block`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (VG.Proof.TripleDes.X86_64.blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      VG.Proof.TripleDes.X86_64.blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (original.gpr .rsi) =
    VG.Proof.TripleDes.X86_64.blockResult keys direction (Spec.TripleDes.blockAt original.mem (original.gpr .rsi))
  saved : ∀ r ∈ VG.Impl.TripleDes.X86_64.savedRegs ++ [Reg.rdi], s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = original.gpr q
  frame : VG.Frame (VG.Proof.TripleDes.X86_64.blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : Addr) (direction : Direction) (s : State)
    (hp : VG.Proof.TripleDes.X86_64.HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (block direction) s (VG.Proof.TripleDes.X86_64.BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86_64.blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ [Reg.rdi, .rsi, .rdx, .rsp] := by decide
    exact (hs₂.2.2.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.regs .rdx (by decide)) hs₂.2.2.frame
  have savedRead₂ : ∀ i < 7, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [hs₂.2.2.rd, hs₂.2.2.wr, hs₁.rd, hs₁.wr, hregs₂ .rdx (by decide)]
    exact hp.saveRead
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .rsi) 8 := by
    rw [hs₂.2.2.wr, hs₁.wr, hregs₂ .rsi (by decide)]
    exact hwrite
  apply WP.mono (VG.Proof.TripleDes.X86_64.blockTail_ok s s₂ _ hs₂.1 saved₂ savedRead₂ hwrite₂)
  intro s₃ hs₃
  refine ⟨?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.wr.trans hs₁.wr),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .rsi (by decide)] at hresult
    exact hresult.trans (VG.Proof.TripleDes.X86_64.blockResult_core keys direction _)
  · have hf₁ : VG.Frame (VG.Proof.TripleDes.X86_64.blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨s.gpr .rdx, 512⟩, by simp [VG.Proof.TripleDes.X86_64.blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : VG.Frame (VG.Proof.TripleDes.X86_64.blockRegions s) s₁.mem s₂.mem := hs₂.2.2.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨s.gpr .rdx, 512⟩, by simp [VG.Proof.TripleDes.X86_64.blockRegions], ?_⟩
      have hbase := hs₁.regs .rdx (by decide)
      change Region.Sub ⟨s₁.gpr .rdx + BitVec.ofNat 64 56, 392⟩ ⟨s.gpr .rdx, 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : VG.Frame (VG.Proof.TripleDes.X86_64.blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .rsi (by decide)]
      exact ⟨⟨s.gpr .rsi, 8⟩, by simp [VG.Proof.TripleDes.X86_64.blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit`. -/
section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.X86_64.roundBody
materialize_value Impl.TripleDes.X86_64.blockLoad
materialize_value Impl.TripleDes.X86_64.blockStore

/-! The functions. -/

materialize_code Impl.TripleDes.X86_64.encryptBlock
materialize_code Impl.TripleDes.X86_64.decryptBlock
materialize_code Impl.TripleDes.X86_64.Key.expandKey

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

def PublicRegs (rs : List Reg) (s₁ s₂ : VG.X86_64.State) : Prop :=
  ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

def blockTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx], flags := false,
    lens := [0, 512], bases := [(.rdx, 1, 0)] }

/-- What the rounds need public: the pointers, the round counter and the
saved ones in the scratch buffer. -/
def roundTaint : X86_64.Taint.T :=
  { regs := .ofList [.rax, .rdx, .rsi, .rdi], flags := false,
    lens := [0, 512], bases := [(.rdx, 1, 0)], slots := [(1, 56, 8), (1, 48, 8)] }

/-! Each function runs the loop of rounds three times, two of them in each
direction: their bodies are analysed once, as summaries. -/

taint_summary roundEnc : taintS VG.Proof.TripleDes.X86_64.roundTaint (.block (roundBody ++ roundAdvance .encrypt))
taint_summary roundDec : taintS VG.Proof.TripleDes.X86_64.roundTaint (.block (roundBody ++ roundAdvance .decrypt))

theorem encryptBlock_taint : ∃ h, (taintS.check VG.Proof.TripleDes.X86_64.blockTaint VG.Impl.TripleDes.X86_64.encryptBlock h).isSome = true := by
  taint_decide_sum [roundEnc, roundDec]

theorem decryptBlock_taint : ∃ h, (taintS.check VG.Proof.TripleDes.X86_64.blockTaint VG.Impl.TripleDes.X86_64.decryptBlock h).isSome = true := by
  taint_decide_sum [roundEnc, roundDec]

theorem encryptBlock_constantTime (pre : VG.X86_64.State → Prop) (pub : VG.X86_64.State → VG.X86_64.State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree VG.Proof.TripleDes.X86_64.blockTaint s t) :
    ConstantTime isa pre pub VG.Impl.TripleDes.X86_64.encryptBlock :=
  let ⟨_, h⟩ := VG.Proof.TripleDes.X86_64.encryptBlock_taint
  VG.Taint.constantTime (A := taintS) VG.Proof.TripleDes.X86_64.blockTaint hagree h

theorem decryptBlock_constantTime (pre : VG.X86_64.State → Prop) (pub : VG.X86_64.State → VG.X86_64.State → Prop)
    (hagree : ∀ s t, pre s → pre t → pub s t → X86_64.Taint.Agree VG.Proof.TripleDes.X86_64.blockTaint s t) :
    ConstantTime isa pre pub VG.Impl.TripleDes.X86_64.decryptBlock :=
  let ⟨_, h⟩ := VG.Proof.TripleDes.X86_64.decryptBlock_taint
  VG.Taint.constantTime (A := taintS) VG.Proof.TripleDes.X86_64.blockTaint hagree h

theorem expandKey_constantTime (pre : VG.X86_64.State → Prop) :
    ConstantTime isa pre (VG.Proof.TripleDes.X86_64.PublicRegs [.rdi, .rsi, .rdx, .rcx]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact Taint.agree_ofRegs hp

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.Pre`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 384⟩
    let data : Region := ⟨s.gpr .rsi, 8⟩
    let scratch : Region := ⟨s.gpr .rdx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .rsi) =
    VG.Proof.TripleDes.X86_64.blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))
  pub := VG.Proof.TripleDes.X86_64.PublicRegs [.rdi, .rsi, .rdx]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : VG.Proof.TripleDes.X86_64.selectedRound d j < 16 := by
  cases d <;> simp only [VG.Proof.TripleDes.X86_64.selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + VG.Proof.TripleDes.X86_64.selectedRound d j)) := by
  unfold VG.Proof.TripleDes.X86_64.keyAddr VG.Proof.TripleDes.X86_64.componentBase VG.Proof.TripleDes.X86_64.selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)

theorem headPre_of_contract (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.X86_64.blockContract d).pre s) :
    VG.Proof.TripleDes.X86_64.HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)))
      (s.gpr .rdi) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, _, _⟩ := hs
  have scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have scratchReads : ∀ i < 64, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨s.gpr .rdx, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have spills : Ok VG.Proof.TripleDes.X86_64.sboxCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keyContains : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      (⟨s.gpr .rdi, 384⟩ : Region).Contains (VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase (s.gpr .rdi) c) direction j) 8 := by
    intro c hc direction j hj
    rw [VG.Proof.TripleDes.X86_64.keyAddr_component]
    have hindex := VG.Proof.TripleDes.X86_64.selectedRound_bound direction j hj
    exact Offset.contains_base _ (by omega) (by omega)
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨VG.Proof.TripleDes.X86_64.keyAddr (VG.Proof.TripleDes.X86_64.componentBase (s.gpr .rdi) c) direction j, 8⟩ ⟨s.gpr .rdi, 384⟩ := by
    intro c hc direction j hj
    rw [VG.Proof.TripleDes.X86_64.keyAddr_component]
    have hindex := VG.Proof.TripleDes.X86_64.selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega)
  have workSub : Region.Sub (VG.Proof.TripleDes.X86_64.workRegion s) ⟨s.gpr .rdx, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (VG.Proof.TripleDes.X86_64.saveRegion s) ⟨s.gpr .rdx, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨spills, rfl, (fun i hi => scratchReads i (by omega)),
    (fun i hi => scratchWrites i (by omega)), scratchReads 7 (by decide),
    scratchWrites 7 (by decide), ?_, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  · intro c hc direction j hj
    rw [hrd, hwr]
    exact ⟨⟨s.gpr .rdi, 384⟩, by simp, keyContains c hc direction j hj⟩
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [VG.Proof.TripleDes.X86_64.keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .rdi) c
      (VG.Proof.TripleDes.X86_64.selectedRound direction j) hc (VG.Proof.TripleDes.X86_64.selectedRound_bound direction j hj)).symm


theorem blockTaint_wf (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.X86_64.blockContract d).pre s) :
    Taint.Wf VG.Proof.TripleDes.X86_64.blockTaint s := by
  obtain ⟨_, hwr, _, dataSep, _, _⟩ := hs
  refine ⟨?_, ?_⟩
  · intro _
    rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 8; decide)
        (List.Forall₂.cons (by change 512 ≤ 512; decide) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 8 ≤ 2 ^ 64; decide
      · change 512 ≤ 2 ^ 64; decide
  · intro p hp
    simp only [VG.Proof.TripleDes.X86_64.blockTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rdx = s.gpr .rdx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem blockTaint_agree (d : Direction) (s t : State)
    (hs : (VG.Proof.TripleDes.X86_64.blockContract d).pre s) (ht : (VG.Proof.TripleDes.X86_64.blockContract d).pre t)
    (hp : (VG.Proof.TripleDes.X86_64.blockContract d).pub s t) : X86_64.Taint.Agree VG.Proof.TripleDes.X86_64.blockTaint s t := by
  refine ⟨?_, ?_, VG.Proof.TripleDes.X86_64.blockTaint_wf d s hs, VG.Proof.TripleDes.X86_64.blockTaint_wf d t ht, ?_, ?_, ?_⟩
  · constructor
    · intro r hr
      exact hp r (by simpa only [VG.Proof.TripleDes.X86_64.blockTaint, RegSet.mem_ofList] using hr)
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, hp .rsi (by decide), hp .rdx (by decide)]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [VG.Proof.TripleDes.X86_64.blockTaint, RegSet.not_mem_empty] at hr

end VG.Proof.TripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86_64.VerifiedBlock`. -/
section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

theorem block_gprCorrect (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.X86_64.blockContract d).pre s) :
    WP isa (block d) s (fun s' => gprPreserved s s' ∧ (VG.Proof.TripleDes.X86_64.blockContract d).post s s') := by
  have hp := VG.Proof.TripleDes.X86_64.headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .rsi) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .rsi, 8⟩, by simp, Region.contains_self _ _⟩
  apply WP.mono (VG.Proof.TripleDes.X86_64.block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rdi) d s hp hwrite)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, hpost.result⟩
  · intro r hr
    have hkeep : ∀ q ∈ calleeSaved,
        q ∈ savedRegs ++ [Reg.rdi] ∨ q ∈ [Reg.rsi, .rdx, .rsp] := by decide
    rcases hkeep r hr with h | h
    · exact hpost.saved r h
    · exact hpost.regs r h
  · apply hpost.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [VG.Proof.TripleDes.X86_64.blockRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.2.2.2.1
    · exact hs.2.2.2.2.2

theorem encrypt_correct (s : State) (hs : (VG.Proof.TripleDes.X86_64.blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.TripleDes.X86_64.blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.X86_64.block_gprCorrect .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.TripleDes.X86_64.blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.TripleDes.X86_64.blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.TripleDes.X86_64.block_gprCorrect .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem publicRegs_three (s t : State) : VG.Proof.TripleDes.X86_64.PublicRegs [.rdi, .rsi, .rdx] s t ↔
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx := by
  simp [VG.Proof.TripleDes.X86_64.PublicRegs]

theorem encrypt_verified : Verified target encryptBlock (Spec.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.encrypt_correct
    (VG.Proof.TripleDes.X86_64.encryptBlock_constantTime _ _ (VG.Proof.TripleDes.X86_64.blockTaint_agree .encrypt)) ?_
  sig_implies [Spec.TripleDes.encryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs,
    VG.Proof.TripleDes.X86_64.blockContract, VG.Proof.TripleDes.X86_64.publicRegs_three, VG.Proof.TripleDes.X86_64.blockResult] [satState] using VG.Proof.TripleDes.X86_64.satState

theorem decrypt_verified : Verified target decryptBlock (Spec.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.TripleDes.X86_64.decrypt_correct
    (VG.Proof.TripleDes.X86_64.decryptBlock_constantTime _ _ (VG.Proof.TripleDes.X86_64.blockTaint_agree .decrypt)) ?_
  sig_implies [Spec.TripleDes.decryptBlockContract, Spec.TripleDes.blockSig, abi, argRegs,
    VG.Proof.TripleDes.X86_64.blockContract, VG.Proof.TripleDes.X86_64.publicRegs_three, VG.Proof.TripleDes.X86_64.blockResult] [satState] using VG.Proof.TripleDes.X86_64.satState

end VG.Proof.TripleDes.X86_64

end
