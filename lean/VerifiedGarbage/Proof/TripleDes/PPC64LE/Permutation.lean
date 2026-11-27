module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.Proof.Framework.PPC64LE.Linear
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-! ### `TripleDes.PPC64LE.ConstantTime`, which the modules that import this one used -/

section

/-! # Constant-time Triple DES block and key-expansion programs -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.r3, .r4, .r5]) Key.expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.TripleDes.PPC64LE

end

end

/-! ### `TripleDes.PPC64LE.Word`, which the modules that import this one used -/

section

/-! ### `TripleDes.PPC64LE.Write`, which the modules that import this one used -/

section

/-! ### `TripleDes.PPC64LE.Bytes`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) = rev64 (m.readW p 64) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, rev64_readW]
  simp only [VG.Proof.TripleDes.catBlock, blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero]
  rfl


theorem rev64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (rev64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have hcases : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases hcases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := decide) only [rev64, extractLsb'_append_byte_hi,
      extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
      BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]


theorem blockAt_writeW (m : Mem) (p : Addr) (x : BitVec 64) :
    blockAt (m.writeW p (rev64 x)) p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega_using [hi] : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact rev64_byte x i hi

end VG.Proof.TripleDes.PPC64LE

end

end

/-! # Reading a PPC64LE state through register writes -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE

theorem gpr_write (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.write d v).gpr r = if r = d then v else s.gpr r := rfl

theorem gpr_write_self (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).gpr d = v := by
  simp [State.write]

theorem gpr_write_of_ne (s : State) {d r : Reg} (v : BitVec 64) (h : r ≠ d) :
    (s.write d v).gpr r = s.gpr r := by
  simp [State.write, h]

/-- `s'` is `s` but for the registers `written`. -/
structure Kept (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

end VG.Proof.TripleDes.PPC64LE

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

theorem mask_word (x : BitVec 64) (n : Nat) (hn : 0 < n) (hn64 : n ≤ 64) :
    (x <<< (64 - n)) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < n
  · have hi : 64 - n + j < 64 := by omega
    have hlo : ¬64 - n + j < 64 - n := by omega_using []
    simp only [hi, hlo, h, hj, decide_true, decide_false, Bool.not_false,
      Bool.true_and, show 64 - n + j - (64 - n) = j by omega_using []]
  · have ho : ¬64 - n + j < 64 := by omega_using [h]
    simp only [ho, h, hj, decide_true, decide_false, Bool.false_and, Bool.true_and]

theorem packHalves_shift (l r : BitVec 32) :
    l.setWidth 64 <<< 32 ^^^ r.setWidth 64 = l ++ r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : j < 32
  · simp [h, hj]
  · have hb : j - 32 < 32 := by omega_using [hj]
    simp [h, hj, hb, show j - 32 < 64 by omega_using [hj],
      BitVec.getLsbD_of_ge r j (by omega_using [h])]

theorem pack28_shift (c d : BitVec 28) :
    ((c.setWidth 64 <<< 28) ^^^ d.setWidth 64).setWidth 56 = c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  by_cases h : j < 28
  · simp [h, show j < 64 by omega_using [hj]]
  · simp [h, show j < 64 by omega_using [hj], show j - 28 < 28 by omega_using [hj],
      show j - 28 < 64 by omega_using [hj], BitVec.getLsbD_of_ge d j (by omega_using [h])]


end VG.Proof.TripleDes.PPC64LE

end

end

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.TripleDes.PPC64LE

def permutationCfg : Cfg := { base := .r5, slots := 0, ext := .r5, exts := 0 }
def permutationInputs (src : Reg) : List (Reg × Nat) := [(src, 0)]

def permutationBits {m : Nat} (positions : Vector Nat m) (n p : Nat) : List Nat :=
  if p < m then [n - positions.getD (m - 1 - p) 1] else []

def permutationOutputs {m : Nat} (positions : Vector Nat m) (n : Nat) (dst : Reg) :
    List (Reg × (Nat → List Nat)) := [(dst, permutationBits positions n)]

theorem initialPermutation_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs initialPermutation.lit)
      (linEnv (permutationInputs .r7)) (linPost 6 (permutationOutputs Spec.TripleDes.ip 64 .r8)) = true := by
  decide +kernel

theorem finalPermutation_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs finalPermutation.lit)
      (linEnv (permutationInputs .r6)) (linPost 6 (permutationOutputs Spec.TripleDes.fp 64 .r8)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs keyPermutation1.lit)
      (linEnv (permutationInputs .r8)) (linPost 6 (permutationOutputs Spec.TripleDes.pc1 64 .r9)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    check (lanes 64 6) permutationCfg (linExt 1) (instrs keyPermutation2.lit)
      (linEnv (permutationInputs .r8)) (linPost 6 (permutationOutputs Spec.TripleDes.pc2 56 .r9)) = true := by
  decide +kernel

theorem permutationCfg_ok (s : State) : Ok permutationCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (hn64 : n ≤ 64)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (src dst : Reg) (is : List Instr)
    (hchk : check (lanes 64 6) permutationCfg (linExt 1) is
      (linEnv (permutationInputs src)) (linPost 6 (permutationOutputs positions n dst)) = true)
    (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dst = (Spec.TripleDes.permute positions ((s.gpr src).setWidth n)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => dstOf op != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 64 := fun _ => s.gpr src
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ :=
    linear_ok hchk (permutationCfg_ok s) W (fun r i h => by
      simp only [permutationInputs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [permutationCfg] at hj)
  refine ⟨s', hs', ?_, rd, wr, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hout := out dst (permutationBits positions n) (by simp [permutationOutputs]) j hj
    change (s'.gpr dst).getLsbD j =
      ((Spec.TripleDes.permute positions ((s.gpr src).setWidth n)).setWidth 64).getLsbD j
    rw [BitVec.getLsbD_setWidth]
    simp only [hj, decide_true, Bool.true_and]
    rw [hout]
    by_cases hjm : j < m
    · have hk : m - 1 - j < m := by omega_using [hjm]
      obtain ⟨hlo, hhi⟩ := bounds _ hk
      have hsource : n - positions.getD (m - 1 - j) 1 < n := by omega_using [hn, hlo]
      have h64 : n - positions.getD (m - 1 - j) 1 < 64 := by omega_using [hn64, hlo]
      rw [VG.Proof.TripleDes.permute_bit positions _ hn j hjm,
        BitVec.getLsbD_setWidth]
      simp only [hsource, decide_true, Bool.true_and, permutationBits, hjm, ite_true,
        xorBits, List.foldr_cons, List.foldr_nil, Bool.xor_false, bitOf,
        Nat.mod_eq_of_lt h64, W]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hjm])]
      simp only [permutationBits, hjm, ite_false, xorBits, List.foldr_nil]
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.PPC64LE
