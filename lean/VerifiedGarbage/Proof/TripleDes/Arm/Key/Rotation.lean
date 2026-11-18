module

import VerifiedGarbage.Proof.TripleDes.KeySchedule
public import VerifiedGarbage.Proof.Rc2.Arm.Lookup
public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.AddrArith
meta import Lean.Elab.Tactic.Omega.Frontend
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.TripleDes.Arm.Lit
import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `TripleDes.Arm.Permutation`, which only this module used -/

section

@[expose] public section

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
  [(lo, permutationBits positions n srcSplit dstSplit 0),
   (hi, permutationBits positions n srcSplit (m - dstSplit) dstSplit)]

theorem keyPermutation1_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs keyPermutation1.lit)
      (linEnv (permutationInputs .r5 .r4)) (linPost 6 (permutationOutputs Spec.TripleDes.pc1 64 32 28 .r11 .r10)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs keyPermutation2.lit)
      (linEnv (permutationInputs .r11 .r10)) (linPost 6 (permutationOutputs Spec.TripleDes.pc2 56 28 32 .r4 .r5)) = true := by
  decide +kernel

def packedInput (n split : Nat) (lo hi : BitVec 32) : BitVec n :=
  ((hi.setWidth (n - split)) ++ lo.setWidth split).setWidth n

theorem packedInput_bit (n split : Nat) (lo hi : BitVec 32) (k : Nat)
    (hk : k < n) (hs : split ≤ n) :
    (packedInput n split lo hi).getLsbD k =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split) := by
  simp only [packedInput, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and,
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
      (permutationBits positions n split width start p) =
    (((Spec.TripleDes.permute positions (packedInput n split lo hi) >>> start).setWidth width).setWidth 32).getLsbD p := by
  simp only [BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
  by_cases hw' : p < width
  · have hm : start + p < m := by omega_using [hw, hw']
    simp only [hw', decide_true, Bool.true_and]
    have hk : m - 1 - (start + p) < m := by omega_using [hw, hw']
    obtain ⟨hb, ht⟩ := bounds _ hk
    have hn' : n - positions.getD (m - 1 - (start + p)) 1 < n := by omega_using [hn, hb]
    rw [VG.Proof.TripleDes.permute_bit positions _ hn _ hm, packedInput_bit _ _ _ _ _ hn' hs]
    simp only [permutationBits, hw', hm, and_self, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false]
    let k := n - positions.getD (m - 1 - (start + p)) 1
    change bitOf (fun i => if i = 0 then lo else hi) (if k < split then k else 32 + k - split) =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split)
    by_cases h : k < split
    · have h32 : k < 32 := by omega_using [hlo, h]
      simp only [h, ite_true, bitOf, Nat.div_eq_of_lt h32, Nat.mod_eq_of_lt h32]
    · have h32 : k - split < 32 := by change n - positions.getD (m - 1 - (start + p)) 1 < n at hn'; dsimp [k]; omega_using [hhi, hb]
      have he : 32 + k - split = 32 * 1 + (k - split) := by omega_using [h]
      simp only [h, ite_false, he, bitOf_word _ _ _ h32]
      rfl
  · simp only [hw', decide_false, Bool.false_and, permutationBits, false_and, ite_false, xorBits_nil]

theorem permutationCfg_ok (s : State) : Ok permutationCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [permutationCfg] at hk
  · intro k hk; simp [permutationCfg] at hk
  · change (s.gpr .r2).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .r2).isLt
    omega_using []
  · intro k hk; simp [permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split dstSplit : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32) (hd : dstSplit ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (srcLo srcHi dstLo dstHi : Reg) (is : List Instr)
    (hchk : check (lanes 32 6) permutationCfg (linExt 2) is
      (linEnv (permutationInputs srcLo srcHi))
      (linPost 6 (permutationOutputs positions n split dstSplit dstLo dstHi)) = true)
    (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dstLo = ((Spec.TripleDes.permute positions
        (packedInput n split (s.gpr srcLo) (s.gpr srcHi))).setWidth dstSplit).setWidth 32 ∧
      s'.gpr dstHi = ((Spec.TripleDes.permute positions
        (packedInput n split (s.gpr srcLo) (s.gpr srcHi)) >>> dstSplit).setWidth (m - dstSplit)).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => !clobbers op r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr srcLo else s.gpr srcHi
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ :=
    linear_ok hchk (permutationCfg_ok s) W (fun r i h => by
      simp only [permutationInputs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [permutationCfg] at hj)
  refine ⟨s', hs', ?_, ?_, rd, wr, sp, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstLo (permutationBits positions n split dstSplit 0) (by simp [permutationOutputs]) p hp
    rw [h]
    have hbits := permutationBits_ok positions hn split dstSplit 0 hs hlo hhi (by omega_using [hd]) bounds (s.gpr srcLo) (s.gpr srcHi) p hp
    simpa only [BitVec.ushiftRight_zero] using hbits
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstHi (permutationBits positions n split (m - dstSplit) dstSplit)
      (by simp [permutationOutputs]) p hp
    rw [h]
    exact permutationBits_ok positions hn split (m - dstSplit) dstSplit hs hlo hhi
      (by omega_using [hd]) bounds _ _ p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.Arm

end

end

/-! ### `TripleDes.Arm.WordStore`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.Arm
open VG

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega_using [])
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [getLsbD_read m n (a + 1) (i - 8) (by omega_using [h, hi])]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega_using []
      have e2 : (i - 8) % 8 = i % 8 := by omega_using [hi]
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega_using [hi]

theorem readW_pair (m : Mem) (p : Addr) :
    m.readW (p + 4) 32 ++ m.readW p 32 = m.readW p 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases hlo : i < 32
  · rw [ite_eq_left hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hlo, hi, decide_true, Bool.true_and]
    rw [getLsbD_read m 4 p i (by omega_using [hlo]), getLsbD_read m 8 p i (by omega_using [hi])]
  · rw [ite_eq_right hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hi,
      show i - 32 < 32 by omega_using [hi], decide_true, Bool.true_and]
    rw [getLsbD_read m 4 (p + 4) (i - 32) (by omega_using [hi]), getLsbD_read m 8 p i (by omega_using [hi])]
    have ha : 4 + (i - 32) / 8 = i / 8 := by omega_using [hlo]
    have hb : (i - 32) % 8 = i % 8 := by omega_using [hlo]
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
    have hb : (a - p).toNat < 8 := by omega_using [hhi, he]
    rw [ite_eq_left hhi, ite_eq_left hb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp (disch := omega_using []) only [ite_eq_right, he]
    apply congrArg (fun b => decide (i < 8) && b)
    apply congrArg hi.getLsbD
    omega_using []
  · rw [ite_eq_right hhi]
    by_cases hlo : (a - p).toNat < 4
    · have hb : (a - p).toNat < 8 := by omega_using [hlo]
      rw [ite_eq_left hlo, ite_eq_left hb]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi'
      simp (disch := omega_using [hlo, hi']) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
        ite_eq_left]
    · have hb : ¬ (a - p).toNat < 8 := by bv_omega
      rw [ite_eq_right hlo, ite_eq_right hb]

end VG.Proof.TripleDes.Arm

end

end

/-! ### `TripleDes.Arm.Key.Permutation`, which the modules that import this one used -/

section

/-! ### `TripleDes.Arm.Bytes`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) = rev (m.readW p 32) ++ rev (m.readW (p + 4) 32) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, rev_readW, rev_readW]
  simp only [VG.Proof.TripleDes.catBlock, blockAt, Vector.getElem_ofFn,
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
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega_arith
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega_arith) only [BitVec.getLsbD_append, ↓ite_eq_left, ↓ite_eq_right,
      Nat.sub_sub] <;> rfl

theorem packed28 (c d : BitVec 28) :
    packedInput 56 28 (d.setWidth 32) (c.setWidth 32) = c ++ d := by
  simp only [packedInput, BitVec.setWidth_setWidth_of_le _ (by decide : 28 ≤ 32),
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
    blockAt (m.writeW p (byteRev64 x)) p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega_arith : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact byteRev64_byte x i hi

theorem revPair (l r : BitVec 32) : rev r ++ rev l = byteRev64 (l ++ r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega_arith
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega_arith) only [rev, byteRev64, BitVec.getLsbD_append,
      BitVec.getLsbD_extractLsb', ite_eq_left, ite_eq_right, Nat.sub_sub] <;>
    congr 2 <;> omega_arith

end VG.Proof.TripleDes.Arm

end

end

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Impl.TripleDes.Arm

theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr) s = some s' ∧
      s'.gpr .r11 = ((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .r5) (s.gpr .r4))).setWidth 28).setWidth 32 ∧
      s'.gpr .r10 = (((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .r5) (s.gpr .r4))) >>> 28).setWidth 28).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) 32 28
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .r5 .r4 .r11 .r10 (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩


theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr) s = some s' ∧
      s'.gpr .r4 = ((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .r11) (s.gpr .r10))).setWidth 32).setWidth 32 ∧
      s'.gpr .r5 = (((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .r11) (s.gpr .r10))) >>> 32).setWidth 16).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) 28 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .r11 .r10 .r4 .r5 (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.Arm.Key

end

end

/-! ### `TripleDes.Arm.KeySteps`, which this module and modules that import it used -/

section

/-! ### `TripleDes.Arm.Word`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.Arm

theorem mask28 (x : BitVec 32) : x &&& 0x0fffffff = (x.setWidth 28).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 28 - 1) = x.toNat % 268435456 % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem rotate28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ((x.setWidth 32).rotateRight (32 - n) ^^^ (x.setWidth 32) >>> (28 - n)) &&& 0x0fffffff =
      (x.rotateLeft n).setWidth 32 := by
  rw [mask28]
  apply congrArg (BitVec.setWidth 32)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n32 : (32 - n) % 32 = 32 - n := Nat.mod_eq_of_lt (by omega_using [hn])
  have n28 : n % 28 = n := Nat.mod_eq_of_lt (by omega_using [hn'])
  rw [n32, n28]
  rw [show 32 - (32 - n) = n by omega_using [hn']]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (28 - n) < 32 by omega_using [hn', h], BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 32 by omega_using [hj],
      show j - n < 32 by omega_using [hj], BitVec.getLsbD_of_ge]


theorem mask_word (x : BitVec 32) (n : Nat) (hn : 0 < n) (hn32 : n ≤ 32) :
    (x <<< (32 - n)) >>> (32 - n) = (x.setWidth n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < n
  · have hi : 32 - n + j < 32 := by omega
    have hlo : ¬32 - n + j < 32 - n := by omega_using []
    simp only [hi, hlo, h, hj, decide_true, decide_false, Bool.not_false,
      Bool.true_and, show 32 - n + j - (32 - n) = j by omega_using []]
  · have ho : ¬32 - n + j < 32 := by omega_using [h]
    simp only [ho, h, hj, decide_true, decide_false, Bool.false_and, Bool.true_and]

theorem packed48 (x : BitVec 48) :
    ((x >>> 32).setWidth 16).setWidth 32 ++ x.setWidth 32 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases hlo : i < 32
  · simp only [hlo, ite_true, decide_true, Bool.true_and]
  · simp (disch := omega) only [hlo, ite_false, decide_true, Bool.true_and,
      show i - 32 < 32 by omega_using [hi], show 32 + (i - 32) = i by omega_using [hlo]]
    by_cases h48 : i < 48
    · simp only [show i - 32 < 16 by omega_using [h48], decide_true, Bool.true_and]
    · simp only [show ¬i - 32 < 16 by omega_using [h48], decide_false, Bool.false_and,
        BitVec.getLsbD_of_ge x i (by omega_using [h48])]

end VG.Proof.TripleDes.Arm

end

end

@[expose] public section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .r4)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (Key.rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r', r' ≠ r → r' ≠ .r4 → s'.gpr r' = s.gpr r') := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega_using [hn, hn']
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega_using [hn']
  refine ⟨_, by
    simp only [Key.rotate28, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, hleft.1, hleft.2, hright.1, hright.2,
      show 1 ≤ (4 : Nat) from by decide, show (4 : Nat) ≤ 31 from by decide, and_self, ite_true, Option.map_some,
      hr, Ne.symm hr, gpr_setReg, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hr, ite_false]
    rw [hx, mask_word _ 28 (by decide) (by decide)]
    exact (mask28 _).symm.trans (rotate28_word x n hn hn')
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r' h1 h2; simp only [gpr_setReg, h1, h2, ite_false]
end VG.Proof.TripleDes.Arm

end

end

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep)

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r10 = (c.rotateLeft n).setWidth 32
  d : s'.gpr .r11 = (d.rotateLeft n).setWidth 32
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r4 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    WP isa (Impl.TripleDes.Arm.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.Arm.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, _, reg₁⟩ := rotate28_ok s .r10 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r11 = d.setWidth 32 := (reg₁ .r11 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, _, reg₂⟩ := rotate28_ok s₁ .r11 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r10 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 32 j >>> 1) == (0 : BitVec 32)) = decide (j < 2) ∧
    ((BitVec.ofNat 32 j - BitVec.ofNat 32 k) == (0 : BitVec 32)) = decide (j = k) := by
  decide

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .r9 = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.mov .r4 (.shifted .r9 .lsr 1), .cmp .r4 (.imm 0)] s = some s' ∧
      isa.eval .eq s' = some (decide (j < 2)) ∧ Keep [.r4] s s' := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some, 
      exec, Op2.eval, Option.map_some, gpr_setReg]
    rfl, ?_, ?_⟩
  · change some (((s.gpr .r9 >>> 1) - 0) == 0) = _
    have hz : (s.gpr .r9 >>> 1) - (0 : BitVec 32) = s.gpr .r9 >>> 1 := by bv_omega
    rw [hz, hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [VG.Proof.Rc2.Arm.gpr_subFlags, gpr_setReg, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r9 = BitVec.ofNat 32 j) :
    ∃ s', runBlock isa [.cmp .r9 (.imm (BitVec.ofNat 32 k))] s = some s' ∧
      isa.eval .eq s' = some (decide (j = k)) ∧ Keep [.r4] s s' := by
  have henc : encodable (BitVec.ofNat 32 k) = true := by
    have hfinite : ∀ k < 16, encodable (BitVec.ofNat 32 k) = true := by decide
    exact hfinite k hk
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      henc, ite_true, Option.map_some]
    rfl, ?_, ?_⟩
  · change some ((s.gpr .r9 - BitVec.ofNat 32 k) == 0) = _
    rw [hv]
    exact congrArg some (comparison_values j hj k hk).2
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r10 = c.setWidth 32) (hd : s.gpr .r11 = d.setWidth 32)
    (hjreg : s.gpr .r9 = BitVec.ofNat 32 j) :
    WP isa Impl.TripleDes.Arm.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.Arm.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Keep [.r4] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 5)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.Arm.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .r10 (by simp)).trans hc)
      ((h.reg .r11 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Keep [.r4] s a) (hb : Keep [.r4] a b) : Keep [.r4] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cond₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r9 (by simp)).trans hjreg)
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cond₃, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r9 (by simp)).trans hjreg)
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.Arm.Key
