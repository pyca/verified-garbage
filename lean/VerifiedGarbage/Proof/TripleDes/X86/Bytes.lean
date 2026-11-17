module

import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.TripleDes.X86.Sbox
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `TripleDes.X86.Permutation`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.Bitslice VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86 VG.Proof.TripleDes.X86.Linear

def permutationCfg : Cfg := { base := .ebp, slots := 0, ext := .ebp, exts := 0 }
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

theorem initialPermutation_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs initialPermutation.lit)
      (linEnv (permutationInputs .esi .edi)) (linPost 6 (permutationOutputs Spec.TripleDes.ip 64 32 32 .eax .ebx)) = true := by
  decide +kernel

theorem finalPermutation_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs finalPermutation.lit)
      (linEnv (permutationInputs .edi .esi)) (linPost 6 (permutationOutputs Spec.TripleDes.fp 64 32 32 .eax .ebx)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs keyPermutation1.lit)
      (linEnv (permutationInputs .esi .edi)) (linPost 6 (permutationOutputs Spec.TripleDes.pc1 64 32 28 .eax .ebx)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    check (lanes 32 6) permutationCfg (linExt 2) (instrs keyPermutation2.lit)
      (linEnv (permutationInputs .edi .esi)) (linPost 6 (permutationOutputs Spec.TripleDes.pc2 56 28 32 .eax .ebx)) = true := by
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
  · change (s.gpr .ebp).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .ebp).isLt
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
    (hsp : (is.all fun op => op.dst != some .esp) = true) (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dstLo = ((Spec.TripleDes.permute positions
        (packedInput n split (s.gpr srcLo) (s.gpr srcHi))).setWidth dstSplit).setWidth 32 ∧
      s'.gpr dstHi = ((Spec.TripleDes.permute positions
        (packedInput n split (s.gpr srcLo) (s.gpr srcHi)) >>> dstSplit).setWidth (m - dstSplit)).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => op.dst != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr srcLo else s.gpr srcHi
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ :=
    linear_ok hchk (permutationCfg_ok s) W (fun r i h => by
      simp only [permutationInputs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [permutationCfg] at hj)
  refine ⟨s', hs', ?_, ?_, rd, wr, ?_, ?_, keep⟩
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
  · exact keep .esp hsp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.X86

end

end

@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) = bswap (m.readW p 32) ++ bswap (m.readW (p + 4) 32) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, bswap_readW, bswap_readW]
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

theorem bswapPair (l r : BitVec 32) : bswap r ++ bswap l = byteRev64 (l ++ r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega_arith
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega_arith) only [bswap, byteRev64, BitVec.getLsbD_append,
      BitVec.getLsbD_extractLsb', ite_eq_left, ite_eq_right, Nat.sub_sub] <;>
    congr 2 <;> omega_arith

end VG.Proof.TripleDes.X86
