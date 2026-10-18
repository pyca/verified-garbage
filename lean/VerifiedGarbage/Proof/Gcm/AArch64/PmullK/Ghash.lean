module

public import VerifiedGarbage.Proof.Gcm.AArch64.PmullK.Groups
meta import VerifiedGarbage.Proof.Gcm.AArch64.PmullK.Groups
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
meta import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Powers8
meta import VerifiedGarbage.Spec.Gcm.Powers8
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
public import Mathlib.Tactic.Ring.RingNF
meta import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.LinearCombination
meta import Mathlib.Tactic.LinearCombination
import all Init.Data.Nat.Bitwise.Basic

/-!
# GHASH with PMULL and EOR3: the whole functions

`ghash_verified`, `ghashW_verified` and `ghashS_verified` prove
`Impl.Gcm.AArch64.PmullK`'s `vg_ghash_aes_sha3`, `vg_ghash_with_powers_aes_sha3`
and `vg_ghash_store_powers_aes_sha3` against the contracts of `vg_ghash`,
`vg_ghash_with_powers` and `vg_ghash_store_powers`. Their prologues are
`vg_ghash_aes`'s (`Pmull/Ghash.lean`), whose invariant `Inv` the keys turn into
this module's `KInv` (`KInv.of_inv`): that of `vg_ghash_aes`'s loops, with the
powers `H'ᵏ` held only with their halves swapped (`sReg k`,
`x · ρ(sReg k) = Hᵏ`) and their keys (`keyV`), which the steps of `k` blocks
(`bodyK_ok`) and of one (`body1K_ok`) keep. The products `Groups.lean`
computes as bits add `x · a · s` (`val_fix_kadd`): `mid` has the two
products `vg_ghash_aes` adds to it, and the other two each twice.
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.PmullK

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly pwOff)
open VG.Impl.Gcm.AArch64.PmullK (P A₂ B₂ P₂ kReg kHi keyOf)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Karatsuba's products -/

/-- `kadd` adds `x · a · s` (`s` as loaded) to the product. -/
theorem val_fix_kadd (p : Prod) (a s : BitVec 128) :
    (fix (kadd p a s (kkey s))).val = (fix p).val + x * ρ a * ρ s := by
  simp only [fix, kadd, kkey, Prod.val, φ_xor, φ_polyMul, ψ_xor, ρ]
  linear_combination (x ^ 65 * (ψ (vdword a 0) * ψ (vdword s 0) + ψ (vdword a 1) * ψ (vdword s 1))) *
    two_Q

/-! ## The invariant and the steps -/

/-- What holds after `i` blocks, with the powers and keys up to `K`. -/
structure KInv (s₀ : State) (K i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  c : s.v C = ofVDwords poly poly
  sw : ∀ k, 1 ≤ k → k ≤ K → x * ρ (s.v (sReg k)) = φ (H₀ s₀) ^ k
  key : ∀ k, 1 ≤ k → k ≤ K → keyV s k = kkey (s.v (sReg k))
  y : ρ (s.v Y) = φ (Ys s₀ i)
  x0 : s.gpr .x0 = hA s₀
  x1 : s.gpr .x1 = yp s₀
  x2 : s.gpr .x2 = blkAddr s₀ i
  x3 : s.gpr .x3 = BitVec.ofNat 64 (nb s₀ - i)
  x5 : s.gpr .x5 = s.gpr .x3 >>> 3
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The invariant does not depend on `x6`. -/
theorem KInv.of_x6 {s₀ : State} {K i : Nat} {s s' : State} (hI : KInv s₀ K i s)
    (hg : ∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KInv s₀ K i s' where
  le := hI.le
  c := by rw [hv, hI.c]
  sw k hk hkK := by rw [hv, hI.sw k hk hkK]
  key k hk hkK := by simp only [keyV, hv]; exact hI.key k hk hkK
  y := by rw [hv, hI.y]
  x0 := by rw [hg .x0 (by decide), hI.x0]
  x1 := by rw [hg .x1 (by decide), hI.x1]
  x2 := by rw [hg .x2 (by decide), hI.x2]
  x3 := by rw [hg .x3 (by decide), hI.x3]
  x5 := by rw [hg .x5 (by decide), hg .x3 (by decide), hI.x5]
  mem := by rw [hm, hI.mem]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

theorem sReg_nmem_key (k : Nat) : sReg k ∉ keyRegs := by unfold sReg; split <;> decide

/-- `Inv` and the keys make `KInv`. -/
theorem KInv.of_inv {s₀ : State} {K i : Nat} {s s' : State} (hI : Inv s₀ K i s)
    (o : VOnly keyRegs s s') (hkey : ∀ k, 1 ≤ k → k ≤ K → keyV s' k = kkey (s'.v (sReg k))) :
    KInv s₀ K i s' where
  le := hI.le
  c := by rw [o.v C (by decide), hI.c]
  sw k hk hkK := by rw [o.v _ (sReg_nmem_key k), hI.sw k hk hkK, ρ_ext8_self, hI.t k hk hkK]
  key := hkey
  y := by rw [o.v Y (by decide), hI.y]
  x0 := by rw [o.gpr, hI.x0]
  x1 := by rw [o.gpr, hI.x1]
  x2 := by rw [o.gpr, hI.x2]
  x3 := by rw [o.gpr, hI.x3]
  x5 := by rw [o.gpr, hI.x5]
  mem := by rw [o.mem, hI.mem]
  rd := by rw [o.rd, hI.rd]
  wr := by rw [o.wr, hI.wr]

/-- The keys of all eight powers. -/
theorem keysK_ok {s₀ : State} {i : Nat} {s : State} (hI : Inv s₀ 8 i s) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.keys) s (KInv s₀ 8 i) :=
  WP.mono (keys_ok s) fun _ ⟨hk, o⟩ =>
    KInv.of_inv hI o (keys_key (fun k a b => hI.sw k a b) hk fun k => o.v _ (sReg_nmem_key k))

/-- The key of `H'`. -/
theorem key1K_ok {s₀ : State} {i : Nat} {s : State} (hI : Inv s₀ 1 i s) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.key1) s (KInv s₀ 1 i) :=
  WP.mono (key1_ok s (hI.sw 1 le_rfl le_rfl)) fun _ ⟨h, o⟩ =>
    KInv.of_inv hI o.weaken fun k hk hk1 => by obtain rfl : k = 1 := (by omega); exact h

/-! ## Pairs of blocks -/

/-- Two blocks' products added to `pv`. -/
theorem val_pair (pv : Prod) (a₁ s₁ a₂ s₂ : BitVec 128) :
    (fix ⟨pv.lo ^^^ polyMul (vdword a₁ 1) (vdword s₁ 1) ^^^ polyMul (vdword a₂ 1) (vdword s₂ 1),
      pv.mid ^^^ polyMul (vdword a₁ 0 ^^^ vdword a₁ 1) (kkey s₁) ^^^
        polyMul (vdword a₂ 0 ^^^ vdword a₂ 1) (kkey s₂),
      pv.hi ^^^ polyMul (vdword a₁ 0) (vdword s₁ 0) ^^^ polyMul (vdword a₂ 0) (vdword s₂ 0)⟩).val =
      (fix pv).val + x * ρ a₁ * ρ s₁ + x * ρ a₂ * ρ s₂ := by
  exact (val_fix_kadd (kadd pv a₁ s₁ (kkey s₁)) a₂ s₂).trans (by rw [val_fix_kadd])

/-- After `j` blocks of `k` from the second on, added to `pv`, and the first,
which `Y` is added to, once `done`: the product is `Y` after `j + 1` blocks
times `Hᵏ⁻¹⁻ʲ`. -/
def BIK (s₀ : State) (k i j : Nat) (done : Bool) (pv : Prod) : Prop :=
  (fix pv).val + (if done then 0 else (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) ^ k) =
    φ (Ys s₀ (i + 1 + j)) * φ (H₀ s₀) ^ (k - 1 - j)

theorem BIK.zero (s₀ : State) {k : Nat} (hk : 1 ≤ k) (i : Nat) : BIK s₀ k i 0 false Prod.zero := by
  have e : φ (H₀ s₀) ^ k = φ (H₀ s₀) ^ (k - 1 - 0) * φ (H₀ s₀) := by
    rw [← pow_succ]; exact congrArg _ (by omega)
  simp only [BIK, fix_zero, Prod.val_zero, zero_add, Bool.false_eq_true, ite_false, Nat.add_zero,
    φ_Ys_succ]
  linear_combination (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * e

/-- The registers the loops write. -/
abbrev loopRegs : List VReg := [A, T, P, A₂, B₂, P₂, HI, LO, MID, Y]

/-- Block `i + j` of the data, as loaded at `x2 + 16 j`. -/
theorem ρ_blockV {s₀ : State} {K i : Nat} {sB s : State} (hI : KInv s₀ K i sB)
    (o : VOnly loopRegs sB s) (j : Nat) :
    ρ (blockV s (16 * j)) = φ (blockAt s₀.mem (blkAddr s₀ (i + j))) := by
  rw [blockV, ρ_load, o.mem, o.gpr, hI.mem, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add]

theorem sReg_nmem_loop (k : Nat) : sReg k ∉ loopRegs := by unfold sReg; split <;> decide
theorem keyOf_nmem_loop (k : Nat) : keyOf k ∉ loopRegs := by unfold keyOf kReg; split <;> decide

/-- The powers and keys, kept by the loops. -/
theorem keep_sw {s₀ : State} {K i : Nat} {sB s : State} (hI : KInv s₀ K i sB)
    (o : VOnly loopRegs sB s) {k : Nat} (hk : 1 ≤ k) (hkK : k ≤ K) :
    x * ρ (s.v (sReg k)) = φ (H₀ s₀) ^ k ∧ keyV s k = kkey (s.v (sReg k)) := by
  have hs : s.v (sReg k) = sB.v (sReg k) := o.v _ (sReg_nmem_loop k)
  refine ⟨by rw [hs, hI.sw k hk hkK], ?_⟩
  rw [hs, ← hI.key k hk hkK]
  simp only [keyV, o.v _ (keyOf_nmem_loop k)]

/-- Pair `m` of a step of `k` blocks, added to `pv`. -/
theorem pair_step {s₀ : State} (hp : Pm s₀) {K k i m : Nat} (hk2 : 2 ≤ k) (hkK : k ≤ K) (hK : K ≤ 8)
    (hke : k % 2 = 0) (hm : m < k / 2) (hi : i + k ≤ nb s₀) {sB : State} (hI : KInv s₀ K i sB)
    {s : State} (o : VOnly loopRegs sB s) (hy : s.v Y = sB.v Y) {pv : Prod}
    (hB : BIK s₀ k i (2 * m) false pv) :
    WP isa (.block (Impl.Gcm.AArch64.PmullK.pairAt k m)) s fun s' => VOnly pairRegs s s' ∧
      BIK s₀ k i (if m + 1 = k / 2 then k - 1 else 2 * m + 2) (decide (m + 1 = k / 2))
        ⟨pv.lo ^^^ s'.v A ^^^ s'.v A₂, pv.mid ^^^ s'.v T ^^^ s'.v B₂, pv.hi ^^^ s'.v P ^^^ s'.v P₂⟩ := by
  have hn := hp.nb_lt
  have hx2 : s.gpr .x2 = blkAddr s₀ i := by rw [o.gpr, hI.x2]
  have hin : ∀ j, i + j < nb s₀ →
      InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj => by
    rw [o.rd, o.wr, hI.rd, hI.wr, hx2]; exact in_blk16 hp hj
  have eH : ∀ a b : Nat, a + 1 = b → φ (H₀ s₀) ^ b = φ (H₀ s₀) ^ a * φ (H₀ s₀) := fun a b h => by
    rw [← h, pow_succ]
  unfold Impl.Gcm.AArch64.PmullK.pairAt
  by_cases hl : m + 1 = k / 2
  · simp only [hl, ite_true, decide_true]
    refine WP.mono (kpair_ok (k - 1) 1 0 k true s (by omega) (by omega) (hin _ (by omega))
      (hin _ (by omega))) fun s' ⟨p₁, a₁, t₁, p₂, a₂, b₂, o'⟩ => ⟨o', ?_⟩
    obtain ⟨w₁, k₁⟩ := keep_sw hI o le_rfl (by omega)
    obtain ⟨w₂, k₂⟩ := keep_sw hI o (by omega) hkK
    rw [p₁, a₁, t₁, p₂, a₂, b₂, k₁, k₂]
    simp only [ite_true] at *
    simp only [BIK, val_pair, ite_true, add_zero]
    have hX : ρ (blockV s (16 * (k - 1))) = φ (blockAt s₀.mem (blkAddr s₀ (i + (k - 1)))) :=
      ρ_blockV hI o _
    have hX₀ : ρ (blockV s (16 * 0) ^^^ s.v Y) =
        φ (blockAt s₀.mem (blkAddr s₀ i)) + φ (Ys s₀ i) := by
      rw [ρ_xor, ρ_blockV hI o, Nat.add_zero, hy, hI.y]
    have hB' := hB
    simp only [BIK, Bool.false_eq_true, ite_false] at hB'
    rw [show 2 * m = k - 2 by omega] at hB'
    rw [hX, hX₀, show k - 1 - (k - 1) = 0 by omega, pow_zero, mul_one]
    have e1 := φ_Ys_succ s₀ (i + (k - 1))
    rw [show i + (k - 1) + 1 = i + 1 + (k - 1) by omega] at e1
    rw [show i + 1 + (k - 2) = i + (k - 1) by omega, show k - 1 - (k - 2) = 1 by omega,
      pow_one] at hB'
    linear_combination hB' - e1 + (φ (blockAt s₀.mem (blkAddr s₀ i)) + φ (Ys s₀ i)) * w₂ +
      φ (blockAt s₀.mem (blkAddr s₀ (i + (k - 1)))) * (w₁.trans (pow_one _))
  · simp only [hl, ite_false, decide_false]
    have hm' : 2 * m + 2 < k := by omega
    refine WP.mono (kpair_ok (2 * m + 1) (k - 2 * m - 1) (2 * m + 2) (k - 2 * m - 2) false s
      (by omega) (by omega) (hin _ (by omega)) (hin _ (by omega)))
      fun s' ⟨p₁, a₁, t₁, p₂, a₂, b₂, o'⟩ => ⟨o', ?_⟩
    obtain ⟨w₁, k₁⟩ := keep_sw hI o (k := k - 2 * m - 1) (by omega) (by omega)
    obtain ⟨w₂, k₂⟩ := keep_sw hI o (k := k - 2 * m - 2) (by omega) (by omega)
    rw [p₁, a₁, t₁, p₂, a₂, b₂, k₁, k₂]
    simp only [Bool.false_eq_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.xor_zero] at *
    simp only [BIK, val_pair, Bool.false_eq_true, ite_false]
    rw [ρ_blockV hI o, ρ_blockV hI o]
    have hB' := hB
    simp only [BIK, Bool.false_eq_true, ite_false] at hB'
    have e1 := φ_Ys_succ s₀ (i + 1 + 2 * m)
    have e2 := φ_Ys_succ s₀ (i + 1 + (2 * m + 1))
    rw [show i + 1 + 2 * m + 1 = i + 1 + (2 * m + 1) by omega] at e1
    rw [show i + 1 + (2 * m + 1) + 1 = i + 1 + (2 * m + 2) by omega] at e2
    rw [show i + (2 * m + 1) = i + 1 + 2 * m by omega, show i + (2 * m + 2) = i + 1 + (2 * m + 1) by omega]
    have h1 := eH (k - 1 - (2 * m + 2)) (k - 2 * m - 2) (by omega)
    have h2 := eH (k - 2 * m - 2) (k - 1 - 2 * m) (by omega)
    have hq : φ (H₀ s₀) ^ (k - 2 * m - 1) = φ (H₀ s₀) ^ (k - 1 - 2 * m) := by
      rw [show k - 2 * m - 1 = k - 1 - 2 * m by omega]
    linear_combination hB' + φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + 2 * m))) * (w₁.trans hq) +
      φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + (2 * m + 1)))) * w₂ +
      (φ (Ys s₀ (i + 1 + 2 * m)) + φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + 2 * m)))) * h2 -
      φ (H₀ s₀) ^ (k - 2 * m - 2) * e1 +
      (φ (Ys s₀ (i + 1 + (2 * m + 1))) + φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + (2 * m + 1))))) * h1 -
      φ (H₀ s₀) ^ (k - 1 - (2 * m + 2)) * e2

/-! ## The steps -/

/-- The registers the pairs and their sums write. -/
abbrev pairsRegs : List VReg := [A, T, P, A₂, B₂, P₂, HI, LO, MID]

/-- `KInv` after the reduction into `Y` and `advance k`, from `KInv` before the
step's pairs. -/
theorem KInv.step {s₀ : State} (hp : Pm s₀) {K k i : Nat} (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    (hi : i + k ≤ nb s₀) {s s₃ : State} (hI : KInv s₀ K i s) (o₃ : VOnly pairsRegs s s₃)
    (hv : (fix (prod s₃)).val = φ (Ys s₀ (i + k))) :
    WP isa (.block (Impl.Gcm.AArch64.PmullK.reduceK ++ Impl.Gcm.AArch64.Pmull.advance k)) s₃
      (KInv s₀ K (i + k)) := by
  have hn := hp.nb_lt
  rw [WP.block_append_iff]
  refine WP.mono (reduceK_ok s₃ (by rw [o₃.v C (by decide), hI.c])) fun s₄ ⟨r₄, o₄⟩ => ?_
  refine WP.mono (advance_ok k (by omega) s₄) fun s' ⟨f2, f3, f5, fg, fv, fm, frd, fwr⟩ => ?_
  have O : VOnly loopRegs s s₄ := (o₃.trans o₄).weaken
  have kv : ∀ r, r ∉ loopRegs → s'.v r = s.v r := fun r h => by rw [fv, O.v r h]
  have kg : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r := fun r h2 h3 h5 => by
    rw [fg r h2 h3 h5, O.gpr]
  refine ⟨by omega, by rw [kv C (by decide), hI.c],
    fun m hm hmK => by rw [kv _ (sReg_nmem_loop _), hI.sw m hm hmK],
    fun m hm hmK => by
      simp only [keyV, kv _ (keyOf_nmem_loop _), kv _ (sReg_nmem_loop _)]; exact hI.key m hm hmK,
    ?_, by rw [kg .x0 (by decide) (by decide) (by decide), hI.x0],
    by rw [kg .x1 (by decide) (by decide) (by decide), hI.x1], ?_, ?_, f5,
    by rw [fm, O.mem, hI.mem], by rw [frd, O.rd, hI.rd], by rw [fwr, O.wr, hI.wr]⟩
  · rw [fv, r₄, ρ_reduce, hv]
  · rw [f2, O.gpr, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add]
  · rw [f3, O.gpr, hI.x3, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

/-- The pairs from the second on, of a step of `k` blocks. -/
def PIK (s₀ sB : State) (k i n : Nat) (s : State) : Prop :=
  VOnly pairsRegs sB s ∧
    BIK s₀ k i (if n + 1 = k / 2 then k - 1 else 2 * n + 2) (decide (n + 1 = k / 2)) (prod s)

theorem bodyK_ok {s₀ : State} (hp : Pm s₀) {K k i : Nat} (hk2 : 2 ≤ k) (hke : k % 2 = 0)
    (hkK : k ≤ K) (hK : K ≤ 8) (hi : i + k ≤ nb s₀) {s : State} (hI : KInv s₀ K i s) :
    WP isa (.block (Impl.Gcm.AArch64.PmullK.bodyK k)) s (KInv s₀ K (i + k)) := by
  simp only [Impl.Gcm.AArch64.PmullK.bodyK, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pair_step hp hk2 hkK hK hke (m := 0) (by omega) hi hI (VOnly.refl _ _) rfl
    (BIK.zero s₀ (by omega) i)) fun s₁ ⟨o₁, b₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addFirst_ok s₁) fun s₂ ⟨p₂, o₂⟩ => ?_
  have h₂ : PIK s₀ s k i 0 s₂ := by
    refine ⟨(o₁.trans o₂).weaken, ?_⟩
    rw [p₂]
    simpa only [Prod.zero, BitVec.ofNat_eq_ofNat, BitVec.zero_xor] using b₁
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := k / 2 - 1) (PIK s₀ s k i)
    (fun m s' hm ⟨o', b'⟩ => ?_) (k / 2 - 1) le_rfl s₂ h₂) fun s₃ ⟨o₃, b₃⟩ => ?_
  · have hnd : ¬ m + 1 = k / 2 := by omega
    simp only [hnd, ite_false, decide_false] at b'
    rw [WP.block_append_iff]
    refine WP.mono (pair_step hp hk2 hkK hK hke (m := m + 1) (pv := prod s') (by omega) hi hI
      o'.weaken (o'.v Y (by decide)) (by rw [show 2 * (m + 1) = 2 * m + 2 by omega]; exact b'))
      fun s₄ ⟨o₄, b₄⟩ => ?_
    refine WP.mono (addNext_ok s₄) fun s₅ ⟨p₅, o₅⟩ => ⟨(o'.trans (o₄.trans o₅)).weaken, ?_⟩
    rw [p₅, o₄.v LO (by decide), o₄.v MID (by decide), o₄.v HI (by decide)]
    exact b₄
  · have hd : k / 2 - 1 + 1 = k / 2 := by omega
    simp only [hd, ite_true, decide_true] at b₃
    refine KInv.step hp (by omega) (by omega) hi hI o₃ ?_
    have := b₃
    simp only [BIK, ite_true, add_zero, show k - 1 - (k - 1) = 0 by omega, pow_zero, mul_one,
      show i + 1 + (k - 1) = i + k by omega] at this
    exact this

theorem body1K_ok {s₀ : State} (hp : Pm s₀) {K i : Nat} (hK1 : 1 ≤ K)
    (hi : i + 1 ≤ nb s₀) {s : State} (hI : KInv s₀ K i s) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.body1K) s (KInv s₀ K (i + 1)) := by
  simp only [Impl.Gcm.AArch64.PmullK.body1K, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x2 0 s rfl (by decide)
    (by rw [hI.rd, hI.wr, show (0 : Nat) = 16 * 0 from rfl, hI.x2]; exact in_blk16 hp (by omega)))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₁) fun s₂ ⟨e₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (single_ok s₂) fun s₃ ⟨p₃, o₃⟩ => ?_
  have O₂ : VOnly loopRegs s s₂ := (o₁.trans o₂).weaken
  refine KInv.step hp le_rfl (by decide) hi hI ((o₁.trans (o₂.trans o₃)).weaken) ?_
  obtain ⟨w, k⟩ := keep_sw hI O₂ le_rfl hK1
  have hA : ρ (s₂.v A) = φ (blockAt s₀.mem (blkAddr s₀ i)) + φ (Ys s₀ i) := by
    rw [e₂, ρ_xor, l₁, o₁.v Y (by decide), hI.y]
    have := ρ_blockV hI (VOnly.refl loopRegs s) 0
    rw [Nat.add_zero] at this
    exact congrArg (· + φ (Ys s₀ i)) this
  rw [p₃, k, val_fix_kadd, fix_zero, Prod.val_zero, zero_add, hA, φ_Ys_succ]
  linear_combination (φ (blockAt s₀.mem (blkAddr s₀ i)) + φ (Ys s₀ i)) * (w.trans (pow_one _))

/-! ## The loops -/

/-- The remaining blocks, one at a time. -/
theorem onesK_ok {s₀ : State} (hp : Pm s₀) {K i : Nat} (hK1 : 1 ≤ K) {s : State}
    (hI : KInv s₀ K i s) :
    WP isa (.loop (.block Impl.Gcm.AArch64.PmullK.body1K) (.nonzero .x .x3)) s
      (KInv s₀ K (nb s₀)) ∨ i = nb s₀ := by
  have hn := hp.nb_lt
  by_cases hlt : i < nb s₀
  · left
    let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ KInv s₀ K i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block Impl.Gcm.AArch64.PmullK.body1K) s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ KInv s₀ K (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body1K_ok hp hK1 (by omega) hI) fun s' hI' => ?_
      have hev : eval (.nonzero .x .x3) s' = some (decide (nb s₀ - (i + 1) ≠ 0)) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x3,
          ofNat_bne (show nb s₀ - (i + 1) < 2 ^ 64 by omega)]
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by rw [hev, decide_eq_false (not_not.mpr hlast)], this ▸ hI'⟩
      · exact .inr ⟨by rw [hev, decide_eq_true hlast], nb s₀ - (i + 1), by omega, i + 1, rfl,
          by omega, hI'⟩
    exact WP.loop (M := isa) Inv1 hstep (nb s₀ - i) s ⟨i, rfl, hlt, hI⟩
  · right; have := hI.le; omega

/-- `k` blocks if bit `sh` of the remaining count (less than `2 ^ (sh + 1)`) is
set, with `k = 2 ^ sh`. -/
theorem bitK_ok {s₀ : State} (hp : Pm s₀) {i : Nat} (sh k : Nat) (hk : k = 2 ^ sh) (hk2 : 2 ≤ k)
    (hke : k % 2 = 0) (hk8 : k ≤ 8) (hsh : sh < 64) (hi : nb s₀ - i < 2 * k) {s : State}
    (hI : KInv s₀ 8 i s) :
    WP isa (.seq (.block [.lsr .x .x6 .x3 sh])
      (.ite (.zero .x .x6) (.block []) (.block (Impl.Gcm.AArch64.PmullK.bodyK k)))) s
      (fun s' => ∃ i', nb s₀ - i' < k ∧ KInv s₀ 8 i' s') := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (lsr_ok .x6 .x3 sh hsh s) fun s₁ ⟨f6, fg, fv, fm, frd, fwr⟩ => ?_)
  have hI₁ := hI.of_x6 fg fv fm frd fwr
  have hev : eval (.zero .x .x6) s₁ = some (decide (nb s₀ - i < k)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, f6, hI.x3,
      shr_beq sh (show nb s₀ - i < 2 ^ 64 by omega), hk]
  refine WP.ite _ hev (fun h => WP.block_nil ⟨i, by simpa using h, hI₁⟩) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  exact WP.mono (bodyK_ok hp hk2 hke hk8 le_rfl (by have := hI.le; omega) hI₁) fun s' h' =>
    ⟨i + k, by omega, h'⟩

/-- The last `n mod 8` blocks, once the powers and keys are set up. -/
theorem tailK_ok {s₀ : State} (hp : Pm s₀) {i : Nat} (hi : nb s₀ - i < 8) {s : State}
    (hI : KInv s₀ 8 i s) :
    WP isa Impl.Gcm.AArch64.PmullK.tailK s (KInv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  unfold Impl.Gcm.AArch64.PmullK.tailK
  refine WP.seq_assoc (WP.mono (bitK_ok hp 2 4 rfl (by decide) (by decide) (by decide) (by decide)
    (by omega) hI) fun s₁ ⟨i₁, hi₁, hI₁⟩ => ?_)
  refine WP.seq_assoc (WP.mono (bitK_ok hp 1 2 rfl (by decide) (by decide) (by decide) (by decide)
    (by omega) hI₁) fun s₂ ⟨i₂, hi₂, hI₂⟩ => ?_)
  have hev : eval (.zero .x .x3) s₂ = some (decide (nb s₀ - i₂ = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₂.x3,
      ofNat_beq (show nb s₀ - i₂ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i₂ = nb s₀ := by have := hI₂.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · simp only [decide_eq_false_iff_not] at h
    have : i₂ + 1 = nb s₀ := by have := hI₂.le; omega
    exact this ▸ body1K_ok hp (by decide) (by omega) hI₂

/-- The loop of eight blocks, then the tail, from all eight powers and keys. -/
theorem eightsK_ok {s₀ : State} (hp : Pm s₀) (h8 : 8 ≤ nb s₀) {s₁ : State} (hI₁ : KInv s₀ 8 0 s₁) :
    WP isa (.seq (.loop (.block (Impl.Gcm.AArch64.PmullK.bodyK 8)) (.nonzero .x .x5))
      Impl.Gcm.AArch64.PmullK.tailK) s₁ (KInv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ KInv s₀ 8 i s) ?_
    fun s₄ ⟨i, hi, hI₄⟩ => tailK_ok hp hi hI₄)
  let Inv8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ KInv s₀ 8 i s
  have hstep : ∀ m s, Inv8 m s → WP isa (.block (Impl.Gcm.AArch64.PmullK.bodyK 8)) s (fun s' =>
      (eval (.nonzero .x .x5) s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ KInv s₀ 8 i s') ∨
      (eval (.nonzero .x .x5) s' = some true ∧ ∃ m' < m, Inv8 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (bodyK_ok hp (by decide) (by decide) le_rfl le_rfl hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x5) s' = some (decide (8 ≤ nb s₀ - (i + 8))) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x5, hI'.x3,
        shr3_bne (show nb s₀ - (i + 8) < 2 ^ 64 by omega)]
    by_cases h8 : 8 ≤ nb s₀ - (i + 8)
    · exact .inr ⟨by rw [hev, decide_eq_true h8], nb s₀ - (i + 8), by omega, i + 8, rfl,
        by omega, hI'⟩
    · exact .inl ⟨by rw [hev, decide_eq_false h8], i + 8, by omega, hI'⟩
  exact WP.loop (M := isa) Inv8 hstep (nb s₀) s₁ ⟨0, rfl, by omega, hI₁⟩

/-- The block of fewer than eight, one at a time. -/
theorem fewK_ok {s₀ : State} (hp : Pm s₀) {K : Nat} (hK1 : 1 ≤ K) {s₁ : State}
    (hI₁ : KInv s₀ K 0 s₁) :
    WP isa (.ite (.zero .x .x3) (.block [])
      (.loop (.block Impl.Gcm.AArch64.PmullK.body1K) (.nonzero .x .x3))) s₁ (KInv s₀ K (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x3) s₁ = some (decide (nb s₀ = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x3, Nat.sub_zero,
      ofNat_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (h ▸ hI₁)
  · simp only [decide_eq_false_iff_not] at h
    rcases onesK_ok hp hK1 hI₁ with h' | h'
    · exact h'
    · exact absurd h'.symm h

/-- The loops of `ghashAllK`, from all eight powers and keys. -/
theorem loopsPartK_ok {s₀ : State} (hp : Pm s₀) {s₁ : State} (hI₁ : KInv s₀ 8 0 s₁) :
    WP isa (.ite (.zero .x .x5)
        (.ite (.zero .x .x3) (.block []) (.loop (.block Impl.Gcm.AArch64.PmullK.body1K) (.nonzero .x .x3)))
        (.seq (.loop (.block (Impl.Gcm.AArch64.PmullK.bodyK 8)) (.nonzero .x .x5))
          Impl.Gcm.AArch64.PmullK.tailK)) s₁ (KInv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun _ => fewK_ok hp (by decide) hI₁) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  exact eightsK_ok hp h hI₁

theorem epilogueK_ok {s₀ : State} (hp : Pm s₀) {K : Nat} {s : State} (hI : KInv s₀ K (nb s₀) s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.epilogue) s fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 16 := by
    rw [hI.wr, hI.x1]
    exact ⟨yR s₀, hp.y_in, contains_offset (by decide) (by decide)⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (s := s.setV Y _) (by decide) (by decide) hout,
    WP.block_nil ?_⟩
  show blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x1 + BitVec.ofNat 64 0) 16
    ((s.setV Y _).v Y)) (yp s₀) = Ys s₀ (nb s₀)
  apply φ_inj
  simp only [mem_setV, gpr_setV, v_setV, ↓reduceIte, hI.x1, add_ofNat_zero, φ_store, hI.y]

/-! ## `vg_ghash_aes_sha3` -/

/-- `Inv` is `KInv` without powers. -/
theorem KInv.of_inv0 {s₀ : State} {K i : Nat} {s : State} (hI : Inv s₀ K i s) : KInv s₀ 0 i s :=
  ⟨hI.le, hI.c, fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega), hI.y, hI.x0,
    hI.x1, hI.x2, hI.x3, hI.x5, hI.mem, hI.rd, hI.wr⟩

theorem loops_ok {s₀ : State} (hp : Pm s₀) :
    WP isa Impl.Gcm.AArch64.PmullK.ghash s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ K, KInv s₀ K (nb s₀) s) ?_
    fun s₂ ⟨K, hI₂⟩ => epilogueK_ok hp hI₂)
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun _ => ?_) (fun h => ?_)
  · have hev3 : eval (.zero .x .x3) s₁ = some (decide (nb s₀ = 0)) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x3, Nat.sub_zero,
        ofNat_beq (show nb s₀ < 2 ^ 64 by omega)]
    refine WP.ite _ hev3 (fun h0 => ?_) (fun h0 => ?_)
    · simp only [decide_eq_true_eq] at h0
      exact WP.block_nil ⟨0, by rw [h0]; exact KInv.of_inv0 hI₁⟩
    · simp only [decide_eq_false_iff_not] at h0
      refine WP.seq (WP.mono (key1K_ok hI₁) fun s₂ hI₂ => ?_)
      rcases onesK_ok hp le_rfl hI₂ with h' | h'
      · exact WP.mono h' fun s h => ⟨1, h⟩
      · exact absurd h'.symm h0
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at h
    refine WP.seq ?_
    rw [WP.block_append_iff]
    exact WP.mono (powers_ok hI₁) fun s₂ hI₂ => WP.mono (keysK_ok hI₂) fun s₃ hI₃ =>
      WP.mono (eightsK_ok hp h hI₃) fun s h => ⟨8, h⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.AArch64.PmullK.ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loops_ok (Pre.pm hp)) (by decide +kernel) (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.PmullK.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub
    Impl.Gcm.AArch64.PmullK.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ghash_verified :
    Verified AArch64.target Impl.Gcm.AArch64.PmullK.ghash (Spec.Gcm.ghashContract AArch64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashAArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Gcm.AArch64.satState] using Proof.Gcm.AArch64.satState)

/-! ## `vg_ghash_with_powers_aes_sha3` -/

/-- `ghashAllK pro []`, from a prologue that sets up all eight powers and keys. -/
theorem loopsAllK_ok {s₀ : State} (hp : Pm s₀) {pro : List Instr}
    (hpro : WP isa (.block pro) s₀ (KInv s₀ 8 0)) :
    WP isa (Impl.Gcm.AArch64.PmullK.ghashAllK pro []) s₀ fun s' =>
      Proof.Gcm.ghashAArch64.post s₀ s' := by
  refine WP.seq (WP.mono hpro fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (loopsPartK_ok hp hI₁) fun s₂ hI₂ => ?_)
  rw [List.append_nil]
  exact epilogueK_ok hp hI₂

theorem correctW {s₀ : State} (hs : Proof.Gcm.ghashWithAArch64.pre s₀) :
    WP isa Impl.Gcm.AArch64.PmullK.ghashW s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hpro : WP isa (.block (Impl.Gcm.AArch64.Pmull.prologueW ++ Impl.Gcm.AArch64.PmullK.keys)) s₀
      (KInv s₀ 8 0) := by
    rw [WP.block_append_iff]
    exact WP.mono (prologueW_ok hs) fun _ h => keysK_ok h
  exact WP.mono (WP.gprs (rs := preserved) (loopsAllK_ok (pm_of_with hs) hpro)
    (by decide +kernel) (by decide +kernel)) fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghashW_correct (s : State) (hs : Proof.Gcm.ghashWithAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.PmullK.ghashW s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashWithAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correctW hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashW_ct : ConstantTime isa Proof.Gcm.ghashWithAArch64.pre Proof.Gcm.ghashWithAArch64.pub
    Impl.Gcm.AArch64.PmullK.ghashW := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3, h4, h5, hsp⟩, h6⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem ghashW_verified :
    Verified AArch64.target Impl.Gcm.AArch64.PmullK.ghashW (Spec.Gcm.ghashWithPowersContract AArch64.abi) :=
  Verified.of_correct ghashW_correct ghashW_ct
    { pre := by
        sig_implies_pre [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateW, by
        sig_pre [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig, Spec.Gcm.ghashSig,
          Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs, satStateW,
          Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | (rw [blockAt_zero]; exact powers8Repr_zero _)
          | exact Region.disjoint_of_sep (by decide)⟩ }

/-! ## `vg_ghash_store_powers_aes_sha3` -/

/-- With the eight powers set up, `H'ᵏ` (`sReg k` with its halves swapped) is
the prepared power of `Hᵏ`. -/
theorem sReg_pp {s₀ s : State} {i : Nat} (hI : KInv s₀ 8 i s) {k : Nat} (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    ext8 (s.v (sReg k)) (s.v (sReg k)) = pp (H₀ s₀) k :=
  φ_inj (x_cancel (by rw [φ_ext8_self, hI.sw k hk1 hk8, x_φ_pp]))

/-- The powers below `K` stored at `pw`, the block at `y` kept. -/
structure SWK (s₀ : State) (yv : BitVec 128) (K : Nat) (s : State) : Prop where
  x8 : s.gpr .x8 = s₀.gpr .x5
  wr : s.wr = s₀.wr
  t : ∀ k, 1 ≤ k → k ≤ 8 → ext8 (s.v (sReg k)) (s.v (sReg k)) = pp (H₀ s₀) k
  pw : ∀ k, 1 ≤ k → k ≤ K → s.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 = pp (H₀ s₀) k
  y : s.mem.read (yp s₀) 16 = yv

theorem sReg_ne_P' (k : Nat) : sReg k ∉ [Impl.Gcm.AArch64.PmullK.P] := by
  simp only [List.mem_singleton]; exact sReg_ne_P k

/-- `H'ᴷ⁺¹` stored. -/
theorem storeIK_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) {yv : BitVec 128} {K : Nat}
    (hK : K + 1 ≤ 8) {s : State} (hS : SWK s₀ yv K s) :
    WP isa (.block (Impl.Gcm.AArch64.PmullK.storePwK (K + 1))) s (SWK s₀ yv (K + 1)) := by
  obtain ⟨-, hwr, -, -, -, -, -, hyp, -, -, -⟩ := h
  have hc : ∀ k, k ≤ 8 → Region.Contains ⟨s₀.gpr .x5, 128⟩ (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 :=
    fun k hk => contains_offset (by have := pwOff_le k (by omega); omega)
      (by have := pwOff_le k (by omega); omega)
  rw [Impl.Gcm.AArch64.PmullK.storePwK, show ∀ (a b : Instr), [a, b] = [a] ++ [b] from fun _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (swap_ok Impl.Gcm.AArch64.PmullK.P (sReg (K + 1)) s) fun s₁ ⟨w₁, o₁⟩ => ?_
  have hout : InRegions s₁.wr (s₁.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 := by
    rw [o₁.wr, o₁.gpr, hS.wr, hwr, hS.x8]; exact ⟨⟨s₀.gpr .x5, 128⟩, by simp, hc (K + 1) hK⟩
  have ho' : pwOff (K + 1) < 4096 * 16 := by have := pwOff_le (K + 1) (by omega); omega
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (pwOff_mod (K + 1)) ho' hout, WP.block_nil ?_⟩
  refine ⟨by rw [o₁.gpr, hS.x8], by rw [o₁.wr, hS.wr],
    fun k hk1 hk8 => by rw [o₁.v _ (sReg_ne_P' k)]; exact hS.t k hk1 hk8, fun k hk hkK => ?_, ?_⟩
  · show (s₁.mem.write (s₁.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s₁.v Impl.Gcm.AArch64.PmullK.P)).read _ 16 = _
    rw [o₁.gpr, hS.x8, o₁.mem]
    rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [read_write16, w₁, hS.t _ hk hK]
    · rw [Mem.read_write_sep (Offset.sep _ (pwOff_sep k (by omega) (K + 1) (by omega) hk (by omega)
          (by omega)) (by have := pwOff_le k (by omega); omega)
          (by have := pwOff_le (K + 1) (by omega); omega)) (by decide),
        hS.pw k hk hkK']
  · show (s₁.mem.write (s₁.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s₁.v Impl.Gcm.AArch64.PmullK.P)).read _ 16 = _
    have hcy : Region.Contains ⟨s₀.gpr .x1, 16⟩ (s₀.gpr .x1) 16 := by
      have := contains_offset (base := s₀.gpr .x1) (len := 16) (off := 0) (n := 16) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    rw [o₁.gpr, hS.x8, o₁.mem, Mem.read_write_sep (Region.Disjoint.sep hyp hcy (hc (K + 1) hK))
      (by decide), hS.y]

/-- The epilogue, then the eight powers stored. -/
theorem epiSK_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) {s : State}
    (hI : KInv s₀ 8 (nb s₀) s) (h8 : s.gpr .x8 = s₀.gpr .x5) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.epilogue ++ Impl.Gcm.AArch64.PmullK.storesSK)) s fun s' =>
      Proof.Gcm.ghashAArch64.post s₀ s' ∧ Spec.Gcm.Powers8Repr s'.mem (s₀.gpr .x5) (H₀ s₀) := by
  have hp := pm_of_store h
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 16 := by
    rw [hI.wr, hI.x1]
    exact ⟨yR s₀, hp.y_in, contains_offset (by decide) (by decide)⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (s := s.setV Y _) (by decide) (by decide) hout, ?_⟩
  -- After the epilogue: `Y` at `y`.
  let se : State := { s.setV Y (VRevOp.eval .rev64b (s.v Y)) with
    mem := (s.setV Y (VRevOp.eval .rev64b (s.v Y))).mem.write
      ((s.setV Y (VRevOp.eval .rev64b (s.v Y))).gpr .x1 + BitVec.ofNat 64 0) 16
      ((s.setV Y (VRevOp.eval .rev64b (s.v Y))).v Y) }
  have hye : blockAt se.mem (yp s₀) = Ys s₀ (nb s₀) := by
    apply φ_inj
    simp only [se, mem_setV, gpr_setV, v_setV, ↓reduceIte, hI.x1, add_ofNat_zero, φ_store, hI.y]
  have hS0 : SWK s₀ (se.mem.read (yp s₀) 16) 0 se :=
    ⟨by simp only [se, gpr_setV, h8], by simp only [se, wr_setV, hI.wr],
      fun k hk1 hk8 => by
        simp only [se, v_setV, (ne_sReg (r := Y) k).symm, ite_false]; exact sReg_pp hI hk1 hk8,
      fun _ _ h => absurd h (by omega), rfl⟩
  show WP isa (.block Impl.Gcm.AArch64.PmullK.storesSK) se _
  simp only [Impl.Gcm.AArch64.PmullK.storesSK, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 0) (by decide) hS0) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 1) (by decide) h₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 2) (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 3) (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 4) (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 5) (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeIK_ok h (K := 6) (by decide) h₆) fun s₇ h₇ => ?_
  refine WP.mono (storeIK_ok h (K := 7) (by decide) h₇) fun s' h' => ⟨?_, ?_⟩
  · show blockAt s'.mem (yp s₀) = Ys s₀ (nb s₀)
    rw [← hye]
    apply φ_inj
    rw [← ρ_load, ← ρ_load, h'.y]
  · intro j hj
    have e : ∀ k, 1 ≤ k → k ≤ 8 → s'.mem.readW (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 128 =
        pp (H₀ s₀) k := fun k hk1 hk8 => by rw [Mem.readW, ← h'.pw k hk1 hk8]; rfl
    refine ⟨?_, ?_⟩
    · have := e (2 * j + 2) (by omega) (by omega)
      rw [show pwOff (2 * j + 2) = 32 * j by
        simp only [pwOff, show (2 * j + 2) % 2 = 0 by omega, ↓reduceIte]; omega] at this
      exact this
    · have := e (2 * j + 1) (by omega) (by omega)
      rw [show pwOff (2 * j + 1) = 16 + 32 * j by
        simp only [pwOff, show (2 * j + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]; omega] at this
      exact this

theorem correctS {s₀ : State} (hs : Proof.Gcm.ghashStoreAArch64.pre s₀) :
    WP isa Impl.Gcm.AArch64.PmullK.ghashS s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashStoreAArch64.post s₀ s' := by
  have hp := pm_of_store hs
  have hw : WP isa Impl.Gcm.AArch64.PmullK.ghashS s₀ (Proof.Gcm.ghashStoreAArch64.post s₀) := by
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (prologueS_ok hs) fun s₁ ⟨hI₁, h8₁⟩ => ?_
    refine WP.mono (WP.gprs (rs := [.x8]) (keysK_ok hI₁) (by decide +kernel) (by decide +kernel))
      fun s₂ ⟨hI₂, g₂⟩ => ?_
    refine WP.seq (WP.mono (WP.gprs (rs := [.x8]) (loopsPartK_ok hp hI₂) (by decide +kernel)
      (by decide +kernel)) fun s₃ ⟨hI₃, g₃⟩ => ?_)
    exact epiSK_ok hs hI₃ (by rw [g₃ .x8 (by simp), g₂ .x8 (by simp), h8₁])
  exact WP.mono (WP.gprs (rs := preserved) hw (by decide +kernel) (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghashS_correct (s : State) (hs : Proof.Gcm.ghashStoreAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.PmullK.ghashS s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashStoreAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correctS hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashS_ct : ConstantTime isa Proof.Gcm.ghashStoreAArch64.pre Proof.Gcm.ghashStoreAArch64.pub
    Impl.Gcm.AArch64.PmullK.ghashS := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3, h4, h5, hsp⟩, h6⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem ghashS_verified :
    Verified AArch64.target Impl.Gcm.AArch64.PmullK.ghashS (Spec.Gcm.ghashStorePowersContract AArch64.abi) :=
  Verified.of_correct ghashS_correct ghashS_ct
    { pre := by
        sig_implies_pre [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateS, by
        sig_pre [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig, Spec.Gcm.ghashSig,
          Spec.Gcm.storePowersParam, AArch64.abi, AArch64.argRegs, satStateS,
          Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

end VG.Proof.Gcm.AArch64.PmullK
