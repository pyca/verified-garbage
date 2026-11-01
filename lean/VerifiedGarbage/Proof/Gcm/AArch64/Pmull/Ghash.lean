module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Arith
public import VerifiedGarbage.Proof.Gcm.Powers8Contract
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.PrepKey
import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Arith
meta import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.PrepKey
meta import VerifiedGarbage.Proof.Gcm.Powers
meta import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Contract


@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

section

/-!
# GHASH with PMULL: the instruction groups in `Q`

What a load and a store of a block are in `Q`, and what `mul` computes
(`Groups.lean`, as bits): `x · a · t`, so that `mul` by `vg_ghash_aes`'s key
multiplies by the hash subkey (`mulV_keyV`).
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)

/-- A block, loaded and `rev64`ed. -/
theorem ρ_load (m : Mem) (p : Addr) :
    ρ (VRevOp.eval .rev64b (m.read p 16)) = φ (Spec.Gcm.blockAt m p) := by
  rw [ρ, vdword_rev64b _ (by decide), vdword_rev64b _ (by decide), vdword_read16 m p (by decide),
    vdword_read16 m p (by decide), ← blockAt_rev, φ_append]

/-- A block as loaded, `rev64`ed and stored. -/
theorem φ_store (m : Mem) (p : Addr) (v : BitVec 128) :
    φ (Spec.Gcm.blockAt (m.write p 16 (VRevOp.eval .rev64b v)) p) = ρ v := by
  rw [← ρ_load, read_write16, rev64b_rev64b]

/-- `d ← mul(a, t)` with its halves swapped, a block of class `x · a · t` (`a` as loaded). -/
theorem mul_ok (d a sk t : VReg) (s : State) (ha : Free a) (hs : Free sk) (ht : Free t)
    (hst : s.v sk = ext8 (s.v t) (s.v t)) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.mul d a sk t)) s fun s' =>
      ρ (s'.v d) = x * ρ (s.v a) * φ (s.v t) ∧ VOnly [LO, MID, HI, T, d] s s' :=
  WP.mono (mulV_ok d a sk t s ha hs ht hst hc) fun _ ⟨h, o⟩ =>
    ⟨by rw [h, mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add], o⟩

/-- A 16-byte load at `[n, #off]`, and `rev64`. -/
theorem ldrev_ok (d : VReg) (n : Reg) (off : Nat) (s : State) (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadRev d n off)) s fun s' =>
      ρ (s'.v d) = φ (Spec.Gcm.blockAt s.mem (s.gpr n + BitVec.ofNat 64 off)) ∧ VOnly [d] s s' :=
  WP.mono (loadRev_ok d n off s ho ho' hin) fun _ ⟨h, o⟩ => ⟨by rw [h, ρ_load], o⟩

/-- `ρ` determines a value. -/
theorem ρ_inj {a b : BitVec 128} (h : ρ a = ρ b) : a = b := by
  rw [← φ_ext8_self, ← φ_ext8_self] at h
  rw [← ext8_ext8 a, φ_inj h, ext8_ext8]

/-- `mul` by `vg_ghash_aes`'s key of `H` multiplies by `H`. -/
theorem mulV_keyV : MulKey := fun b H => by
  have hu : ρ (mulV (ext8 H H) xInv2) = x * φ H * φ xInv2 := by
    rw [mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add, ρ_ext8_self]
  apply ρ_inj
  rw [mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add, ρ_ext8_self, ρ_ext8_self, keyV,
    φ_ext8_self, hu, φ_mul]
  linear_combination φ b * φ H * x2_φ_xInv2

/-! ## The prepared powers

`Spec.Gcm.preparedPower v` is `v · x⁻¹` in `Q` (`x_φ_preparedPower`), so
`mul` of prepared powers is the prepared power of their product (`prepPow`,
the `PrepPow` that `Pmull/PrepKey.lean` states without the algebra).
-/

section
open Polynomial

/-- `x⁻¹` (`1 + x + x⁶ + x¹²⁷`), the constant `preparedPower` adds. -/
def xInvB : BitVec 128 := 0xc2000000000000000000000000000001#128

theorem gp_xInvB : gp xInvB = 1 + X + X ^ 6 + X ^ 127 := by
  have hb : ∀ d < 128, xInvB.getMsbD d = (d = 0 || d = 1 || d = 6 || d = 127) := by decide +kernel
  ext d
  rw [coeff_gp]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  by_cases hd : d < 128
  · rw [hb d hd]
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 6 ∨ d = 127 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6 ∧ d ≠ 127)) with
      rfl | rfl | rfl | rfl | ⟨h0, h1, h6, h7⟩
    · decide
    · decide
    · decide
    · decide
    · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, h7, Bool.false_eq_true, ↓reduceIte,
        show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
  · have e : xInvB.getMsbD d = false := by
      simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]; omega
    rw [e]
    simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega, show (1 : Nat) ≠ d by omega,
      add_zero, show d ≠ 6 by omega, show d ≠ 127 by omega]

theorem x_φ_xInvB : x * φ xInvB = 1 := by
  simp only [φ, gp_xInvB, map_add, map_one, map_pow, AdjoinRoot.mk_X]
  linear_combination x128 + (x + x ^ 2 + x ^ 7) * two_Q

theorem gp_shl1' (h : BitVec 128) : X * gp (h <<< 1) + C (bit (h.getMsbD 0)) = gp h := by
  ext d
  rw [coeff_add, coeff_C, coeff_gp]
  rcases d with _ | d
  · simp only [mul_coeff_zero, coeff_X_zero, zero_mul, ↓reduceIte, zero_add]
  · rw [coeff_X_mul, coeff_gp, BitVec.getMsbD_shiftLeft]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]

/-- `preparedPower v` is `v · x⁻¹`. -/
theorem x_φ_preparedPower (h : Spec.Gcm.Block) : x * φ (Spec.Gcm.preparedPower h) = φ h := by
  have e := congrArg (AdjoinRoot.mk g) (gp_shl1' h)
  simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at e
  rw [Spec.Gcm.preparedPower, φ_xor, mul_add]
  change x * AdjoinRoot.mk g (gp (h <<< 1)) + _ = AdjoinRoot.mk g (gp h)
  rw [← e]
  split_ifs with hb
  · rw [show (0xc2000000000000000000000000000001 : BitVec 128) = xInvB from rfl, x_φ_xInvB, hb]
    simp only [bit, ↓reduceIte, map_one]
  · rw [φ_zero, Bool.not_eq_true] at *; rw [hb]
    simp only [mul_zero, add_zero, bit, Bool.false_eq_true, ↓reduceIte, map_zero]

/-- The prepared power of `Hᵏ` is `Hᵏ · x⁻¹`. -/
theorem x_φ_preparedPower_hpow (H : Spec.Gcm.Block) (k : Nat) :
    x * φ (Spec.Gcm.preparedPower (Spec.Gcm.hpow H k)) = φ H ^ k := by
  rw [x_φ_preparedPower, φ_hpow]

end

/-- `x` cancels. -/
theorem x_cancel {a b : Q} (h : x * a = x * b) : a = b := by
  linear_combination (x * φ xInv2) * h - (a - b) * x2_φ_xInv2

theorem x_φ_pp (H : Spec.Gcm.Block) (k : Nat) : x * φ (pp H k) = φ H ^ k :=
  x_φ_preparedPower_hpow H k

theorem prepPow : PrepPow where
  key H := by
    apply φ_inj
    apply x_cancel
    rw [keyV, φ_ext8_self, mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add, ρ_ext8_self, x_φ_pp,
      pow_one]
    linear_combination φ H * x2_φ_xInv2
  mul H a b := by
    apply ρ_inj
    rw [mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add, ρ_ext8_self, ρ_ext8_self]
    apply x_cancel
    have hab : x * φ (pp H (a + b)) = φ H ^ a * φ H ^ b := by rw [x_φ_pp, pow_add]
    linear_combination (x * φ (pp H b)) * x_φ_pp H a + φ H ^ a * x_φ_pp H b - hab

end VG.Proof.Gcm.AArch64.Pmull

end

/-!
# GHASH with PMULL: the whole function

`ghash_verified` proves `Impl.Gcm.AArch64.Pmull.ghash` against
`Proof.Gcm.ghashAArch64` (the contract of `vg_ghash`,
`Proof/Gcm/AArch64/Ghash.lean`).

The registers `tReg k` hold `Tₖ` with `x · Tₖ = Hᵏ` (`k = 1 …`, up to 8
once the powers are computed), so that `mul(a, Tₖ) = a · Hᵏ`, `sReg k` the
same with its halves swapped, and `v0` holds `Y` after `i` blocks, as
loaded; the memory is not written until the epilogue stores `Y`.
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## `Y` and the blocks -/

/-- `Y` after `i` blocks. -/
abbrev Ys (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

theorem φ_Ys_succ (s₀ : State) (i : Nat) :
    φ (Ys s₀ (i + 1)) = (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) := by
  rw [Ys, ghashFrom_blocksAt_succ, φ_mul, φ_xor]

/-- What the loops need of the regions: `H` readable, the data readable,
`Y` writable, and `Y` apart from the data (`Pre`, or that of
`vg_ghash_prepared`, whose `H` is followed by its powers). -/
structure Pm (s₀ : State) : Prop where
  h_in : InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofNat 64 0) 16
  d_in : dR s₀ ∈ s₀.rd
  y_in : yR s₀ ∈ s₀.wr
  y_d : (yR s₀).Disjoint (dR s₀)

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem Pm.nb_lt {s₀ : State} (h : Pm s₀) : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem Pre.pm {s₀ : State} (hp : Pre s₀) : Pm s₀ :=
  ⟨⟨hR s₀, by simp [hp.rd], contains_offset (by decide) (by decide)⟩, by simp [hp.rd], by simp [hp.wr],
    hp.y_d⟩

/-- Block `i + j` is in the data. -/
theorem in_blk16 {s₀ : State} (hp : Pm s₀) {i j : Nat} (h : i + j < nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * j)) 16 := by
  have := hp.nb_lt
  refine ⟨dR s₀, List.mem_append_left _ hp.d_in, ?_⟩
  rw [blkAddr, Offset.add_add, ← Nat.mul_add]
  exact contains_offset (by omega) (by omega)

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem shr3_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3).toNat = n / 8 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem shr3_beq {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3 == 0) = decide (n < 8) := by
  by_cases h : n < 8
  · have e : BitVec.ofNat 64 n >>> 3 = 0 :=
      BitVec.eq_of_toNat_eq (by rw [shr3_toNat hn]; show n / 8 = 0; omega)
    rw [e, decide_eq_true h]; rfl
  · have e : BitVec.ofNat 64 n >>> 3 ≠ 0 := fun e => by
      have h' := congrArg BitVec.toNat e
      rw [shr3_toNat hn] at h'
      have : n / 8 = 0 := h'
      omega
    rw [beq_eq_false_iff_ne.mpr e, decide_eq_false h]

theorem shr_beq {n : Nat} (s : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n >>> s == 0) = decide (n < 2 ^ s) := by
  have h : (BitVec.ofNat 64 n >>> s).toNat = n / 2 ^ s := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  by_cases hlt : n < 2 ^ s
  · have e : BitVec.ofNat 64 n >>> s = 0 :=
      BitVec.eq_of_toNat_eq (by rw [h]; exact Nat.div_eq_of_lt hlt)
    rw [e, decide_eq_true hlt]; rfl
  · have e : BitVec.ofNat 64 n >>> s ≠ 0 := fun e => by
      have h' := congrArg BitVec.toNat e
      rw [h] at h'
      have h0 : n / 2 ^ s = 0 := h'
      have := Nat.div_pos (Nat.le_of_not_lt hlt) (Nat.two_pow_pos s)
      omega
    rw [beq_eq_false_iff_ne.mpr e, decide_eq_false hlt]

theorem shr3_bne {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 3 != 0) = decide (8 ≤ n) := by
  rw [bne, shr3_beq hn]
  by_cases h : n < 8
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

theorem ofNat_bne {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  rw [bne, ofNat_beq hk]
  by_cases h : k = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true h]; rfl

/-! ## The invariant -/

/-- What holds after `i` blocks, with the powers up to `K`. -/
structure Inv (s₀ : State) (K i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  c : s.v C = ofVDwords poly poly
  t : ∀ k, 1 ≤ k → k ≤ K → x * φ (s.v (tReg k)) = φ (H₀ s₀) ^ k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = ext8 (s.v (tReg k)) (s.v (tReg k))
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
theorem Inv.of_x6 {s₀ : State} {K i : Nat} {s s' : State} (hI : Inv s₀ K i s)
    (hg : ∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ K i s' where
  le := hI.le
  c := by rw [hv, hI.c]
  t k hk hkK := by rw [hv, hI.t k hk hkK]
  sw k hk hkK := by rw [hv, hI.sw k hk hkK]
  y := by rw [hv, hI.y]
  x0 := by rw [hg .x0 (by decide), hI.x0]
  x1 := by rw [hg .x1 (by decide), hI.x1]
  x2 := by rw [hg .x2 (by decide), hI.x2]
  x3 := by rw [hg .x3 (by decide), hI.x3]
  x5 := by rw [hg .x5 (by decide), hg .x3 (by decide), hI.x5]
  mem := by rw [hm, hI.mem]
  rd := by rw [hrd, hI.rd]
  wr := by rw [hwr, hI.wr]

/-! ## The powers -/

theorem nmem_pow {r a b : VReg} (h1 : r ∉ [LO, MID, HI, T]) (h2 : r ≠ a) (h3 : r ≠ b) :
    r ∉ [LO, MID, HI, T, a] ++ [b] := by
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2⟩, h3⟩

theorem tReg_ne {i j : Nat} (hi : 1 ≤ i) (hi' : i ≤ 8) (hj : 1 ≤ j) (hj' : j ≤ 8) (h : i ≠ j) :
    tReg i ≠ tReg j := fun e => h (tReg_inj i (by omega) j (by omega) hi hj e)

theorem sReg_ne {i j : Nat} (hi : 1 ≤ i) (hi' : i ≤ 8) (hj : 1 ≤ j) (hj' : j ≤ 8) (h : i ≠ j) :
    sReg i ≠ sReg j := fun e => h (sReg_inj i (by omega) j (by omega) hi hj e)

/-- `H'ᴷ⁺¹ = mul(H'ⁱ, H'ʲ)`, from code `m` that computes the product into `sReg (K + 1)`. -/
theorem powWith_ok (m : List Instr) {s₀ : State} {K i j n : Nat} (hi : 1 ≤ i) (hiK : i ≤ K)
    (hj : 1 ≤ j) (hjK : j ≤ K) (hij : i + j = K + 1) (hK : K + 1 ≤ 8) {s : State} (hI : Inv s₀ K n s)
    (hm : WP isa (.block m) s fun s' =>
      ρ (s'.v (sReg (K + 1))) = x * ρ (s.v (sReg i)) * φ (s.v (tReg j)) ∧
        VOnly [LO, MID, HI, T, sReg (K + 1)] s s') :
    WP isa (.block (m ++ ([.vop (.ext (tReg (K + 1)) (sReg (K + 1)) (sReg (K + 1)) 8)] : List Instr)))
      s (Inv s₀ (K + 1) n) := by
  rw [WP.block_append_iff]
  refine WP.mono hm fun s₁ ⟨m₁, o₁⟩ => ?_
  refine WP.mono (swap_ok (tReg (K + 1)) (sReg (K + 1)) s₁) fun s' ⟨w, o₂⟩ => ?_
  have O := o₁.trans o₂
  have kv : ∀ r, r ∉ [LO, MID, HI, T] → r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r :=
    fun r h1 h2 h3 => O.v r (nmem_pow h1 h3 h2)
  have ks : s'.v (sReg (K + 1)) = s₁.v (sReg (K + 1)) := o₂.v _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => tReg_ne_sReg _ _ e.symm)
  have told : ∀ k, 1 ≤ k → k ≤ K → s'.v (tReg k) = s.v (tReg k) := fun k hk hkK =>
    kv _ (tReg_nmem' k) (tReg_ne hk (by omega) (by omega) hK (by omega)) (tReg_ne_sReg _ _)
  have sold : ∀ k, 1 ≤ k → k ≤ K → s'.v (sReg k) = s.v (sReg k) := fun k hk hkK =>
    kv _ (sReg_nmem' k) (fun e => tReg_ne_sReg _ _ e.symm) (sReg_ne hk (by omega) (by omega) hK (by omega))
  refine ⟨hI.le, by rw [kv C (by decide) (ne_tReg _) (ne_sReg _), hI.c],
    fun k hk hkK => ?_, fun k hk hkK => ?_,
    by rw [kv Y (by decide) (ne_tReg _) (ne_sReg _), hI.y], by rw [O.gpr, hI.x0],
    by rw [O.gpr, hI.x1], by rw [O.gpr, hI.x2], by rw [O.gpr, hI.x3], by rw [O.gpr, hI.x5],
    by rw [O.mem, hI.mem], by rw [O.rd, hI.rd], by rw [O.wr, hI.wr]⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [w, φ_ext8_self, m₁, hI.sw i hi hiK, ρ_ext8_self, ← hij, pow_add, ← hI.t i hi hiK,
        ← hI.t j hj hjK]
      ring
    · rw [told k hk hkK', hI.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [ks, w, ext8_ext8]
    · rw [told k hk hkK', sold k hk hkK', hI.sw k hk hkK']

/-- `H'ᴷ⁺¹ = mul(H'ⁱ, H'ʲ)`. -/
theorem pow_ok {s₀ : State} {K i j n : Nat} (hi : 1 ≤ i) (hiK : i ≤ K) (hj : 1 ≤ j) (hjK : j ≤ K)
    (hij : i + j = K + 1) (hK : K + 1 ≤ 8) {s : State} (hI : Inv s₀ K n s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.pow (K + 1) i j)) s (Inv s₀ (K + 1) n) :=
  powWith_ok _ hi hiK hj hjK hij hK hI (mul_ok (sReg (K + 1)) (sReg i) (sReg j) (tReg j) s
    (sReg_free _) (sReg_free _) (tReg_free _) (hI.sw j hj hjK) hI.c)

/-- The square `sqr` computes is the product `mulV` would: its middle products cancel. -/
theorem sqr_mulV (a t : BitVec 128) (h : a = ext8 t t) :
    reduce ⟨polyMul (vdword a 1) (vdword a 1), 0, polyMul (vdword a 0) (vdword a 0)⟩ = mulV a t := by
  have hm : polyMul (vdword a 0) (vdword t 0) ^^^ polyMul (vdword a 1) (vdword t 1) = 0 := by
    rw [h, vdword_ext8_0, vdword_ext8_1, polyMul_comm (vdword t 0), BitVec.xor_self]; rfl
  have zx : ∀ x : BitVec 128, 0 ^^^ x = x := fun x => by simp
  rw [mulV, ← h]
  simp only [Prod.acc, Prod.zero, zx, hm]

/-- `H'ᴷ⁺¹ = mul(H'ⁱ, H'ʲ)`, by `powS`. -/
theorem powS_ok {s₀ : State} {K i j n : Nat} (hi : 1 ≤ i) (hiK : i ≤ K) (hj : 1 ≤ j) (hjK : j ≤ K)
    (hij : i + j = K + 1) (hK : K + 1 ≤ 8) {s : State} (hI : Inv s₀ K n s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.powS (K + 1) i j)) s (Inv s₀ (K + 1) n) := by
  rw [Impl.Gcm.AArch64.Pmull.powS]
  refine powWith_ok _ hi hiK hj hjK hij hK hI ?_
  split
  · next he =>
    subst he
    refine WP.mono (sqr_ok (sReg (K + 1)) (sReg i) s (sReg_free _) hI.c) fun _ ⟨h, o⟩ => ⟨?_, o⟩
    rw [h, sqr_mulV _ _ (hI.sw i hi hiK), mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add]
  · refine WP.mono (mulD_ok (sReg (K + 1)) (sReg i) (sReg j) (tReg j) s (sReg_free _) (sReg_free _)
      (tReg_free _) (hI.sw j hj hjK) hI.c) fun _ ⟨h, o⟩ => ⟨?_, o⟩
    rw [h, mulV, ρ_reduce, Prod.val_acc, Prod.val_zero, zero_add]

theorem powersS_ok {s₀ : State} {n : Nat} {s : State} (hI : Inv s₀ 1 n s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.powersS) s (Inv s₀ 8 n) := by
  simp only [Impl.Gcm.AArch64.Pmull.powersS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (powS_ok (K := 1) (i := 1) (j := 1) le_rfl le_rfl le_rfl le_rfl rfl (by decide) hI)
    fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powS_ok (K := 2) (i := 2) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powS_ok (K := 3) (i := 2) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powS_ok (K := 4) (i := 3) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powS_ok (K := 5) (i := 3) (j := 3) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (powS_ok (K := 6) (i := 4) (j := 3) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₆) fun s₇ h₇ => ?_
  exact powS_ok (K := 7) (i := 4) (j := 4) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) h₇

theorem powers_ok {s₀ : State} {n : Nat} {s : State} (hI : Inv s₀ 1 n s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.powers) s (Inv s₀ 8 n) := by
  simp only [Impl.Gcm.AArch64.Pmull.powers, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 1) (i := 1) (j := 1) le_rfl le_rfl le_rfl le_rfl rfl (by decide) hI)
    fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 2) (i := 2) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 3) (i := 2) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 4) (i := 4) (j := 1) (by decide) le_rfl le_rfl (by decide) rfl
    (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 5) (i := 4) (j := 2) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow_ok (K := 6) (i := 4) (j := 3) (by decide) (by decide) (by decide) (by decide)
    rfl (by decide) h₆) fun s₇ h₇ => ?_
  exact pow_ok (K := 7) (i := 4) (j := 4) (by decide) (by decide) (by decide) (by decide) rfl
    (by decide) h₇

/-! ## The blocks -/

/-- After `j` blocks of `k` from the second on, from `sB`: with the first
block's product, which is added last, the product is `Y` after `j + 1` blocks
times `Hᵏ⁻¹⁻ʲ`. -/
def BI (s₀ sB : State) (k i j : Nat) (s : State) : Prop :=
  (prod s).val + (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * φ (H₀ s₀) ^ k =
      φ (Ys s₀ (i + 1 + j)) * φ (H₀ s₀) ^ (k - 1 - j) ∧
    VOnly [LO, MID, HI, A, T] sB s

theorem blk_ok {s₀ : State} (hp : Pm s₀) {K k i j : Nat} (hkK : k ≤ K) (hK : K ≤ 8)
    (hj : j + 1 < k) (hi : i + k ≤ nb s₀) {sB s : State} (hI : Inv s₀ K i sB)
    (hB : BI s₀ sB k i j s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.blk k j)) s (BI s₀ sB k i (j + 1)) := by
  obtain ⟨hv, o⟩ := hB
  rw [Impl.Gcm.AArch64.Pmull.blk, WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x2 (16 * (j + 1)) s (Nat.mul_mod_right 16 _) (by omega)
    (by rw [o.rd, o.wr, o.gpr, hI.rd, hI.wr, hI.x2]; exact in_blk16 hp (by omega)))
    fun s₁ ⟨l₁, o₁⟩ => ?_
  refine WP.mono (acc_ok A (sReg (k - 1 - j)) (tReg (k - 1 - j)) s₁ free_A (sReg_free _)
    (tReg_free _)) fun s₂ ⟨p₂, o₂⟩ => ⟨?_, (o.trans (o₁.trans o₂)).weaken⟩
  have o₀₁ := o.trans o₁
  have hs : s₁.v (sReg (k - 1 - j)) = ext8 (s₁.v (tReg (k - 1 - j))) (s₁.v (tReg (k - 1 - j))) := by
    rw [o₀₁.v _ (sReg_nmem' _), o₀₁.v _ (tReg_nmem' _), hI.sw _ (by omega) (by omega)]
  have ht : x * φ (s₁.v (tReg (k - 1 - j))) = φ (H₀ s₀) ^ (k - 1 - j) := by
    rw [o₀₁.v _ (tReg_nmem' _), hI.t _ (by omega) (by omega)]
  have ha : blockAt s.mem (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + 1))) =
      blockAt s₀.mem (blkAddr s₀ (i + 1 + j)) := by
    rw [o.mem, o.gpr, hI.mem, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add,
      show i + (j + 1) = i + 1 + j by omega]
  have e : φ (H₀ s₀) ^ (k - 1 - j) = φ (H₀ s₀) ^ (k - 1 - (j + 1)) * φ (H₀ s₀) := by
    rw [← pow_succ]; exact congrArg _ (by omega)
  rw [p₂, hs, Prod.val_acc, o₁.prod (by decide) (by decide) (by decide), l₁, ha,
    show i + 1 + (j + 1) = (i + 1 + j) + 1 by omega, φ_Ys_succ]
  linear_combination hv + (φ (Ys s₀ (i + 1 + j)) + φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + j)))) * e +
    φ (blockAt s₀.mem (blkAddr s₀ (i + 1 + j))) * ht

theorem body_ok {s₀ : State} (hp : Pm s₀) {K k i : Nat} (hk : 1 ≤ k) (hkK : k ≤ K) (hK : K ≤ 8)
    (hi : i + k ≤ nb s₀) {s : State} (hI : Inv s₀ K i s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.body k)) s (Inv s₀ K (i + k)) := by
  have hn := hp.nb_lt
  simp only [Impl.Gcm.AArch64.Pmull.body, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  have b₀ : BI s₀ s k i 0 s₁ := by
    refine ⟨?_, o₁.weaken⟩
    have e : φ (H₀ s₀) ^ k = φ (H₀ s₀) ^ (k - 1 - 0) * φ (H₀ s₀) := by
      rw [← pow_succ]; exact congrArg _ (by omega)
    rw [p₁, Prod.val_zero, zero_add, Nat.add_zero, φ_Ys_succ]
    linear_combination (φ (Ys s₀ i) + φ (blockAt s₀.mem (blkAddr s₀ i))) * e
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := k - 1) (BI s₀ s k i)
    (fun j s' hj hB => blk_ok hp hkK hK (by omega) hi hI hB) (k - 1) (Nat.le_refl _) s₁ b₀)
    fun s₂ ⟨p₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x2 (16 * 0) s₂ rfl (by decide)
    (by rw [o₂.rd, o₂.wr, o₂.gpr, hI.rd, hI.wr, hI.x2]; exact in_blk16 hp (by omega)))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₃) fun s₄ ⟨e₄, o₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok A (sReg k) (tReg k) s₄ free_A (sReg_free _) (tReg_free _))
    fun s₅ ⟨p₅, o₅⟩ => ?_
  have o₂₄ := o₂.trans (o₃.trans o₄)
  have hv : (prod s₅).val = φ (Ys s₀ (i + k)) := by
    have hs : s₄.v (sReg k) = ext8 (s₄.v (tReg k)) (s₄.v (tReg k)) := by
      rw [o₂₄.v _ (sReg_nmem' _), o₂₄.v _ (tReg_nmem' _), hI.sw _ hk hkK]
    have ht : x * φ (s₄.v (tReg k)) = φ (H₀ s₀) ^ k := by
      rw [o₂₄.v _ (tReg_nmem' _), hI.t _ hk hkK]
    have hy : ρ (s₃.v Y) = φ (Ys s₀ i) := by
      rw [(o₂.trans o₃).v Y (by decide), hI.y]
    have ha : blockAt s₂.mem (s₂.gpr .x2 + BitVec.ofNat 64 (16 * 0)) =
        blockAt s₀.mem (blkAddr s₀ i) := by
      rw [o₂.mem, o₂.gpr, hI.mem, hI.x2, Nat.mul_zero, add_ofNat_zero]
    rw [p₅, hs, Prod.val_acc, (o₃.trans o₄).prod (by decide) (by decide) (by decide), e₄, ρ_xor,
      l₃, hy, ha]
    have e := p₂
    rw [show i + 1 + (k - 1) = i + k by omega, show k - 1 - (k - 1) = 0 by omega, pow_zero,
      mul_one] at e
    linear_combination e + (φ (blockAt s₀.mem (blkAddr s₀ i)) + φ (Ys s₀ i)) * ht
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok Y s₅ (by rw [(o₂₄.trans o₅).v C (by decide), hI.c]))
    fun s₆ ⟨r₆, o₆⟩ => ?_
  refine WP.mono (advance_ok k (by omega) s₆)
    fun s' ⟨f2, f3, f5, fg, fv, fm, frd, fwr⟩ => ?_
  have O : VOnly [LO, MID, HI, A, T, Y] s s₆ :=
    (o₂.trans ((o₃.trans (o₄.trans o₅)).trans o₆)).weaken
  have kv : ∀ r, r ∉ [LO, MID, HI, A, T, Y] → s'.v r = s.v r := fun r h => by rw [fv, O.v r h]
  have kg : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s'.gpr r = s.gpr r := fun r h2 h3 h5 => by
    rw [fg r h2 h3 h5, O.gpr]
  refine ⟨by omega, by rw [kv C (by decide), hI.c],
    fun m hm hmK => by rw [kv _ (tReg_nmem' _), hI.t m hm hmK],
    fun m hm hmK => by rw [kv _ (sReg_nmem' _), kv _ (tReg_nmem' _), hI.sw m hm hmK], ?_,
    by rw [kg .x0 (by decide) (by decide) (by decide), hI.x0],
    by rw [kg .x1 (by decide) (by decide) (by decide), hI.x1], ?_, ?_, f5,
    by rw [fm, O.mem, hI.mem], by rw [frd, O.rd, hI.rd], by rw [fwr, O.wr, hI.wr]⟩
  · rw [fv, r₆, ρ_reduce, hv]
  · rw [f2, O.gpr, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add]
  · rw [f3, O.gpr, hI.x3, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]

/-! ## The prologue and the epilogue -/

theorem prologue_ok {s₀ : State} (hp : Pm s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologue) s₀ (Inv s₀ 1 0) := by
  simp only [Impl.Gcm.AArch64.Pmull.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x0 0 s₀ rfl (by decide)
    hp.h_in) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₁) fun s₂ ⟨c₂, t₂, w₂, kv₂, kg₂, m₂, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok (sReg 1) A (sReg 2) (tReg 2) s₂ free_A (sReg_free _) (tReg_free _)
    (by rw [w₂, t₂]) c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have g₄ : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s₄.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  have mem₄ : s₄.mem = s₀.mem := by rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok Y .x1 0 s₄ rfl (by decide)
    (by rw [o₄.rd, o₄.wr, o₃.rd, o₃.wr, rd₂, wr₂, o₁.rd, o₁.wr,
      g₄ .x1 (by decide) (by decide) (by decide)]
        exact ⟨yR s₀, List.mem_append_right _ hp.y_in, contains_offset (by decide) (by decide)⟩))
    fun s₅ ⟨l₅, o₅⟩ => ?_
  refine WP.mono (lsr_ok .x5 .x3 3 (by decide) s₅) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [fg r h5, o₅.gpr, g₄ r h5 h6 h7]
  have O : VOnly ([tReg 1] ++ [Y]) s₃ s₅ := o₄.trans o₅
  have t₁ : s'.v (tReg 1) = ext8 (s₃.v (sReg 1)) (s₃.v (sReg 1)) := by
    rw [fv, o₅.v _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact (ne_tReg (r := Y) 1).symm), w₄]
  have s₁' : s'.v (sReg 1) = s₃.v (sReg 1) := by
    rw [fv, O.v _ (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => tReg_ne_sReg _ _ e.symm, (ne_sReg (r := Y) 1).symm⟩)]
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide) (ne_tReg 2) (ne_sReg 2)
  refine ⟨Nat.zero_le _, ?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_, ?_,
    by rw [g .x0 (by decide) (by decide) (by decide)],
    by rw [g .x1 (by decide) (by decide) (by decide)],
    by rw [g .x2 (by decide) (by decide) (by decide)]; simp [blkAddr],
    by rw [g .x3 (by decide) (by decide) (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₅.mem, mem₄],
    by rw [frd, o₅.rd, o₄.rd, o₃.rd, rd₂, o₁.rd], by rw [fwr, o₅.wr, o₄.wr, o₃.wr, wr₂, o₁.wr]⟩
  · have h : C ∉ [LO, MID, HI, T, sReg 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, by decide, ne_sReg 1⟩
    have h' : C ∉ [tReg 1] ++ [Y] := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨ne_tReg 1, by decide⟩
    rw [fv, O.v C h', o₃.v C h, c₂]
  · obtain rfl : k = 1 := by omega
    rw [t₁, φ_ext8_self, m₃, hA₂, l₁, t₂, add_ofNat_zero]
    linear_combination φ (H₀ s₀) * x2_φ_xInv2
  · obtain rfl : k = 1 := by omega
    rw [t₁, s₁', ext8_ext8]
  · rw [fv, l₅, mem₄, g₄ .x1 (by decide) (by decide) (by decide), add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

/-- `prologue`, with `H'` by `twist`. -/
theorem prologueT_ok {s₀ : State} (hp : Pm s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologueT) s₀ (Inv s₀ 1 0) := by
  simp only [Impl.Gcm.AArch64.Pmull.prologueT, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok A .x0 0 s₀ rfl (by decide)
    hp.h_in) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constC_ok s₁) fun s₂ ⟨c₂, kv₂, kg₂, m₂, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (twist_ok (sReg 1) s₂ c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have g₄ : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s₄.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [o₄.gpr, o₃.gpr, kg₂ r h5, o₁.gpr]
  have mem₄ : s₄.mem = s₀.mem := by rw [o₄.mem, o₃.mem, m₂, o₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok Y .x1 0 s₄ rfl (by decide)
    (by rw [o₄.rd, o₄.wr, o₃.rd, o₃.wr, rd₂, wr₂, o₁.rd, o₁.wr,
      g₄ .x1 (by decide) (by decide) (by decide)]
        exact ⟨yR s₀, List.mem_append_right _ hp.y_in, contains_offset (by decide) (by decide)⟩))
    fun s₅ ⟨l₅, o₅⟩ => ?_
  refine WP.mono (lsr_ok .x5 .x3 3 (by decide) s₅) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s₀.gpr r := fun r h5 h6 h7 => by
    rw [fg r h5, o₅.gpr, g₄ r h5 h6 h7]
  have O : VOnly ([tReg 1] ++ [Y]) s₃ s₅ := o₄.trans o₅
  have t₁ : s'.v (tReg 1) = ext8 (s₃.v (sReg 1)) (s₃.v (sReg 1)) := by
    rw [fv, o₅.v _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact (ne_tReg (r := Y) 1).symm), w₄]
  have s₁' : s'.v (sReg 1) = s₃.v (sReg 1) := by
    rw [fv, O.v _ (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => tReg_ne_sReg _ _ e.symm, (ne_sReg (r := Y) 1).symm⟩)]
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide)
  refine ⟨Nat.zero_le _, ?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_, ?_,
    by rw [g .x0 (by decide) (by decide) (by decide)],
    by rw [g .x1 (by decide) (by decide) (by decide)],
    by rw [g .x2 (by decide) (by decide) (by decide)]; simp [blkAddr],
    by rw [g .x3 (by decide) (by decide) (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₅.mem, mem₄],
    by rw [frd, o₅.rd, o₄.rd, o₃.rd, rd₂, o₁.rd], by rw [fwr, o₅.wr, o₄.wr, o₃.wr, wr₂, o₁.wr]⟩
  · have h : C ∉ [LO, MID, HI, T, sReg 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, by decide, by decide, ne_sReg 1⟩
    have h' : C ∉ [tReg 1] ++ [Y] := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨ne_tReg 1, by decide⟩
    rw [fv, O.v C h', o₃.v C h, c₂]
  · obtain rfl : k = 1 := by omega
    rw [t₁, φ_ext8_self, m₃, twistV_ρ, hA₂, l₁, add_ofNat_zero, pow_one]
  · obtain rfl : k = 1 := by omega
    rw [t₁, s₁', ext8_ext8]
  · rw [fv, l₅, mem₄, g₄ .x1 (by decide) (by decide) (by decide), add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

theorem epilogue_ok {s₀ : State} (hp : Pm s₀) {K : Nat} {s : State} (hI : Inv s₀ K (nb s₀) s) :
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

/-! ## The whole function -/

theorem WP.seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun s' => WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h
  exact WP.seq (WP.mono h fun _ h' => WP.seq h')

/-- The remaining blocks, one at a time. -/
theorem ones_ok {s₀ : State} (hp : Pm s₀) {K i : Nat} (hK1 : 1 ≤ K) (hK8 : K ≤ 8) {s : State}
    (hI : Inv s₀ K i s) :
    WP isa (.ite (.zero .x .x3) (.block [])
      (.loop (.block (Impl.Gcm.AArch64.Pmull.body 1)) (.nonzero .x .x3))) s (Inv s₀ K (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x3) s = some (decide (nb s₀ - i = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI.x3,
      ofNat_beq (show nb s₀ - i < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i = nb s₀ := by have := hI.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI)
  · let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ K i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 1)) s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ Inv s₀ K (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hp le_rfl hK1 hK8 (by omega) hI) fun s' hI' => ?_
      have hev : eval (.nonzero .x .x3) s' = some (decide (nb s₀ - (i + 1) ≠ 0)) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x3,
          ofNat_bne (show nb s₀ - (i + 1) < 2 ^ 64 by omega)]
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by rw [hev, decide_eq_false (not_not.mpr hlast)], this ▸ hI'⟩
      · exact .inr ⟨by rw [hev, decide_eq_true hlast], nb s₀ - (i + 1), by omega, i + 1, rfl,
          by omega, hI'⟩
    have hlt : i < nb s₀ := by have := hI.le; simp only [decide_eq_false_iff_not] at h; omega
    exact WP.loop (M := isa) Inv1 hstep (nb s₀ - i) s ⟨i, rfl, hlt, hI⟩

/-- `k` blocks if bit `sh` of the remaining count (less than `2 ^ (sh + 1)`) is
set, with `k = 2 ^ sh`. -/
theorem bit_ok {s₀ : State} (hp : Pm s₀) {i : Nat} (sh k : Nat) (hk : k = 2 ^ sh) (hk1 : 1 ≤ k)
    (hk8 : k ≤ 8) (hsh : sh < 64) (hi : nb s₀ - i < 2 * k) {s : State} (hI : Inv s₀ 8 i s) :
    WP isa (.seq (.block [.lsr .x .x6 .x3 sh])
      (.ite (.zero .x .x6) (.block []) (.block (Impl.Gcm.AArch64.Pmull.body k)))) s
      (fun s' => ∃ i', nb s₀ - i' < k ∧ Inv s₀ 8 i' s') := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (lsr_ok .x6 .x3 sh hsh s) fun s₁ ⟨f6, fg, fv, fm, frd, fwr⟩ => ?_)
  have hI₁ := hI.of_x6 fg fv fm frd fwr
  have hev : eval (.zero .x .x6) s₁ = some (decide (nb s₀ - i < k)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, f6, hI.x3,
      shr_beq sh (show nb s₀ - i < 2 ^ 64 by omega), hk]
  refine WP.ite _ hev (fun h => WP.block_nil ⟨i, by simpa using h, hI₁⟩) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  exact WP.mono (body_ok hp hk1 hk8 le_rfl (by omega) hI₁) fun s' h' => ⟨i + k, by omega, h'⟩

/-- The last `n mod 8` blocks, once the powers are computed. -/
theorem tail_ok {s₀ : State} (hp : Pm s₀) {i : Nat} (hi : nb s₀ - i < 8) {s : State}
    (hI : Inv s₀ 8 i s) :
    WP isa Impl.Gcm.AArch64.Pmull.tail s (Inv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  unfold Impl.Gcm.AArch64.Pmull.tail
  refine WP.seq_assoc (WP.mono (bit_ok hp 2 4 rfl (by decide) (by decide) (by decide) (by omega) hI)
    fun s₁ ⟨i₁, hi₁, hI₁⟩ => ?_)
  refine WP.seq_assoc (WP.mono (bit_ok hp 1 2 rfl (by decide) (by decide) (by decide) (by omega)
    hI₁) fun s₂ ⟨i₂, hi₂, hI₂⟩ => ?_)
  have hev : eval (.zero .x .x3) s₂ = some (decide (nb s₀ - i₂ = 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₂.x3,
      ofNat_beq (show nb s₀ - i₂ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · have : i₂ = nb s₀ := by have := hI₂.le; simp only [decide_eq_true_eq] at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · simp only [decide_eq_false_iff_not] at h
    have : i₂ + 1 = nb s₀ := by omega
    exact this ▸ body_ok hp le_rfl (by decide) le_rfl (by omega) hI₂

/-- GHASH from a prologue that sets up `H'` and powers that set up `H'²` to
`H'⁸` (`Inv`). -/
theorem loopsWith_ok {s₀ : State} (hp : Pm s₀) {pro pow : List Instr}
    (hpro : WP isa (.block pro) s₀ (Inv s₀ 1 0))
    (hpow : ∀ n s, Inv s₀ 1 n s → WP isa (.block pow) s (Inv s₀ 8 n)) :
    WP isa (Impl.Gcm.AArch64.Pmull.ghashWith pro pow) s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono hpro fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ K, Inv s₀ K (nb s₀) s) ?_
    fun s₂ ⟨K, hI₂⟩ => epilogue_ok hp hI₂)
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun _ => WP.mono (ones_ok hp le_rfl (by decide) hI₁) fun s h => ⟨1, h⟩)
    (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  refine WP.seq (WP.mono (hpow _ _ hI₁) fun s₃ hI₃ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s) ?_
    fun s₄ ⟨i, hi, hI₄⟩ => WP.mono (tail_ok hp hi hI₄) fun s h => ⟨8, h⟩)
  let Inv8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ Inv s₀ 8 i s
  have hstep : ∀ m s, Inv8 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 8)) s (fun s' =>
      (eval (.nonzero .x .x5) s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s') ∨
      (eval (.nonzero .x .x5) s' = some true ∧ ∃ m' < m, Inv8 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (body_ok hp (by decide) le_rfl le_rfl hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x5) s' = some (decide (8 ≤ nb s₀ - (i + 8))) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x5, hI'.x3,
        shr3_bne (show nb s₀ - (i + 8) < 2 ^ 64 by omega)]
    by_cases h8 : 8 ≤ nb s₀ - (i + 8)
    · exact .inr ⟨by rw [hev, decide_eq_true h8], nb s₀ - (i + 8), by omega, i + 8, rfl,
        by omega, hI'⟩
    · exact .inl ⟨by rw [hev, decide_eq_false h8], i + 8, by omega, hI'⟩
  exact WP.loop (M := isa) Inv8 hstep (nb s₀) s₃ ⟨0, rfl, by omega, hI₃⟩

theorem loops_ok {s₀ : State} (hp : Pm s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghash s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' :=
  loopsWith_ok hp (prologueT_ok hp) fun _ _ h => powersS_ok h

/-- Whether a register is not one of `preserved`, as one `match`: the
kernel evaluates `(dsts i).all notPres` on every instruction several times
faster than `preserved.all fun r => !clobbers i r`. -/
private def notPres : Reg → Bool
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28 | .x30 => false
  | _ => true

private theorem keeps_pres {c : Prog isa} (h : c.allInstrs (fun i => (dsts i).all notPres) = true) :
    c.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
  rw [Code.allInstrs_eq] at h ⊢
  refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun r hr => ?_
  have hn : notPres r = false := by revert r; decide
  simp only [clobbers_eq_false_of_all (List.all_eq_true.mp h i hi) hn, Bool.not_false]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loops_ok (Pre.pm hp)) (keeps_pres (by decide +kernel))
    (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghash := by
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
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghash (Proof.Gcm.ghashContract AArch64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Proof.Gcm.ghashContract, Proof.Gcm.ghashSig, Proof.Gcm.ghashAArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Gcm.AArch64.satState] using Proof.Gcm.AArch64.satState)

/-! ## With the prepared powers

`vg_ghash_prepared_aes` loads `H'ᵏ = pp H k` from the context
(`Impl.Gcm.AArch64.Pmull.powOff`), where `x · pp H k = Hᵏ`
(`x_φ_preparedPower_hpow`), instead of computing it; the loops are
`ghash`'s (`loopsWith_ok`). -/

theorem pm_of_prepared {s₀ : State} (h : Proof.Gcm.ghashPreparedAArch64.pre s₀) : Pm s₀ := by
  obtain ⟨hrd, hwr, -, -, hyd, -, -, -⟩ := h
  exact ⟨⟨⟨hA s₀, 144⟩, by simp [hrd], contains_offset (by decide) (by decide)⟩, by simp [hrd],
    by simp [hwr], hyd⟩

theorem sub240_add (a : Addr) {d : Nat} (hd : 240 ≤ d) :
    a - 240 + BitVec.ofNat 64 d = a + BitVec.ofNat 64 (d - 240) := by
  have e : BitVec.ofNat 64 d = BitVec.ofNat 64 240 + BitVec.ofNat 64 (d - 240) := by
    rw [BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' hd]
  rw [e, ← BitVec.add_assoc]
  exact congrArg (· + BitVec.ofNat 64 (d - 240)) (BitVec.sub_add_cancel a _)

/-- The power `H'ᵏ` at `h + powOff k`, as `tReg k` holds it. -/
theorem read_powOff {s₀ : State} (h : Proof.Gcm.ghashPreparedAArch64.pre s₀) {k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ 8) :
    x * φ (s₀.mem.read (hA s₀ + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.powOff k)) 16) =
      φ (H₀ s₀) ^ k := by
  have hr := h.2.2.2.2.2.2.2
  have hH : Spec.Gcm.ctxH s₀.mem (hA s₀ - 240) = H₀ s₀ := by
    show blockAt s₀.mem (hA s₀ - 240 + 240) = _
    rw [BitVec.sub_add_cancel]
  have e : ∀ d, 240 ≤ d → s₀.mem.readW (hA s₀ - 240 + BitVec.ofNat 64 d) 128 =
      s₀.mem.read (hA s₀ + BitVec.ofNat 64 (d - 240)) 16 := fun d hd => by
    rw [sub240_add _ hd, Mem.readW]; rfl
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · obtain ⟨hv, -⟩ := hr (j - 1) (by omega)
    rw [e _ (by omega), show 256 + 32 * (j - 1) - 240 = Impl.Gcm.AArch64.Pmull.powOff (2 * j) by
      simp only [Impl.Gcm.AArch64.Pmull.powOff, Nat.mul_mod_right, ↓reduceIte]; omega] at hv
    rw [hv, hH, show 2 * (j - 1) + 2 = 2 * j by omega, x_φ_preparedPower_hpow]
  · obtain ⟨-, hv⟩ := hr j (by omega)
    rw [e _ (by omega), show 272 + 32 * j - 240 = Impl.Gcm.AArch64.Pmull.powOff (2 * j + 1) by
      simp only [Impl.Gcm.AArch64.Pmull.powOff, show (2 * j + 1) % 2 = 1 by omega, Nat.one_ne_zero,
        ↓reduceIte]; omega] at hv
    rw [hv, hH, x_φ_preparedPower_hpow]

theorem loadPow_ok (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr)
    (s.gpr .x0 + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.powOff k)) 16) (hk : k ≤ 48) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPow k)) s fun s' =>
      s'.v (tReg k) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.powOff k)) 16 ∧
      s'.v (sReg k) = ext8 (s'.v (tReg k)) (s'.v (tReg k)) ∧ VOnly [tReg k, sReg k] s s' := by
  have ho : Impl.Gcm.AArch64.Pmull.powOff k % 16 = 0 := by
    unfold Impl.Gcm.AArch64.Pmull.powOff; split <;> omega
  have ho' : Impl.Gcm.AArch64.Pmull.powOff k < 4096 * 16 := by
    unfold Impl.Gcm.AArch64.Pmull.powOff; split <;> omega
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq ho ho' hin, ?_⟩
  refine WP.mono (swap_ok (sReg k) (tReg k) _) fun s' ⟨w, o⟩ => ?_
  have ts : tReg k ∉ [sReg k] := by
    simp only [List.mem_singleton]; exact tReg_ne_sReg _ _
  refine ⟨by rw [o.v _ ts]; simp only [v_setV, ite_true], by rw [w, o.v _ ts], ⟨fun r hr => ?_, o.gpr, o.mem,
    o.rd, o.wr, o.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [o.v r (by simp only [List.mem_singleton]; exact hr.2)]
  simp only [v_setV, hr.1, ite_false]

theorem prologueP_ok {s₀ : State} (h : Proof.Gcm.ghashPreparedAArch64.pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologueP) s₀ (Inv s₀ 1 0) := by
  have hp := pm_of_prepared h
  have hrd := h.1
  simp only [Impl.Gcm.AArch64.Pmull.prologueP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadPow_ok 1 s₀ ⟨⟨hA s₀, 144⟩, by simp [hrd], contains_offset (by decide) (by decide)⟩
    (by decide)) fun s₁ ⟨t₁, w₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  have hcb : WP isa (.block ([.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)] : List Instr)) s₁ fun s₂ =>
      s₂.v C = ofVDwords poly poly ∧ (∀ r, r ≠ C → s₂.v r = s₁.v r) ∧
      (∀ r, r ≠ .x5 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_x (show 16 * 3 < 64 by decide),
        exec_dup_d2]; rfl, ?_⟩
    refine ⟨by simp only [v_setV, ite_true, gpr_write_x]; decide, fun r hr => by simp only [v_setV, hr, ite_false,
      v_write], fun r hr => by simp only [gpr_setV, gpr_write_x, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono hcb fun s₂ ⟨c₂, v₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok Y .x1 0 s₂ rfl (by decide)
    (by rw [rd₂, wr₂, o₁.rd, o₁.wr, g₂ .x1 (by decide), o₁.gpr]
        exact ⟨yR s₀, List.mem_append_right _ hp.y_in, contains_offset (by decide) (by decide)⟩))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  refine WP.mono (lsr_ok .x5 .x3 3 (by decide) s₃) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → s'.gpr r = s₀.gpr r := fun r h5 => by
    rw [fg r h5, o₃.gpr, g₂ r h5, o₁.gpr]
  have mem₂ : s₂.mem = s₀.mem := by rw [m₂, o₁.mem]
  have t' : s'.v (tReg 1) = s₁.v (tReg 1) := by
    rw [fv, o₃.v _ (by simp only [List.mem_singleton]; exact (ne_tReg (r := Y) 1).symm),
      v₂ _ (ne_tReg (r := C) 1).symm]
  have s' : s'.v (sReg 1) = s₁.v (sReg 1) := by
    rw [fv, o₃.v _ (by simp only [List.mem_singleton]; exact (ne_sReg (r := Y) 1).symm),
      v₂ _ (ne_sReg (r := C) 1).symm]
  refine ⟨Nat.zero_le _, by rw [fv, o₃.v C (by decide), c₂], fun k hk hk1 => ?_, fun k hk hk1 => ?_, ?_,
    by rw [g .x0 (by decide)], by rw [g .x1 (by decide)],
    by rw [g .x2 (by decide)]; simp [blkAddr], by rw [g .x3 (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₃.mem, mem₂],
    by rw [frd, o₃.rd, rd₂, o₁.rd], by rw [fwr, o₃.wr, wr₂, o₁.wr]⟩
  · obtain rfl : k = 1 := by omega
    rw [t', t₁]
    exact read_powOff h (by decide) (by decide)
  · obtain rfl : k = 1 := by omega
    rw [t', s', w₁]
  · rw [fv, l₃, mem₂, g₂ .x1 (by decide), o₁.gpr, add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

/-- `H'ᴷ⁺¹` loaded. -/
theorem loadPowI_ok {s₀ : State} (h : Proof.Gcm.ghashPreparedAArch64.pre s₀) {K n : Nat} (hK : 1 ≤ K)
    (hK8 : K + 1 ≤ 8) {s : State} (hI : Inv s₀ K n s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPow (K + 1))) s (Inv s₀ (K + 1) n) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.powOff (K + 1))) 16 := by
    rw [hI.rd, hI.wr, hI.x0]
    refine ⟨⟨hA s₀, 144⟩, by simp [h.1], contains_offset ?_ ?_⟩ <;>
      (unfold Impl.Gcm.AArch64.Pmull.powOff; split <;> omega)
  refine WP.mono (loadPow_ok (K + 1) s hin (by omega)) fun s' ⟨t, w, o⟩ => ?_
  have kv : ∀ r, r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r := fun r h1 h2 =>
    o.v r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  have told : ∀ k, 1 ≤ k → k ≤ K → s'.v (tReg k) = s.v (tReg k) := fun k hk hkK =>
    kv _ (tReg_ne hk (by omega) (by omega) hK8 (by omega)) (tReg_ne_sReg _ _)
  have sold : ∀ k, 1 ≤ k → k ≤ K → s'.v (sReg k) = s.v (sReg k) := fun k hk hkK =>
    kv _ (fun e => tReg_ne_sReg _ _ e.symm) (sReg_ne hk (by omega) (by omega) hK8 (by omega))
  refine ⟨hI.le, by rw [kv C (ne_tReg _) (ne_sReg _), hI.c], fun k hk hkK => ?_, fun k hk hkK => ?_,
    by rw [kv Y (ne_tReg _) (ne_sReg _), hI.y], by rw [o.gpr, hI.x0],
    by rw [o.gpr, hI.x1], by rw [o.gpr, hI.x2], by rw [o.gpr, hI.x3], by rw [o.gpr, hI.x5],
    by rw [o.mem, hI.mem], by rw [o.rd, hI.rd], by rw [o.wr, hI.wr]⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [t, hI.x0, hI.mem]; exact read_powOff h hk (by omega)
    · rw [told k hk hkK', hI.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · exact w
    · rw [told k hk hkK', sold k hk hkK', hI.sw k hk hkK']

theorem powersP_ok {s₀ : State} (h : Proof.Gcm.ghashPreparedAArch64.pre s₀) {n : Nat} {s : State}
    (hI : Inv s₀ 1 n s) : WP isa (.block Impl.Gcm.AArch64.Pmull.powersP) s (Inv s₀ 8 n) := by
  simp only [Impl.Gcm.AArch64.Pmull.powersP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadPowI_ok h (K := 1) le_rfl (by decide) hI) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPowI_ok h (K := 2) (by decide) (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPowI_ok h (K := 3) (by decide) (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPowI_ok h (K := 4) (by decide) (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPowI_ok h (K := 5) (by decide) (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPowI_ok h (K := 6) (by decide) (by decide) h₆) fun s₇ h₇ => ?_
  exact loadPowI_ok h (K := 7) (by decide) (by decide) h₇

theorem correctP {s₀ : State} (hs : Proof.Gcm.ghashPreparedAArch64.pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghashP s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved)
    (loopsWith_ok (pm_of_prepared hs) (prologueP_ok hs) fun _ _ hI => powersP_ok hs hI)
    (keeps_pres (by decide +kernel)) (by decide +kernel)) fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghashP_correct (s : State) (hs : Proof.Gcm.ghashPreparedAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghashP s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashPreparedAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correctP hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashP_ct : ConstantTime isa Proof.Gcm.ghashPreparedAArch64.pre Proof.Gcm.ghashPreparedAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghashP := by
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

/-- Zero memory has the eight prepared powers of the zero subkey. -/
theorem preparedPowersRepr_zero (p : Addr) : Proof.Gcm.PreparedPowers8Repr (fun _ => 0) p := by
  intro k hk
  have z : ∀ q : Addr, Spec.Gcm.blockAt (fun _ => 0) q = 0 := fun q => by
    simp [Spec.Gcm.blockAt, Spec.Aes.bytesAt, Spec.Gcm.ofBytes]
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  have hz : ∀ k, Spec.Gcm.hpow 0 (k + 1) = 0 := fun k => φ_inj (by
    rw [φ_hpow, φ_zero, zero_pow (Nat.succ_ne_zero k)])
  simp only [Spec.Gcm.ctxH, z, hz, w]
  constructor <;> decide

/-- A state satisfying `vg_ghash_prepared`'s precondition, with zero memory. -/
def satStateP : State := { Proof.Gcm.AArch64.satState with rd := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩] }

theorem ghashP_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghashP (Proof.Gcm.ghashPrepared8Contract AArch64.abi) :=
  Verified.of_correct ghashP_correct ghashP_ct
    { pre := by
        sig_implies_pre [Proof.Gcm.ghashPrepared8Contract, Proof.Gcm.ghashPrepared8Sig,
          Proof.Gcm.ghashPreparedAArch64, Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Proof.Gcm.ghashPrepared8Contract, Proof.Gcm.ghashPrepared8Sig,
          Proof.Gcm.ghashPreparedAArch64, Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Proof.Gcm.ghashPrepared8Contract, Proof.Gcm.ghashPrepared8Sig,
          Proof.Gcm.ghashPreparedAArch64, Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateP, by
        sig_pre [Proof.Gcm.ghashPrepared8Contract, Proof.Gcm.ghashPrepared8Sig, AArch64.abi, AArch64.argRegs,
          satStateP, Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact preparedPowersRepr_zero _
          | exact Region.disjoint_of_sep (by decide)⟩ }

end VG.Proof.Gcm.AArch64.Pmull

/-!
# GHASH with PMULL and the powers in their own buffer

`ghashW_verified` and `ghashS_verified` prove
`Impl.Gcm.AArch64.Pmull.ghashW` (`vg_ghash_with_powers_aes`) and
`Impl.Gcm.AArch64.Pmull.ghashS` (`vg_ghash_store_powers_aes`) against their
AArch64 contracts, `Proof.Gcm.ghashWithAArch64` and
`Proof.Gcm.ghashStoreAArch64`. Both set up all eight powers before the loops
(`Inv s₀ 8 0`, `loopsPart_ok`): `ghashW` loads them from `pw`, where
`x · H'ᵏ = Hᵏ` (`read_pwOff`), and `ghashS` computes them as `ghash` does,
then stores them after its epilogue, where `H'ᵏ = pp H k` (`tReg_pp`).
-/

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly pwOff)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## The loops, from all eight powers -/

/-- The loops of `ghashAll`, from all eight powers. -/
theorem loopsPart_ok {s₀ : State} (hp : Pm s₀) {s₁ : State} (hI₁ : Inv s₀ 8 0 s₁) :
    WP isa (.ite (.zero .x .x5) Impl.Gcm.AArch64.Pmull.tail
        (.seq (.loop (.block (Impl.Gcm.AArch64.Pmull.body 8)) (.nonzero .x .x5))
          Impl.Gcm.AArch64.Pmull.tail)) s₁ (Inv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun h => tail_ok hp (by simpa using h) hI₁) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s) ?_
    fun s₄ ⟨i, hi, hI₄⟩ => tail_ok hp hi hI₄)
  let Inv8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ Inv s₀ 8 i s
  have hstep : ∀ m s, Inv8 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 8)) s (fun s' =>
      (eval (.nonzero .x .x5) s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s') ∨
      (eval (.nonzero .x .x5) s' = some true ∧ ∃ m' < m, Inv8 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (body_ok hp (by decide) le_rfl le_rfl hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x5) s' = some (decide (8 ≤ nb s₀ - (i + 8))) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x5, hI'.x3,
        shr3_bne (show nb s₀ - (i + 8) < 2 ^ 64 by omega)]
    by_cases h8 : 8 ≤ nb s₀ - (i + 8)
    · exact .inr ⟨by rw [hev, decide_eq_true h8], nb s₀ - (i + 8), by omega, i + 8, rfl,
        by omega, hI'⟩
    · exact .inl ⟨by rw [hev, decide_eq_false h8], i + 8, by omega, hI'⟩
  exact WP.loop (M := isa) Inv8 hstep (nb s₀) s₁ ⟨0, rfl, by omega, hI₁⟩

/-- `ghashAll pro []`, from a prologue that sets up all eight powers. -/
theorem loopsAll_ok {s₀ : State} (hp : Pm s₀) {pro : List Instr}
    (hpro : WP isa (.block pro) s₀ (Inv s₀ 8 0)) :
    WP isa (Impl.Gcm.AArch64.Pmull.ghashAll pro []) s₀ fun s' =>
      Proof.Gcm.ghashAArch64.post s₀ s' := by
  refine WP.seq (WP.mono hpro fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (loopsPart_ok hp hI₁) fun s₂ hI₂ => ?_)
  rw [List.append_nil]
  exact epilogue_ok hp hI₂

/-! ## Reading the powers -/

theorem pm_of_with {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) : Pm s₀ := by
  obtain ⟨hrd, hwr, -, -, hyd, -⟩ := h
  exact ⟨⟨hR s₀, by simp [hrd], contains_offset (by decide) (by decide)⟩, by simp [hrd],
    by simp [hwr], hyd⟩

theorem pwOff_mod (k : Nat) : pwOff k % 16 = 0 := by
  unfold pwOff; split <;> omega

/-- The power `H'ᵏ` at `pw + pwOff k`, as `tReg k` holds it. -/
theorem read_pwOff {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) {k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ 8) :
    x * φ (s₀.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16) = φ (H₀ s₀) ^ k := by
  have hr := h.2.2.2.2.2.2.2.2.2
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · obtain ⟨hv, -⟩ := hr (j - 1) (by omega)
    have h1 : pwOff (2 * j) = 32 * (j - 1) := by
      simp only [pwOff, Nat.mul_mod_right, ↓reduceIte]; omega
    have h2 : 2 * j = 2 * (j - 1) + 2 := by omega
    have hv' : s₀.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff (2 * j))) 16 =
        Spec.Gcm.preparedPower (Spec.Gcm.hpow (H₀ s₀) (2 * j)) :=
      calc _ = s₀.mem.readW (s₀.gpr .x5 + BitVec.ofNat 64 (32 * (j - 1))) 128 := by
              rw [h1, Mem.readW]; rfl
        _ = _ := hv
        _ = _ := by rw [← h2]
    rw [hv', x_φ_preparedPower_hpow]
  · obtain ⟨-, hv⟩ := hr j (by omega)
    have h1 : pwOff (2 * j + 1) = 16 + 32 * j := by
      simp only [pwOff, show (2 * j + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]; omega
    have hv' : s₀.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff (2 * j + 1))) 16 =
        Spec.Gcm.preparedPower (Spec.Gcm.hpow (H₀ s₀) (2 * j + 1)) :=
      calc _ = s₀.mem.readW (s₀.gpr .x5 + BitVec.ofNat 64 (16 + 32 * j)) 128 := by
              rw [h1, Mem.readW]; rfl
        _ = _ := hv
    rw [hv', x_φ_preparedPower_hpow]

theorem loadPw_ok (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr)
    (s.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16) (hk : k ≤ 8) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPw k)) s fun s' =>
      s'.v (tReg k) = s.mem.read (s.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 ∧
      s'.v (sReg k) = ext8 (s'.v (tReg k)) (s'.v (tReg k)) ∧ VOnly [tReg k, sReg k] s s' := by
  have ho' : pwOff k < 4096 * 16 := by unfold pwOff; split <;> omega
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq (pwOff_mod k) ho' hin, ?_⟩
  refine WP.mono (swap_ok (sReg k) (tReg k) _) fun s' ⟨w, o⟩ => ?_
  have ts : tReg k ∉ [sReg k] := by
    simp only [List.mem_singleton]; exact tReg_ne_sReg _ _
  refine ⟨by rw [o.v _ ts]; simp only [v_setV, ite_true], by rw [w, o.v _ ts], ⟨fun r hr => ?_, o.gpr, o.mem,
    o.rd, o.wr, o.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [o.v r (by simp only [List.mem_singleton]; exact hr.2)]
  simp only [v_setV, hr.1, ite_false]

/-- The powers below `K` loaded, nothing else changed. -/
structure PW (s₀ : State) (K : Nat) (s : State) : Prop where
  t : ∀ k, 1 ≤ k → k ≤ K → x * φ (s.v (tReg k)) = φ (H₀ s₀) ^ k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = ext8 (s.v (tReg k)) (s.v (tReg k))
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `H'ᴷ⁺¹` loaded. -/
theorem loadPwI_ok {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) {K : Nat} (hK8 : K + 1 ≤ 8)
    {s : State} (hP : PW s₀ K s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPw (K + 1))) s (PW s₀ (K + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (pwOff (K + 1))) 16 := by
    rw [hP.rd, hP.wr, hP.gpr]
    refine ⟨⟨s₀.gpr .x5, 128⟩, by simp [h.1], contains_offset ?_ ?_⟩ <;>
      (unfold pwOff; split <;> omega)
  refine WP.mono (loadPw_ok (K + 1) s hin hK8) fun s' ⟨t, w, o⟩ => ?_
  have kv : ∀ r, r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r := fun r h1 h2 =>
    o.v r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  refine ⟨fun k hk hkK => ?_, fun k hk hkK => ?_, by rw [o.gpr, hP.gpr], by rw [o.mem, hP.mem],
    by rw [o.rd, hP.rd], by rw [o.wr, hP.wr]⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [t, hP.gpr, hP.mem]; exact read_pwOff h hk (by omega)
    · rw [kv _ (tReg_ne hk (by omega) (by omega) hK8 (by omega)) (tReg_ne_sReg _ _),
        hP.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · exact w
    · rw [kv _ (tReg_ne hk (by omega) (by omega) hK8 (by omega)) (tReg_ne_sReg _ _),
        kv _ (fun e => tReg_ne_sReg _ _ e.symm) (sReg_ne hk (by omega) (by omega) hK8 (by omega)),
        hP.sw k hk hkK']

theorem prologueW_ok {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologueW) s₀ (Inv s₀ 8 0) := by
  have hp := pm_of_with h
  simp only [Impl.Gcm.AArch64.Pmull.prologueW, List.append_assoc]
  have h₀ : PW s₀ 0 s₀ := ⟨fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega),
    rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 0) (by decide) h₀) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 1) (by decide) h₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 2) (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 3) (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 4) (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 5) (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 6) (by decide) h₆) fun s₇ h₇ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 7) (by decide) h₇) fun s₈ h₈ => ?_
  rw [WP.block_append_iff]
  have hcb : WP isa (.block ([.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)] : List Instr)) s₈ fun s₉ =>
      s₉.v C = ofVDwords poly poly ∧ (∀ r, r ≠ C → s₉.v r = s₈.v r) ∧
      (∀ r, r ≠ .x5 → s₉.gpr r = s₈.gpr r) ∧ s₉.mem = s₈.mem ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_x (show 16 * 3 < 64 by decide),
        exec_dup_d2]; rfl, ?_⟩
    refine ⟨by simp only [v_setV, ite_true, gpr_write_x]; decide, fun r hr => by simp only [v_setV, hr, ite_false,
      v_write], fun r hr => by simp only [gpr_setV, gpr_write_x, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono hcb fun s₉ ⟨c₉, v₉, g₉, m₉, rd₉, wr₉⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok Y .x1 0 s₉ rfl (by decide)
    (by rw [rd₉, wr₉, h₈.rd, h₈.wr, g₉ .x1 (by decide), h₈.gpr]
        exact ⟨yR s₀, List.mem_append_right _ hp.y_in, contains_offset (by decide) (by decide)⟩))
    fun s₁₀ ⟨l₁₀, o₁₀⟩ => ?_
  refine WP.mono (lsr_ok .x5 .x3 3 (by decide) s₁₀) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → s'.gpr r = s₀.gpr r := fun r h5 => by
    rw [fg r h5, o₁₀.gpr, g₉ r h5, h₈.gpr]
  have kv : ∀ r, r ≠ C → r ≠ Y → s'.v r = s₈.v r := fun r hc hy => by
    rw [fv, o₁₀.v _ (by simp only [List.mem_singleton]; exact hy), v₉ _ hc]
  refine ⟨Nat.zero_le _, by rw [fv, o₁₀.v C (by decide), c₉], fun k hk hk8 => ?_, fun k hk hk8 => ?_, ?_,
    by rw [g .x0 (by decide)], by rw [g .x1 (by decide)],
    by rw [g .x2 (by decide)]; simp [blkAddr], by rw [g .x3 (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₁₀.mem, m₉, h₈.mem],
    by rw [frd, o₁₀.rd, rd₉, h₈.rd], by rw [fwr, o₁₀.wr, wr₉, h₈.wr]⟩
  · rw [kv _ (ne_tReg (r := C) k).symm (ne_tReg (r := Y) k).symm]; exact h₈.t k hk hk8
  · rw [kv _ (ne_sReg (r := C) k).symm (ne_sReg (r := Y) k).symm,
      kv _ (ne_tReg (r := C) k).symm (ne_tReg (r := Y) k).symm]
    exact h₈.sw k hk hk8
  · rw [fv, l₁₀, m₉, h₈.mem, g₉ .x1 (by decide), h₈.gpr, add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

theorem correctW {s₀ : State} (hs : Proof.Gcm.ghashWithAArch64.pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghashW s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loopsAll_ok (pm_of_with hs) (prologueW_ok hs))
    (keeps_pres (by decide +kernel)) (by decide +kernel)) fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghashW_correct (s : State) (hs : Proof.Gcm.ghashWithAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghashW s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashWithAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correctW hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashW_ct : ConstantTime isa Proof.Gcm.ghashWithAArch64.pre Proof.Gcm.ghashWithAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghashW := by
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

/-- Zero memory has the eight prepared powers of the zero subkey. -/
theorem powers8Repr_zero (p : Addr) : Spec.Gcm.Powers8Repr (fun _ => 0) p 0 := by
  intro k hk
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  have hz : ∀ k, Spec.Gcm.hpow 0 (k + 1) = 0 := fun k => φ_inj (by
    rw [φ_hpow, φ_zero, zero_pow (Nat.succ_ne_zero k)])
  simp only [hz, w]
  constructor <;> decide

theorem blockAt_zero (q : Addr) : Spec.Gcm.blockAt (fun _ => 0) q = 0 := by
  simp [Spec.Gcm.blockAt, Spec.Aes.bytesAt, Spec.Gcm.ofBytes]

/-- A state satisfying `vg_ghash_with_powers`'s precondition, with zero memory. -/
def satStateW : State :=
  { Proof.Gcm.AArch64.satState with
    gpr := fun r => if r = .x5 then 0x6000 else Proof.Gcm.AArch64.satState.gpr r
    rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩, ⟨0x6000, 128⟩] }

theorem ghashW_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghashW (Proof.Gcm.ghashWithPowersContract AArch64.abi) :=
  Verified.of_correct ghashW_correct ghashW_ct
    { pre := by
        sig_implies_pre [Proof.Gcm.ghashWithPowersContract, Proof.Gcm.ghashWithPowersSig,
          Proof.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Proof.Gcm.ghashWithPowersContract, Proof.Gcm.ghashWithPowersSig,
          Proof.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Proof.Gcm.ghashWithPowersContract, Proof.Gcm.ghashWithPowersSig,
          Proof.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateW, by
        sig_pre [Proof.Gcm.ghashWithPowersContract, Proof.Gcm.ghashWithPowersSig, Proof.Gcm.ghashSig,
          Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs, satStateW,
          Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | (rw [blockAt_zero]; exact powers8Repr_zero _)
          | exact Region.disjoint_of_sep (by decide)⟩ }


/-! ## Storing the powers -/

theorem pm_of_store {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) : Pm s₀ := by
  obtain ⟨hrd, hwr, -, -, -, hyd, -⟩ := h
  exact ⟨⟨hR s₀, by simp [hrd], contains_offset (by decide) (by decide)⟩, by simp [hrd],
    by simp [hwr], hyd⟩

/-- `Pm` reads only `x0` to `x3` and the regions of its state. -/
theorem Pm.congr {s₀ s₁ : State} (h0 : s₁.gpr .x0 = s₀.gpr .x0) (h1 : s₁.gpr .x1 = s₀.gpr .x1)
    (h2 : s₁.gpr .x2 = s₀.gpr .x2) (h3 : s₁.gpr .x3 = s₀.gpr .x3) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hp : Pm s₀) : Pm s₁ := by
  obtain ⟨hh, hd, hy, hyd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hA, hrd, hwr, h0]; exact hh
  · simp only [dR, dp, nb, hrd, h2, h3]; exact hd
  · simp only [yR, yp, hwr, h1]; exact hy
  · simp only [yR, yp, dR, dp, nb, h1, h2, h3]; exact hyd

/-- `Inv` reads only `x0` to `x3`, the memory and the regions of its initial state. -/
theorem Inv.congr {s₀ s₁ : State} (h0 : s₁.gpr .x0 = s₀.gpr .x0) (h1 : s₁.gpr .x1 = s₀.gpr .x1)
    (h2 : s₁.gpr .x2 = s₀.gpr .x2) (h3 : s₁.gpr .x3 = s₀.gpr .x3) (hm : s₁.mem = s₀.mem)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) {K i : Nat} {s : State} (hI : Inv s₁ K i s) :
    Inv s₀ K i s := by
  have eH : H₀ s₁ = H₀ s₀ := by simp only [H₀, hA, h0, hm]
  have eY : ∀ j, Ys s₁ j = Ys s₀ j := fun j => by
    simp only [Ys, H₀, Y₀, hA, yp, dp, h0, h1, h2, hm]
  refine ⟨?_, hI.c, fun k hk hkK => ?_, hI.sw, ?_, ?_, ?_, ?_, ?_, hI.x5, ?_, ?_, ?_⟩
  · have := hI.le; simp only [nb, h3] at this ⊢; exact this
  · rw [← eH]; exact hI.t k hk hkK
  · rw [← eY]; exact hI.y
  · rw [hI.x0]; simp only [hA, h0]
  · rw [hI.x1]; simp only [yp, h1]
  · rw [hI.x2]; simp only [blkAddr, dp, h2]
  · rw [hI.x3]; simp only [nb, h3]
  · rw [hI.mem, hm]
  · rw [hI.rd, hrd]
  · rw [hI.wr, hwr]

theorem prologueS_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologueS) s₀ fun s =>
      Inv s₀ 8 0 s ∧ s.gpr .x8 = s₀.gpr .x5 := by
  have hp := pm_of_store h
  simp only [Impl.Gcm.AArch64.Pmull.prologueS, List.singleton_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addImm (show 0 < 4096 by decide) s₀, ?_⟩
  have g : ∀ r, r ≠ .x8 → (s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0)).gpr r = s₀.gpr r :=
    fun r hr => by simp only [gpr_write_x, hr, ite_false]
  have hp₁ := Pm.congr (s₁ := s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0))
    (g .x0 (by decide)) (g .x1 (by decide)) (g .x2 (by decide)) (g .x3 (by decide)) rfl rfl hp
  have hw : WP isa (.block (Impl.Gcm.AArch64.Pmull.prologueT ++ Impl.Gcm.AArch64.Pmull.powersS))
      (s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0)) (Inv (s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0)) 8 0) := by
    rw [WP.block_append_iff]
    exact WP.mono (prologueT_ok hp₁) fun _ hI => powersS_ok hI
  refine WP.mono (WP.gprs (rs := [.x8]) hw (by decide +kernel) (by decide +kernel))
    fun s ⟨hI, g8⟩ => ⟨Inv.congr (g .x0 (by decide)) (g .x1 (by decide)) (g .x2 (by decide))
      (g .x3 (by decide)) rfl rfl rfl hI, ?_⟩
  rw [g8 .x8 (by simp)]
  simp only [gpr_write_x, ite_true, add_ofNat_zero]

/-- With the eight powers computed, `H'ᵏ` is the prepared power of `Hᵏ`. -/
theorem tReg_pp {s₀ s : State} {i : Nat} (hI : Inv s₀ 8 i s) {k : Nat} (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    s.v (tReg k) = pp (H₀ s₀) k :=
  φ_inj (x_cancel (by rw [hI.t k hk1 hk8, x_φ_pp]))

/-- The offsets of distinct powers are 16 bytes apart at least. -/
theorem pwOff_sep : ∀ k < 9, ∀ j < 9, 1 ≤ k → 1 ≤ j → k ≠ j →
    pwOff k + 16 ≤ pwOff j ∨ pwOff j + 16 ≤ pwOff k := by
  intro k hk j hj h1 h2 hne
  unfold Impl.Gcm.AArch64.Pmull.pwOff
  split <;> split <;> omega

theorem pwOff_le : ∀ k < 9, pwOff k + 16 ≤ 128 := by
  intro k hk
  unfold Impl.Gcm.AArch64.Pmull.pwOff
  split <;> omega

/-- A byte outside a write is kept. -/
theorem write_byte_sep {m : Mem} {x b : Addr} {k : Nat} {v : BitVec (8 * k)} (h : Mem.Sep x 1 b k) :
    m.write b k v x = m x :=
  Mem.write_apply (h x (by simp))

/-- The bytes of `scratch` (`x4`) as they were in `s₀`. -/
def ScratchKept (s₀ s : State) : Prop :=
  ∀ x, Region.Contains ⟨s₀.gpr .x4, 256⟩ x 1 → s.mem x = s₀.mem x

/-- The powers below `K` stored at `pw`, the block at `y` kept, `scratch` untouched. -/
structure SW (s₀ : State) (yv : BitVec 128) (K : Nat) (s : State) : Prop where
  x8 : s.gpr .x8 = s₀.gpr .x5
  wr : s.wr = s₀.wr
  t : ∀ k, 1 ≤ k → k ≤ 8 → s.v (tReg k) = pp (H₀ s₀) k
  pw : ∀ k, 1 ≤ k → k ≤ K → s.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 = pp (H₀ s₀) k
  y : s.mem.read (yp s₀) 16 = yv
  sc : ScratchKept s₀ s

/-- `H'ᴷ⁺¹` stored. -/
theorem storeI_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) {yv : BitVec 128} {K : Nat}
    (hK : K + 1 ≤ 8) {s : State} (hS : SW s₀ yv K s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.storePw (K + 1))) s (SW s₀ yv (K + 1)) := by
  obtain ⟨-, hwr, -, -, -, -, -, hyp, -, -, hsp⟩ := h
  have hc : ∀ k, k ≤ 8 → Region.Contains ⟨s₀.gpr .x5, 128⟩ (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 :=
    fun k hk => contains_offset (by have := pwOff_le k (by omega); omega)
      (by have := pwOff_le k (by omega); omega)
  have hout : InRegions s.wr (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 := by
    rw [hS.wr, hwr, hS.x8]; exact ⟨⟨s₀.gpr .x5, 128⟩, by simp, hc (K + 1) hK⟩
  have ho' : pwOff (K + 1) < 4096 * 16 := by have := pwOff_le (K + 1) (by omega); omega
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (pwOff_mod (K + 1)) ho' hout, WP.block_nil ?_⟩
  refine ⟨hS.x8, hS.wr, hS.t, fun k hk hkK => ?_, ?_, fun x hx => ?_⟩
  · show (s.mem.write (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s.v (tReg (K + 1)))).read _ 16 = _
    rw [hS.x8]
    rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [read_write16, hS.t _ hk hK]
    · rw [Mem.read_write_sep (Offset.sep _ (pwOff_sep k (by omega) (K + 1) (by omega) hk (by omega)
          (by omega)) (by have := pwOff_le k (by omega); omega)
          (by have := pwOff_le (K + 1) (by omega); omega)) (by decide),
        hS.pw k hk hkK']
  · show (s.mem.write (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s.v (tReg (K + 1)))).read _ 16 = _
    have hcy : Region.Contains ⟨s₀.gpr .x1, 16⟩ (s₀.gpr .x1) 16 := by
      have := contains_offset (base := s₀.gpr .x1) (len := 16) (off := 0) (n := 16) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    rw [hS.x8, Mem.read_write_sep (Region.Disjoint.sep hyp hcy (hc (K + 1) hK)) (by decide), hS.y]
  · show (s.mem.write (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s.v (tReg (K + 1)))) x = _
    rw [hS.x8, write_byte_sep (Region.Disjoint.sep hsp hx (hc (K + 1) hK)), hS.sc x hx]

/-- The epilogue, then the eight powers stored. -/
theorem epiS_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) {s : State}
    (hI : Inv s₀ 8 (nb s₀) s) (h8 : s.gpr .x8 = s₀.gpr .x5) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.epilogue ++ Impl.Gcm.AArch64.Pmull.storesS)) s fun s' =>
      Proof.Gcm.ghashAArch64.post s₀ s' ∧ Spec.Gcm.Powers8Repr s'.mem (s₀.gpr .x5) (H₀ s₀) ∧
        ScratchKept s₀ s' := by
  have hp := pm_of_store h
  have hys := h.2.2.2.2.2.2.1
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
  have hsc0 : ScratchKept s₀ se := fun x hx => by
    have hcy : Region.Contains ⟨s₀.gpr .x1, 16⟩ (s₀.gpr .x1) 16 := by
      have := contains_offset (base := s₀.gpr .x1) (len := 16) (off := 0) (n := 16) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    simp only [se, mem_setV, gpr_setV, hI.x1, add_ofNat_zero]
    rw [write_byte_sep (Region.Disjoint.sep hys.symm hx hcy), hI.mem]
  have hS0 : SW s₀ (se.mem.read (yp s₀) 16) 0 se :=
    ⟨by simp only [se, gpr_setV, h8], by simp only [se, wr_setV, hI.wr],
      fun k hk1 hk8 => by
        simp only [se, v_setV, (ne_tReg (r := Y) k).symm, ite_false]; exact tReg_pp hI hk1 hk8,
      fun _ _ h => absurd h (by omega), rfl, hsc0⟩
  show WP isa (.block Impl.Gcm.AArch64.Pmull.storesS) se _
  simp only [Impl.Gcm.AArch64.Pmull.storesS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 0) (by decide) hS0) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 1) (by decide) h₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 2) (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 3) (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 4) (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 5) (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 6) (by decide) h₆) fun s₇ h₇ => ?_
  refine WP.mono (storeI_ok h (K := 7) (by decide) h₇) fun s' h' => ⟨?_, ?_, h'.sc⟩
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
    WP isa Impl.Gcm.AArch64.Pmull.ghashS s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashStoreAArch64.post s₀ s' ∧
        ScratchKept s₀ s' := by
  have hp := pm_of_store hs
  have hw : WP isa Impl.Gcm.AArch64.Pmull.ghashS s₀ fun s' =>
      Proof.Gcm.ghashStoreAArch64.post s₀ s' ∧ ScratchKept s₀ s' := by
    refine WP.seq (WP.mono (prologueS_ok hs) fun s₁ ⟨hI₁, h8₁⟩ => ?_)
    refine WP.seq (WP.mono (WP.gprs (rs := [.x8]) (loopsPart_ok hp hI₁) (by decide +kernel)
      (by decide +kernel)) fun s₂ ⟨hI₂, g₂⟩ => ?_)
    exact WP.mono (epiS_ok hs hI₂ (by rw [g₂ .x8 (by simp), h8₁])) fun _ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩
  exact WP.mono (WP.gprs (rs := preserved) hw (keeps_pres (by decide +kernel)) (by decide +kernel))
    fun _ ⟨⟨h₁, h₃⟩, h₂⟩ => ⟨h₂, h₁, h₃⟩

theorem ghashS_correct (s : State) (hs : Proof.Gcm.ghashStoreAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghashS s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashStoreAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂, -⟩ := correctS hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashS_ct : ConstantTime isa Proof.Gcm.ghashStoreAArch64.pre Proof.Gcm.ghashStoreAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghashS := by
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

/-- A state satisfying `vg_ghash_store_powers`'s precondition, with zero memory. -/
def satStateS : State :=
  { Proof.Gcm.AArch64.satState with
    gpr := fun r => if r = .x5 then 0x6000 else Proof.Gcm.AArch64.satState.gpr r
    wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩, ⟨0x6000, 128⟩] }

private theorem ghashS_implies :
    Proof.Gcm.ghashStoreAArch64.Implies (Spec.Gcm.ghashStorePowersContract AArch64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Proof.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Proof.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Proof.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateS, by
        sig_pre [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig, Proof.Gcm.ghashSig,
          Spec.Gcm.storePowersParam, AArch64.abi, AArch64.argRegs, satStateS,
          Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

theorem ghashS_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghashS (Spec.Gcm.ghashStorePowersContract AArch64.abi) :=
  Verified.of_correct ghashS_correct ghashS_ct ghashS_implies

/-- `vg_ghash_store_powers` never writes `scratch`: its caller need not wipe it. -/
theorem ghashS_written (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.Gcm.ghashStorePowersContract AArch64.abi).pre s)
    (he : Exec isa Impl.Gcm.AArch64.Pmull.ghashS s t s') :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Gcm.ghashStorePowersSig [("scratch", 0)] s s' := by
  obtain ⟨t', s'', he', -, -, hsc⟩ := correctS (ghashS_implies.pre s hs)
  obtain ⟨-, rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin, AArch64.abi, AArch64.argRegs, Abi.withConsts, Spec.Gcm.ghashStorePowersSig,
    Spec.Gcm.storePowersParam, Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  intro i hi
  have hi' : i < 256 := by simpa [Elem.size] using hi
  exact hsc _ (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Gcm.AArch64.Pmull
