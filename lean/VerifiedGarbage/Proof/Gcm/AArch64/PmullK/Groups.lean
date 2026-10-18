module

public import VerifiedGarbage.Proof.Gcm.AArch64.PmullK.Ops
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Impl.Gcm.AArch64.PmullK
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# GHASH with PMULL and EOR3: the instruction groups

What each group of instructions of `Impl.Gcm.AArch64.PmullK` does to the
state, as bits (`Arith.lean` gives their classes): a block's three products
(`kprod_ok`), a pair of blocks with them added (`pair_ok`), the reduction of
`fix` of the product (`reduceK_ok`), and the keys (`keyPair_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.PmullK

open VG VG.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Impl.Gcm.AArch64.PmullK (P A₂ B₂ P₂ kReg kHi keyOf)

theorem exec_pmull (hi : Bool) (d n m : VReg) (s : State) :
    exec (.vop (.pmull hi d n m)) s =
      some (s.setV d (polyMul (vdword (s.v n) (if hi then 1 else 0))
        (vdword (s.v m) (if hi then 1 else 0)))) := rfl

theorem exec_eor3 (d n m a : VReg) (s : State) :
    exec (.vop (.eor3 d n m a)) s = some (s.setV d (s.v n ^^^ s.v m ^^^ s.v a)) := rfl

/-- The lane of `H'ᵏ`'s key. -/
def lane (k : Nat) : Nat := if kHi k then 1 else 0

/-- `H'ᵏ`'s key, as `keys` stores it. -/
def keyV (s : State) (k : Nat) : BitVec 64 := vdword (s.v (keyOf k)) (lane k)

theorem vdword_ext8_xor (a : BitVec 128) (e : Nat) (he : e < 2) :
    vdword (ext8 a a ^^^ a) e = vdword a 0 ^^^ vdword a 1 := by
  rw [vdword_xor]
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · rw [vdword_ext8_0, BitVec.xor_comm]
  · rw [vdword_ext8_1]

/-- The products of the block in `a` and `H'ᵏ`. -/
theorem kprod_ok (a b p : VReg) (k : Nat) (s : State) (hab : a ≠ b) (hap : a ≠ p) (hbp : b ≠ p)
    (hsb : sReg k ≠ b) (hsp : sReg k ≠ p) (hka : keyOf k ≠ a)
    (hkb : keyOf k ≠ b) (hkp : keyOf k ≠ p) :
    WP isa (.block (Impl.Gcm.AArch64.PmullK.kprod a b p k)) s fun s' =>
      s'.v p = polyMul (vdword (s.v a) 0) (vdword (s.v (sReg k)) 0) ∧
      s'.v a = polyMul (vdword (s.v a) 1) (vdword (s.v (sReg k)) 1) ∧
      s'.v b = polyMul (vdword (s.v a) 0 ^^^ vdword (s.v a) 1) (keyV s k) ∧
      VOnly [a, b, p] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.PmullK.kprod, runBlock_cons, runStep_some, runBlock_nil, exec_ext8,
    exec_eor, exec_pmull, Option.some.injEq, exists_eq_left', v_setV, ite_true, hab, hap, hbp,
    hab.symm, hap.symm, hbp.symm, hsb, hsp, hka, hkb, hkp, ite_false, Bool.false_eq_true]
  refine ⟨trivial, trivial, ?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · rw [vdword_ext8_xor _ _ (by split <;> omega)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A pair's products added, the first: their sums. -/
theorem addFirst_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.addFirst) s fun s' =>
      prod s' = ⟨s.v A ^^^ s.v A₂, s.v T ^^^ s.v B₂, s.v P ^^^ s.v P₂⟩ ∧ VOnly [HI, LO, MID] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.PmullK.addFirst, runBlock_cons, runStep_some, runBlock_nil, exec_eor,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A pair's products added. -/
theorem addNext_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.addNext) s fun s' =>
      prod s' = ⟨s.v LO ^^^ s.v A ^^^ s.v A₂, s.v MID ^^^ s.v T ^^^ s.v B₂,
        s.v HI ^^^ s.v P ^^^ s.v P₂⟩ ∧ VOnly [HI, LO, MID] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.PmullK.addNext, runBlock_cons, runStep_some, runBlock_nil, exec_eor3,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, v_setV, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `reduceK`: `vg_ghash_aes`'s `reduce` of `fix` of the product, into `Y`. -/
theorem reduceK_ok (s : State) (hc : s.v C = ofVDwords poly poly) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.reduceK) s fun s' =>
      s'.v Y = reduce (fix (prod s)) ∧ VOnly [T, P, MID, HI, Y] s s' := by
  have hc0 : vdword (ofVDwords poly poly) 0 = poly := vdword_append_0 _ _
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.PmullK.reduceK, runBlock_cons, runStep_some, runBlock_nil,
    exec_pmull0, exec_ext8, exec_eor3, Option.some.injEq, exists_eq_left', v_setV, ite_true,
    ite_false, reduceCtorEq, hc]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [hc0, reduce, fix, prod]
    have e : s.v MID ^^^ (ext8 (s.v LO) (s.v LO) ^^^ s.v LO ^^^ s.v HI) ^^^
        polyMul (vdword (s.v LO) 0) poly =
        s.v MID ^^^ s.v HI ^^^ s.v LO ^^^ ext8 (s.v LO) (s.v LO) ^^^ polyMul (vdword (s.v LO) 0) poly := by
      ac_rfl
    rw [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The registers -/

theorem sReg_ne_A (k : Nat) : sReg k ≠ A := by unfold sReg; split <;> decide
theorem sReg_ne_T (k : Nat) : sReg k ≠ T := by unfold sReg; split <;> decide
theorem sReg_ne_P (k : Nat) : sReg k ≠ P := by unfold sReg; split <;> decide
theorem sReg_ne_A₂ (k : Nat) : sReg k ≠ A₂ := by unfold sReg; split <;> decide
theorem sReg_ne_B₂ (k : Nat) : sReg k ≠ B₂ := by unfold sReg; split <;> decide
theorem sReg_ne_P₂ (k : Nat) : sReg k ≠ P₂ := by unfold sReg; split <;> decide
theorem keyOf_ne_A (k : Nat) : keyOf k ≠ A := by unfold keyOf kReg; split <;> decide
theorem keyOf_ne_T (k : Nat) : keyOf k ≠ T := by unfold keyOf kReg; split <;> decide
theorem keyOf_ne_P (k : Nat) : keyOf k ≠ P := by unfold keyOf kReg; split <;> decide
theorem keyOf_ne_A₂ (k : Nat) : keyOf k ≠ A₂ := by unfold keyOf kReg; split <;> decide
theorem keyOf_ne_B₂ (k : Nat) : keyOf k ≠ B₂ := by unfold keyOf kReg; split <;> decide
theorem keyOf_ne_P₂ (k : Nat) : keyOf k ≠ P₂ := by unfold keyOf kReg; split <;> decide

/-- The registers a pair of blocks writes. -/
abbrev pairRegs : List VReg := [A, T, P, A₂, B₂, P₂]

theorem sReg_nmem_pair (k : Nat) : sReg k ∉ pairRegs := by unfold sReg; split <;> decide
theorem keyOf_nmem_pair (k : Nat) : keyOf k ∉ pairRegs := by unfold keyOf kReg; split <;> decide

/-! ## A pair of blocks -/

/-- `Y` added to `A₂` if `y`. -/
theorem addY_ok (y : Bool) (s : State) :
    WP isa (.block (if y then [.vop (.logic .eor A₂ A₂ Y)] else [])) s fun s' =>
      s'.v A₂ = s.v A₂ ^^^ (if y then s.v Y else 0) ∧ VOnly [A₂] s s' := by
  cases y
  · exact WP.block_nil ⟨by simp,
      VOnly.refl _ _⟩
  · exact WP.mono (eor_ok A₂ A₂ Y s) fun s' ⟨h, o⟩ => ⟨by rw [h]; rfl, o⟩

/-- The block at `x2 + off`, as loaded. -/
def blockV (s : State) (off : Nat) : BitVec 128 :=
  VRevOp.eval .rev64b (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 off) 16)

/-- Blocks `j₁` and `j₂` and their products by `H'ᵏ¹` and `H'ᵏ²`, `Y` added to
the second if `y`. -/
theorem kpair_ok (j₁ k₁ j₂ k₂ : Nat) (y : Bool) (s : State) (hj₁ : 16 * j₁ < 4096 * 16)
    (hj₂ : 16 * j₂ < 4096 * 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * j₁)) 16)
    (hin₂ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * j₂)) 16) :
    WP isa (.block (Impl.Gcm.AArch64.PmullK.kpair j₁ k₁ j₂ k₂ y)) s fun s' =>
      s'.v P = polyMul (vdword (blockV s (16 * j₁)) 0) (vdword (s.v (sReg k₁)) 0) ∧
      s'.v A = polyMul (vdword (blockV s (16 * j₁)) 1) (vdword (s.v (sReg k₁)) 1) ∧
      s'.v T = polyMul (vdword (blockV s (16 * j₁)) 0 ^^^ vdword (blockV s (16 * j₁)) 1) (keyV s k₁) ∧
      s'.v P₂ = polyMul (vdword (blockV s (16 * j₂) ^^^ (if y then s.v Y else 0)) 0)
        (vdword (s.v (sReg k₂)) 0) ∧
      s'.v A₂ = polyMul (vdword (blockV s (16 * j₂) ^^^ (if y then s.v Y else 0)) 1)
        (vdword (s.v (sReg k₂)) 1) ∧
      s'.v B₂ = polyMul (vdword (blockV s (16 * j₂) ^^^ (if y then s.v Y else 0)) 0 ^^^
        vdword (blockV s (16 * j₂) ^^^ (if y then s.v Y else 0)) 1) (keyV s k₂) ∧
      VOnly pairRegs s s' := by
  simp only [Impl.Gcm.AArch64.PmullK.kpair, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x2 (16 * j₁) s (Nat.mul_mod_right 16 _) hj₁ hin₁)
    fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (kprod_ok A T P k₁ s₁ (by decide) (by decide) (by decide) (sReg_ne_T _)
    (sReg_ne_P _) (keyOf_ne_A _) (keyOf_ne_T _) (keyOf_ne_P _)) fun s₂ ⟨p₂, a₂, t₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  have o₁₂ := o₁.trans o₂
  refine WP.mono (loadRev_ok A₂ .x2 (16 * j₂) s₂ (Nat.mul_mod_right 16 _) hj₂
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr]; exact hin₂)) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addY_ok y s₃) fun s₄ ⟨e₄, o₄⟩ => ?_
  refine WP.mono (kprod_ok A₂ B₂ P₂ k₂ s₄ (by decide) (by decide) (by decide) (sReg_ne_B₂ _)
    (sReg_ne_P₂ _) (keyOf_ne_A₂ _) (keyOf_ne_B₂ _) (keyOf_ne_P₂ _))
    fun s' ⟨p₅, a₅, b₅, o₅⟩ => ?_
  have o₃₄ := o₃.trans o₄
  have o : VOnly pairRegs s s' := (o₁₂.trans (o₃₄.trans o₅)).weaken
  have fv₁ : ∀ r, r ∉ pairRegs → s₁.v r = s.v r := fun r hr => (o₁.weaken (rs' := pairRegs)).v r hr
  have fv₄ : ∀ r, r ∉ pairRegs → s₄.v r = s.v r := fun r hr =>
    ((o₁₂.trans o₃₄).weaken (rs' := pairRegs)).v r hr
  have hY : s₃.v Y = s.v Y := ((o₁₂.trans o₃).weaken (rs' := pairRegs)).v Y (by decide)
  have hA₂ : s₄.v A₂ = blockV s (16 * j₂) ^^^ (if y then s.v Y else 0) := by
    rw [e₄, l₃, hY, o₁₂.mem, o₁₂.gpr]; rfl
  have o₃₅ : VOnly [A₂, B₂, P₂] s₂ s' := (o₃₄.trans o₅).weaken
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, o⟩
  · rw [o₃₅.v P (by decide), p₂, l₁, fv₁ _ (sReg_nmem_pair _)]; rfl
  · rw [o₃₅.v A (by decide), a₂, l₁, fv₁ _ (sReg_nmem_pair _)]; rfl
  · rw [o₃₅.v T (by decide), t₂, l₁]
    simp only [keyV, fv₁ (keyOf k₁) (keyOf_nmem_pair k₁)]; rfl
  · rw [p₅, hA₂, fv₄ _ (sReg_nmem_pair _)]
  · rw [a₅, hA₂, fv₄ _ (sReg_nmem_pair _)]
  · rw [b₅, hA₂]
    simp only [keyV, fv₄ (keyOf k₂) (keyOf_nmem_pair k₂)]

/-! ## One block -/

theorem kHi_one : kHi 1 = false := rfl
theorem keyOf_one : keyOf 1 = .v20 := rfl

/-- `body1K`'s products of the block in `A` and `H'`, into `hi`, `lo` and `mid`. -/
theorem single_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.single) s fun s' =>
      prod s' = kadd Prod.zero (s.v A) (s.v (sReg 1)) (keyV s 1) ∧ VOnly [MID, HI, LO] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.PmullK.single, kHi_one, keyOf_one, sReg, runBlock_cons, runStep_some, runBlock_nil, exec_ext8, exec_eor,
    exec_pmull0, exec_pmull1, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · simp only [prod, kadd, Prod.zero, keyV, lane, kHi_one, keyOf_one, v_setV, ite_true, ite_false,
      reduceCtorEq, BitVec.ofNat_eq_ofNat, BitVec.zero_xor, Bool.false_eq_true]
    rw [vdword_ext8_xor _ 0 (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-! ## The keys -/

/-- The key in the low lane of `s ⊕ t`'s halves swapped, for `s` the halves
of `t` swapped. -/
theorem lane_lo {sv tv : BitVec 128} (h : sv = ext8 tv tv) : vdword (sv ^^^ tv) 1 = kkey sv := by
  rw [h, kkey, vdword_xor, vdword_ext8_0, vdword_ext8_1, BitVec.xor_comm]

/-- The key in the high lane. -/
theorem lane_hi {sv tv : BitVec 128} (h : sv = ext8 tv tv) : vdword (sv ^^^ tv) 0 = kkey sv := by
  rw [h, kkey, vdword_xor, vdword_ext8_0, vdword_ext8_1]

theorem keyOf_odd (j : Nat) : keyOf (2 * j + 1) = kReg j := by
  unfold keyOf; congr 1; omega

theorem keyOf_even (j : Nat) : keyOf (2 * j + 2) = kReg j := by
  unfold keyOf; congr 1; omega

theorem lane_odd (j : Nat) : lane (2 * j + 1) = 0 := by
  unfold lane kHi; rw [show (2 * j + 1 - 1) % 2 = 0 by omega]; rfl

theorem lane_even (j : Nat) : lane (2 * j + 2) = 1 := by
  unfold lane kHi; rw [show (2 * j + 2 - 1) % 2 = 1 by omega]; rfl

/-- The registers `keys` writes. -/
abbrev keyRegs : List VReg := [P, A, .v20, .v21, .v22, .v23]

theorem keys_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.keys) s fun s' =>
      (∀ j, j < 4 → s'.v (kReg j) =
        ext8 (s.v (sReg (2 * j + 1)) ^^^ s.v (tReg (2 * j + 1)))
          (s.v (sReg (2 * j + 2)) ^^^ s.v (tReg (2 * j + 2)))) ∧
      VOnly keyRegs s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.PmullK.keys, Impl.Gcm.AArch64.PmullK.keyPair, List.cons_append,
    List.nil_append, sReg, tReg, kReg, runBlock_cons, runStep_some, runBlock_nil, exec_eor,
    exec_ext8, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      simp only [v_setV, ite_true, ite_false, reduceCtorEq, Nat.mul_zero,
        Nat.zero_add, Nat.reduceMul, Nat.reduceAdd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- With the powers in `tReg` and their halves swapped in `sReg`, the keys of
all eight. -/
theorem keys_key {s s' : State}
    (hsw : ∀ k, 1 ≤ k → k ≤ 8 → s.v (sReg k) = ext8 (s.v (tReg k)) (s.v (tReg k)))
    (hk : ∀ j, j < 4 → s'.v (kReg j) =
        ext8 (s.v (sReg (2 * j + 1)) ^^^ s.v (tReg (2 * j + 1)))
          (s.v (sReg (2 * j + 2)) ^^^ s.v (tReg (2 * j + 2))))
    (hs : ∀ k, s'.v (sReg k) = s.v (sReg k)) :
    ∀ k, 1 ≤ k → k ≤ 8 → keyV s' k = kkey (s'.v (sReg k)) := by
  intro k hk1 hk8
  rw [hs]
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j, j < 4 ∧ (k = 2 * j + 1 ∨ k = 2 * j + 2) :=
    ⟨(k - 1) / 2, by omega, by omega⟩
  · rw [keyV, keyOf_odd, lane_odd, hk j hj, vdword_ext8_0]
    exact lane_lo (hsw _ (by omega) (by omega))
  · rw [keyV, keyOf_even, lane_even, hk j hj, vdword_ext8_1]
    exact lane_hi (hsw _ (by omega) (by omega))

theorem key1_ok (s : State)
    (hsw : s.v (sReg 1) = ext8 (s.v (tReg 1)) (s.v (tReg 1))) :
    WP isa (.block Impl.Gcm.AArch64.PmullK.key1) s fun s' =>
      keyV s' 1 = kkey (s'.v (sReg 1)) ∧ VOnly [.v20] s s' := by
  refine WP.mono (eor_ok (kReg 0) (sReg 1) (tReg 1) s) fun s' ⟨h, o⟩ => ⟨?_, o⟩
  rw [keyV, keyOf, lane, h, o.v (sReg 1) (by decide)]
  exact lane_hi hsw

end VG.Proof.Gcm.AArch64.PmullK
