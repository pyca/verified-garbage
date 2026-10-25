module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Steps
public import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on PPC64LE: absorbing a block, and the final reduction

As on AArch64 (`Proof/Poly1305/AArch64/Blocks.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Proof.Poly1305.Radix26
open VG.Spec.Poly1305 (P)

/-- The coefficient of `hi` in `dk`: `r(k-i)` or `5 r(k+5-i)`, for the limbs of `R`. -/
def cval (R k i : Nat) : Nat := if i ≤ k then lim R (k - i) else 5 * lim R (k + 5 - i)

/-- The coefficients stored in the state at `st`, for the clamped `R`. -/
def Coefs (m : Mem) (st : Addr) (R : Nat) : Prop :=
  ∀ k < 5, ∀ i < 5, (m.readW (st + BitVec.ofNat 64 (coef k i)) 32).toNat = cval R k i

/-- The coefficient words may be read. -/
def CoefIn (s : State) : Prop :=
  ∀ off, 72 ≤ off → off + 4 ≤ 108 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 off) 4

/-- `dk`, from the limbs of `h` in `s`. -/
def dform (s : State) (R k : Nat) : Nat :=
  v s .r7 * cval R k 0 + ((List.range 4).map fun i => v s (H.getD (i + 1) .r7) * cval R k (i + 1)).sum

theorem dreg_facts : ∀ k < 5, ∀ j < 5, j ≠ k → D.getD j .r12 ≠ D.getD k .r12 ∧ D.getD j .r12 ≠ .r18 := by
  decide

theorem hreg_facts : ∀ i < 5, H.getD i .r7 ∉ [Reg.r12, .r14, .r15, .r16, .r17, .r18] := by decide +kernel

theorem dreg_mem : ∀ n < 5, D.getD n .r12 ∈ [Reg.r12, .r14, .r15, .r16, .r17, .r18] := by decide +kernel

theorem prods_ok (s : State) (R : Nat) (hco : Coefs s.mem (s.gpr .r3) R) (hc : CoefIn s) :
    ∀ n ≤ 5, WP isa (.block ((List.range n).flatMap dsum)) s fun s' =>
      (∀ k < n, v s' (D.getD k .r12) = dform s R k % 2 ^ 64) ∧
      Keeps [.r12, .r14, .r15, .r16, .r17, .r18] s s' := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun k hk => absurd hk (by omega_using [hk]), Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hn])) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have x0₁ : s₁.gpr .r3 = s.gpr .r3 := k₁.gpr'
    have hc₁ : CoefIn s₁ := fun off h₁ h₂ => by
      rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact hc off h₁ h₂
    refine WP.mono (dsum_ok s₁ (by omega_using [hn]) hc₁) fun s₂ ⟨e₂, k₂⟩ => ⟨fun k hk => ?_, ?_⟩
    · have hH : ∀ i < 5, v s₁ (H.getD i .r7) = v s (H.getD i .r7) := fun i hi => by
        simp only [v]
        rw [k₁.1 _ (hreg_facts i hi)]
      have hW : ∀ i < 5, word s₁ (coef n i) = cval R n i := fun i hi => by
        simp only [word, x0₁, k₁.2.1]; exact hco n (by omega_using [hn]) i hi
      by_cases hkn : k = n
      · subst hkn
        have h0 : v s₁ .r7 = v s .r7 := hH 0 (by decide)
        have hs : ((List.range 4).map fun i => v s₁ (H.getD (i + 1) .r7) * word s₁ (coef k (i + 1))) =
            ((List.range 4).map fun i => v s (H.getD (i + 1) .r7) * cval R k (i + 1)) := by
          refine List.map_congr_left fun i hi => ?_
          have hi := List.mem_range.mp hi
          rw [hW (i + 1) (by omega_using [hi]), hH (i + 1) (by omega_using [hi])]
        rw [e₂, hW 0 (by decide), h0, hs, dform]
      · obtain ⟨g1, g2⟩ := dreg_facts n (by omega_using [hn]) k (by omega_using [hn, hk]) hkn
        rw [show v s₂ (D.getD k .r12) = v s₁ (D.getD k .r12) by
          simp only [v]; rw [k₂.1 _ (not_mem2 g2 g1)]]
        exact e₁ k (by omega_using [hk, hkn])
    · refine (k₁.trans k₂).mono fun r hr => ?_
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]
        · exact dreg_mem n (by omega_using [hn])

section
variable (s : State) (R : Nat)
theorem dform0 : dform s R 0 = v s .r7 * lim R 0 + (v s .r8 * (5 * lim R 4) +
    (v s .r9 * (5 * lim R 3) + (v s .r10 * (5 * lim R 2) + (v s .r11 * (5 * lim R 1) + 0)))) := rfl
theorem dform1 : dform s R 1 = v s .r7 * lim R 1 + (v s .r8 * lim R 0 +
    (v s .r9 * (5 * lim R 4) + (v s .r10 * (5 * lim R 3) + (v s .r11 * (5 * lim R 2) + 0)))) := rfl
theorem dform2 : dform s R 2 = v s .r7 * lim R 2 + (v s .r8 * lim R 1 +
    (v s .r9 * lim R 0 + (v s .r10 * (5 * lim R 4) + (v s .r11 * (5 * lim R 3) + 0)))) := rfl
theorem dform3 : dform s R 3 = v s .r7 * lim R 3 + (v s .r8 * lim R 2 +
    (v s .r9 * lim R 1 + (v s .r10 * lim R 0 + (v s .r11 * (5 * lim R 4) + 0)))) := rfl
theorem dform4 : dform s R 4 = v s .r7 * lim R 4 + (v s .r8 * lim R 3 +
    (v s .r9 * lim R 2 + (v s .r10 * lim R 1 + (v s .r11 * lim R 0 + 0)))) := rfl
end

theorem products_ok (s : State) (R : Nat) (hco : Coefs s.mem (s.gpr .r3) R) (hc : CoefIn s) :
    WP isa (.block products) s fun s' =>
      v s' .r12 = dform s R 0 % 2 ^ 64 ∧ v s' .r14 = dform s R 1 % 2 ^ 64 ∧
      v s' .r15 = dform s R 2 % 2 ^ 64 ∧ v s' .r16 = dform s R 3 % 2 ^ 64 ∧
      v s' .r17 = dform s R 4 % 2 ^ 64 ∧ Keeps [.r12, .r14, .r15, .r16, .r17, .r18] s s' :=
  WP.mono (prods_ok s R hco hc 5 (Nat.le_refl _)) fun _ ⟨e, k⟩ =>
    ⟨e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), k⟩

/-- `h += 2¹²⁸` if `pad`. -/
theorem padOpt_ok (s : State) (pad : Bool) :
    WP isa (.block (if pad then padBit else [])) s fun s' =>
      v s' .r11 = (v s .r11 + 2 ^ 24 * pad.toNat) % 2 ^ 64 ∧ Keeps [.r11, .r0] s s' := by
  cases pad
  · show WP isa (.block []) s _
    refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, v]
    exact (Nat.mod_eq_of_lt (s.gpr .r11).isLt).symm
  · show WP isa (.block padBit) s _
    exact WP.mono (padBit_ok s) fun s' ⟨e, k⟩ => ⟨by rw [e]; rfl, k⟩

/-- The limbs of `h` between blocks. -/
def Bounds (s : State) : Prop :=
  v s .r7 < 2 ^ 26 ∧ v s .r8 < 2 ^ 27 ∧ v s .r9 < 2 ^ 26 ∧ v s .r10 < 2 ^ 26 ∧ v s .r11 < 2 ^ 26

/-- `h`, from its limbs. -/
abbrev hv (s : State) : Nat := val5 (v s .r7) (v s .r8) (v s .r9) (v s .r10) (v s .r11)

/-- The registers `absorb` writes. -/
abbrev absorbRegs : List Reg :=
  [.r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r0]

/-- The 64-bit word at `p + d`, as a number. -/
abbrev w64 (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

theorem absorb_eq (pad : Bool) : absorb pad = load2 .r4 0 ++ (split ++ (addLimbs ++
    ((if pad then padBit else []) ++ (products ++ carry)))) := by
  simp only [absorb, addBlock, List.append_assoc]

/-- Absorbing the block at `r4`: from `h` within `Bounds`, the new `h` is
congruent to `(h + m + pad · 2¹²⁸) R` modulo `p`, and within `Bounds`. -/
theorem absorb_ok (s : State) (pad : Bool) {R : Nat} (hR : R < 2 ^ 128) (hm : s.gpr .r20 = M26)
    (hco : Coefs s.mem (s.gpr .r3) R) (hc : CoefIn s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (0 + 8)) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (w64 s.mem (s.gpr .r4) 0 + 2 ^ 64 * w64 s.mem (s.gpr .r4) 8 +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  rw [absorb_eq]
  refine WP.block_append (WP.mono (load2_ok s (by decide) (by decide) (by decide) (by decide) h0 h8)
    fun s₁ ⟨l1, l2, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₁ (by rw [k₁.gpr']; exact hm))
    fun s₂ ⟨m0, m1, m2, m3, m4, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (addLimbs_ok s₂) fun s₃ ⟨a0, a1, a2, a3, a4, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (padOpt_ok s₃ pad) fun s₄ ⟨p4, k₄⟩ => ?_)
  have k₁₄ := ((k₁.trans k₂).trans k₃).trans k₄
  have x0₄ : s₄.gpr .r3 = s.gpr .r3 := k₁₄.gpr'
  refine WP.block_append (WP.mono (products_ok s₄ R (by rw [k₁₄.2.1, x0₄]; exact hco)
    (fun off h₁ h₂ => by rw [k₁₄.2.2.1, k₁₄.2.2.2, x0₄]; exact hc off h₁ h₂))
    fun s₅ ⟨d0, d1, d2, d3, d4, k₅⟩ => ?_)
  refine WP.mono (carry_ok s₅ (by rw [(k₁₄.trans k₅).gpr']; exact hm)) fun s₆ ⟨hcar, k₆⟩ => ?_
  refine ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_, (((k₁₄.trans k₅).trans k₆).mono (by decide))⟩
  -- The block, as a number `N`, and its limbs.
  have hN := val5_lim (v s₁ .r18 + 2 ^ 64 * v s₁ .r19)
  have hNlt : v s₁ .r18 + 2 ^ 64 * v s₁ .r19 < 2 ^ 128 := by
    have := (s₁.gpr .r18).isLt; have := (s₁.gpr .r19).isLt; simp only [v]; omega_arith
  have n0 := lim_lt (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) (j := 0) (by decide)
  have n1 := lim_lt (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) (j := 1) (by decide)
  have n2 := lim_lt (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) (j := 2) (by decide)
  have n3 := lim_lt (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) (j := 3) (by decide)
  have n4 := lim4_lt hNlt
  -- `h + m` in `s₄`.
  have h4₂ : ∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], v s₂ r = v s r := fun r hr => by
    simp only [v]; rw [k₂.1 r (by revert hr; decide +revert), k₁.1 r (by revert hr; decide +revert)]
  have hp : pad.toNat ≤ 1 := by cases pad <;> decide
  rw [h4₂ .r7 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), m0] at a0; rw [h4₂ .r8 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), m1] at a1
  rw [h4₂ .r9 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), m2] at a2; rw [h4₂ .r10 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), m3] at a3
  rw [h4₂ .r11 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]), m4] at a4
  have e0 : v s₄ .r7 = v s .r7 + lim (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) 0 := by
    rw [show v s₄ .r7 = v s₃ .r7 by simp only [v]; rw [k₄.gpr'], a0]; omega_using [b0, n0]
  have e1 : v s₄ .r8 = v s .r8 + lim (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) 1 := by
    rw [show v s₄ .r8 = v s₃ .r8 by simp only [v]; rw [k₄.gpr'], a1]; omega_using [b1, n1]
  have e2 : v s₄ .r9 = v s .r9 + lim (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) 2 := by
    rw [show v s₄ .r9 = v s₃ .r9 by simp only [v]; rw [k₄.gpr'], a2]; omega_using [b2, n2]
  have e3 : v s₄ .r10 = v s .r10 + lim (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) 3 := by
    rw [show v s₄ .r10 = v s₃ .r10 by simp only [v]; rw [k₄.gpr'], a3]; omega_using [b3, n3]
  have e4 : v s₄ .r11 = v s .r11 + lim (v s₁ .r18 + 2 ^ 64 * v s₁ .r19) 4 + 2 ^ 24 * pad.toNat := by
    rw [p4, a4]; omega_using [b4, n4, hp]
  -- The sums of products.
  obtain ⟨q0, q1, q2, q3, q4, hq⟩ := dsum_arith (a0 := v s₄ .r7) (a1 := v s₄ .r8) (a2 := v s₄ .r9)
    (a3 := v s₄ .r10) (a4 := v s₄ .r11) (by omega_using [e0, b0, n0]) (by omega_using [e1, b1, n1])
    (by omega_using [e2, b2, n2]) (by omega_using [e3, b3, n3]) (by omega_using [e4, b4, n4, hp]) hR
  rw [dform0] at d0; rw [dform1] at d1; rw [dform2] at d2; rw [dform3] at d3; rw [dform4] at d4
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q0 (by decide))] at d0
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q1 (by decide))] at d1
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q2 (by decide))] at d2
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q3 (by decide))] at d3
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q4 (by decide))] at d4
  obtain ⟨hv₆, c0, c1, c2, c3, c4⟩ := hcar (by rw [d0]; exact q0) (by rw [d1]; exact q1)
    (by rw [d2]; exact q2) (by rw [d3]; exact q3) (by rw [d4]; exact q4)
  refine ⟨?_, c0, c1, c2, c3, c4⟩
  rw [hv, hv₆, d0, d1, d2, d3, d4, hq]
  have hw : w64 s.mem (s.gpr .r4) 0 + 2 ^ 64 * w64 s.mem (s.gpr .r4) 8 =
      v s₁ .r18 + 2 ^ 64 * v s₁ .r19 := by
    simp only [v, w64, l1, l2]
  have ha : val5 (v s₄ .r7) (v s₄ .r8) (v s₄ .r9) (v s₄ .r10) (v s₄ .r11) =
      hv s + (w64 s.mem (s.gpr .r4) 0 + 2 ^ 64 * w64 s.mem (s.gpr .r4) 8 + 2 ^ 128 * pad.toNat) := by
    rw [hw, ← hN]
    simp only [hv, val5, e0, e1, e2, e3, e4]
    omega_using []
  rw [ha]

/-! ## The final reduction -/

/-- `h` reduced fully, into normalized limbs. -/
theorem reduce_ok (s : State) (hm : s.gpr .r20 = M26) :
    WP isa (.block reduce) s fun s' =>
      (Bounds s → Norm (hv s) (v s' .r7) (v s' .r8) (v s' .r9) (v s' .r10) (v s' .r11)) ∧
      Keeps [.r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19] s s' := by
  rw [reduce]
  refine WP.block_append (WP.mono (reduceA_ok s hm) fun s₁ ⟨h₁, k₁⟩ => ?_)
  refine WP.mono (select_ok s₁) fun s₂ ⟨c4, c5, c6, c7, c8, k₂⟩ => ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_,
    (k₁.trans k₂).mono (by decide)⟩
  rcases h₁ b0 b1 b2 b3 b4 with ⟨hz, hn⟩ | ⟨ho, hn⟩
  · have hz := eq_zero_of_toNat hz
    simp only [v, c4, c5, c6, c7, c8, hz, select_zero]
    exact hn
  · have ho := eq_ones_of_toNat ho
    simp only [v, c4, c5, c6, c7, c8, ho, select_ones]
    exact hn

end VG.Proof.Poly1305.PPC64LE
