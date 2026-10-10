import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath

/-! ## `InvMaskCopy` -/

section

/-! # Copying a multiword signed correction through a mask -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem maskCopy_ok {size : Nat} (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    Scr s base size → s.gpr .ecx = (if c then BitVec.allOnes 32 else 0) →
    o + 4 * k ≤ size → a + 4 * k ≤ size → (o ≤ a ∨ a + 4 * k ≤ o) →
    WP isa (.block (maskCopy k o a)) s fun u =>
      val32 u.mem base o k = (if c then val32 s.mem base a k else 0) ∧
      Keeps [.eax] s u ∧ Outside base o (4 * k) s.mem u.mem
  | 0, _, _, _, _, _, _, _, _, _ => WP.block_nil
      ⟨by cases c <;> rfl, Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hs, hc, ho, ha, sep => by
    have hn := hs.nowrap
    simp only [maskCopy, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_sc hs (d := a) (by omega)) fun s₁ U₁ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₂ U₂ => ?_
    have K₂ := U₁.keeps.trans U₂.keeps
    have hs₂ := hs.of_keeps K₂ (by decide)
    refine wp_storeS (hs₂.ea (d := o) (by omega)) (hs₂.write (d := o) (n := 4) (by omega))
      fun s₃ M₃ => ?_
    have K₃ : Keeps [.eax] s s₃ := K₂.trans (M₃.keeps _)
    have hs₃ := hs.of_keeps K₃ (by decide)
    have O₃ : Outside base o 4 s.mem s₃.mem := by
      rw [M₃.mem, U₂.mem, U₁.mem]; exact writeW32_outside _ _ _ (by omega)
    have hc₃ : s₃.gpr .ecx = (if c then BitVec.allOnes 32 else 0) := by
      rw [K₃.1 _ (by decide), hc]
    refine WP.mono (maskCopy_ok c k hs₃ hc₃ (o := o + 4) (a := a + 4)
      (by omega) (by omega) (by omega)) fun u ⟨V, K, O⟩ =>
      ⟨?_, K₃.trans K, (O₃.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega))⟩
    rw [val32, O.w32 (by omega) (by omega), V, O₃.val32 (by omega) (by omega), M₃.mem,
      w32_write_self, U₂.gpr, U₁.gpr, U₁.other _ (by decide), hc]
    cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      BitVec.and_allOnes] <;> simp [val32, w32]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvSignMask` -/

section

/-! # The mask of a signed word coefficient -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem signMask_eq (x : BitVec 32) :
    0 - (x >>> 31) = if 2 ^ 31 ≤ x.toNat then BitVec.allOnes 32 else 0 := by
  have E : x >>> 31 = if 2 ^ 31 ≤ x.toNat then (1 : BitVec 32) else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := x.isLt
    have : (1 : BitVec 32).toNat = 1 := by decide
    have : (0 : BitVec 32).toNat = 0 := by decide
    split <;> omega
  rw [E]
  split <;> decide

theorem maskOf_ok {s : State} {base : Addr} {size coefficient : Nat}
    (hs : Scr s base size) (hc : coefficient + 4 ≤ size) :
    WP isa (.block (maskOf coefficient)) s fun u =>
      u.gpr .ecx = (if 2 ^ 31 ≤ w32 s.mem base coefficient then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s u ∧ u.mem = s.mem := by
  unfold maskOf
  refine wp_movS (readSrc_sc hs hc) fun s₁ U₁ _ => ?_
  refine wp_shr (by decide) fun s₂ U₂ _ => ?_
  refine wp_movS rfl fun s₃ U₃ _ => ?_
  refine wp_subS rfl fun u U₄ _ => WP.block_nil ?_
  refine ⟨?_, (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
    (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide)), ?_⟩
  · rw [U₄.gpr, U₃.gpr, U₃.other _ (by decide), U₂.gpr, U₁.gpr]
    exact signMask_eq _
  · rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvCorrection` -/

section

/-! # Correcting an unsigned row for a negative coefficient -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem correction_ok {s : State} {base : Addr} {size coefficient acc src tmp k : Nat}
    (hs : Scr s base size) (hc : coefficient + 4 ≤ size) (ha : acc + 4 * (k + 2) ≤ size)
    (hb : src + 4 * (k + 1) ≤ size) (ht : tmp + 4 * (k + 1) ≤ size)
    (st : tmp + 4 * (k + 1) ≤ acc ∨ acc + 4 * (k + 2) ≤ tmp)
    (sb : tmp ≤ src ∨ src + 4 * (k + 1) ≤ tmp) :
    WP isa (.block (correction coefficient acc src tmp (k + 2))) s fun u =>
      Unch base [(acc, 4 * (k + 2)), (tmp, 4 * (k + 1))] s.mem u.mem ∧ Keeps clob s u ∧
      ∃ c : Bool, val32 u.mem base acc (k + 2) + 2 ^ 32 *
          (if 2 ^ 31 ≤ w32 s.mem base coefficient then val32 s.mem base src (k + 1) else 0) =
        val32 s.mem base acc (k + 2) + 2 ^ (32 * (k + 2)) * c.toNat := by
  have hn := hs.nowrap
  unfold correction
  rw [show k + 2 - 1 = k + 1 by omega]
  refine WP.block_append (WP.block_append (WP.mono (maskOf_ok hs hc) fun s₁ ⟨C₁, K₁, M₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (maskCopy_ok (decide (2 ^ 31 ≤ w32 s.mem base coefficient)) (k + 1) hs₁
    (by simpa using C₁) ht hb sb) fun s₂ ⟨V₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  simp only [M₁, decide_eq_true_eq] at V₂
  rw [subInPlace_eq]
  refine WP.mono (chainSubSelf_ok hs₂ k (acc := acc + 4) (b := tmp)
    (by omega) ht (by omega)) fun u ⟨O₃, ⟨c, _, V₃⟩, K₃⟩ => ?_
  refine ⟨?_, ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)), c, ?_⟩
  · intro x hx
    have xa := hx (acc, 4 * (k + 2)) (by simp)
    have xt := hx (tmp, 4 * (k + 1)) (by simp)
    rw [O₃ x (by omega), O₂ x xt, M₁]
  · rw [V₂, O₂.val32 (d := acc + 4) (k := k + 1) (by omega) (by omega), M₁] at V₃
    change w32 u.mem base acc + 2 ^ 32 * val32 u.mem base (acc + 4) (k + 1) + _ =
      w32 s.mem base acc + 2 ^ 32 * val32 s.mem base (acc + 4) (k + 1) + _
    rw [O₃.w32 (by omega) (by omega), O₂.w32 (by omega) (by omega), M₁,
      show k + 2 = (k + 1) + 1 by omega, pow32_succ]
    have := congrArg (fun x => 2 ^ 32 * x) V₃
    simp only [Nat.mul_add, ← Nat.mul_assoc] at this ⊢
    omega

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvNormalize` -/

section

/-! # Adding the modulus under the sign mask -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem addInPlace_eq (dst src n : Nat) :
    addInPlace dst src n = chainK .add .adc dst dst src n := rfl

theorem addIfNeg_ok {s : State} {base : Addr} {size acc modulus tmp n : Nat}
    (hs : Scr s base size) (ha : acc + 4 * (n + 1) ≤ size) (hm : modulus + 4 * n ≤ size)
    (ht : tmp + 4 * (n + 1) ≤ size)
    (sta : tmp + 4 * (n + 1) ≤ acc ∨ acc + 4 * (n + 1) ≤ tmp)
    (stm : tmp + 4 * (n + 1) ≤ modulus ∨ modulus + 4 * n ≤ tmp) :
    WP isa (.block (addIfNeg acc modulus tmp n)) s fun u =>
      Unch base [(acc, 4 * (n + 1)), (tmp, 4 * (n + 1))] s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧
      val32 u.mem base acc (n + 1) =
        (val32 s.mem base acc (n + 1) +
          if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then val32 s.mem base modulus n else 0) %
          2 ^ (32 * (n + 1)) := by
  have hn := hs.nowrap
  unfold addIfNeg
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (maskOf_ok hs (by omega)) fun s₁ ⟨C₁, K₁, M₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (maskCopy_ok (decide (2 ^ 31 ≤ w32 s.mem base (acc + 4 * n))) n hs₁
    (by simpa using C₁) (by omega) hm (by omega)) fun s₂ ⟨V₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  simp only [M₁, decide_eq_true_eq] at V₂
  refine WP.mono (zeros_ok hs₂ (acc := tmp + 4 * n) (k := 1) (by omega)) fun s₃ ⟨O₃, V₃, K₃⟩ => ?_
  have Vtmp : val32 s₃.mem base tmp (n + 1) =
      if 2 ^ 31 ≤ w32 s.mem base (acc + 4 * n) then val32 s.mem base modulus n else 0 := by
    simp only [val32, Nat.mul_zero, Nat.add_zero] at V₃
    rw [val32_succ, O₃.val32 (by omega) (by omega), V₃, V₂, Nat.mul_zero, Nat.add_zero]
  have VAcc : val32 s₃.mem base acc (n + 1) = val32 s.mem base acc (n + 1) := by
    rw [O₃.val32 (by omega) (by omega), O₂.val32 (by omega) (by omega), M₁]
  rw [addInPlace_eq]
  refine WP.mono (chainAddSelf_ok (hs₂.of_keeps K₃ (by decide)) n ha ht (by omega))
    fun u ⟨O₄, ⟨c, _, V₄⟩, K₄⟩ => ⟨?_, ?_, ?_⟩
  · intro x hx
    have hacc := hx (acc, 4 * (n + 1)) (by simp)
    have htmp := hx (tmp, 4 * (n + 1)) (by simp)
    rw [O₄ x hacc, O₃ x (by omega), O₂ x (by omega), M₁]
  · exact ((K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))
  · rw [Vtmp, VAcc] at V₄
    have E := congrArg (fun x => x % 2 ^ (32 * (n + 1))) V₄
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)] at E
    exact E

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvShiftTail` -/

section

/-! # One output word of the divstep arithmetic shift -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem shr_word32 (lo hi : BitVec 32) :
    (lo >>> 30 + ((hi + hi) + (hi + hi))).toNat =
      (lo.toNat / 2 ^ 30 + 4 * hi.toNat) % 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem shrTail_ok {s : State} {base : Addr} {size dst : Nat}
    (hs : Scr s base size) (hd : dst + 4 ≤ size) :
    WP isa (.block (shrTail dst)) s fun u =>
      w32 u.mem base dst = ((s.gpr .eax).toNat / 2 ^ 30 + 4 * (s.gpr .ebx).toNat) % 2 ^ 32 ∧
      Keeps [.eax, .ebx] s u ∧ Outside base dst 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold shrTail
  refine wp_shr (by decide) fun s₁ U₁ _ => ?_
  refine wp_addS rfl fun s₂ U₂ _ => ?_
  refine wp_addS rfl fun s₃ U₃ _ => ?_
  refine wp_addS rfl fun s₄ U₄ _ => ?_
  have K : Keeps [.eax, .ebx] s s₄ :=
    (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      (U₃.keeps.mono (by decide))).trans (U₄.keeps.mono (by decide))
  have hs₄ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₄.ea (by omega)) (hs₄.write hd) fun u U₅ => WP.block_nil ?_
  refine ⟨?_, K.trans (U₅.keeps _), ?_⟩
  · rw [U₅.mem, w32_write_self, U₄.gpr, U₃.other _ (by decide), U₂.other _ (by decide),
      U₁.gpr, U₃.gpr, U₂.gpr, U₁.other _ (by decide)]
    exact shr_word32 _ _
  · rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

theorem shrStep_ok {s : State} {base : Addr} {size dst src j : Nat}
    (hs : Scr s base size) (hd : dst + 4 * j + 4 ≤ size) (ha : src + 4 * (j + 1) + 4 ≤ size) :
    WP isa (.block (shrStep dst src j)) s fun u =>
      w32 u.mem base (dst + 4 * j) =
        (w32 s.mem base (src + 4 * j) / 2 ^ 30 + 4 * w32 s.mem base (src + 4 * (j + 1))) % 2 ^ 32 ∧
      Keeps [.eax, .ebx] s u ∧ Outside base (dst + 4 * j) 4 s.mem u.mem := by
  unfold shrStep
  refine WP.block_append ?_
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ ha) fun s₂ U₂ _ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  refine WP.mono (shrTail_ok (hs.of_keeps K (by decide)) hd) fun u ⟨V, K', O⟩ => ⟨?_, K.trans K', ?_⟩
  · rw [V, U₂.other _ (by decide), U₁.gpr, U₂.gpr, U₁.mem]
  · rw [U₂.mem, U₁.mem] at O
    exact O

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvShift` -/

section

/-! # Shifting the signed result of a divstep matrix row -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem shrRows_ok {s : State} {base : Addr} {size dst src n : Nat}
    (hs : Scr s base size) (ha : src + 4 * n ≤ size) (hd : dst + 4 * n ≤ size)
    (sep : dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) :
    ∀ j, j + 1 ≤ n → WP isa (.block ((List.range j).flatMap (shrStep dst src))) s fun u =>
      val32 u.mem base dst j = val32 s.mem base src (j + 1) / 2 ^ 30 % 2 ^ (32 * j) ∧
      Keeps [.eax, .ebx] s u ∧ Outside base dst (4 * j) s.mem u.mem
  | 0, _ => WP.block_nil ⟨by simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
      Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrRows_ok hs ha hd sep j (by omega)) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_
    refine WP.mono (shrStep_ok (hs.of_keeps K₁ (by decide)) (by omega) (by omega))
      fun u ⟨V₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂, ?_⟩
    · rw [val32_succ, O₂.val32 (by omega) (by omega), V₁, V₂,
        O₁.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega),
        val32_succ s.mem base src (j + 1), val32_succ s.mem base src j, pow32_succ,
        Nat.mul_comm (2 ^ 32) (2 ^ (32 * j))]
      exact (shr_arith32 j _ _ _ (val32_lt _ _ _ _)).symm
    · intro x hx
      rw [O₂ x (by omega), O₁ x (by omega)]

def sext32 (m : Mem) (base : Addr) (src n : Nat) : Nat :=
  val32 m base src n + 2 ^ (32 * n) *
    (if 2 ^ 31 ≤ w32 m base (src + 4 * (n - 1)) then 2 ^ 32 - 1 else 0)

theorem shr30_ok {s : State} {base : Addr} {size dst src n : Nat}
    (hs : Scr s base size) (hn : 1 ≤ n) (ha : src + 4 * n ≤ size) (hd : dst + 4 * n ≤ size)
    (sep : dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst) :
    WP isa (.block (shr30 dst src n)) s fun u =>
      val32 u.mem base dst n = sext32 s.mem base src n / 2 ^ 30 % 2 ^ (32 * n) ∧
      Keeps [.eax, .ebx, .ecx] s u ∧ Outside base dst (4 * n) s.mem u.mem := by
  have hwrap := hs.nowrap
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [shr30, Nat.add_sub_cancel]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (shrRows_ok hs ha hd sep j (Nat.le_refl _)) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)))
  refine WP.mono (maskOf_ok (hs.of_keeps K₁ (by decide)) (by omega)) fun s₂ ⟨C₂, K₂, M₂⟩ => ?_
  have K : Keeps [.eax, .ebx, .ecx] s s₂ :=
    (K₁.mono (by decide)).trans (K₂.mono (by decide))
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_sc hs₂ (by omega)) fun s₃ U₃ _ => ?_
  refine wp_movS rfl fun s₄ U₄ _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .ecx] s₂ s₄ :=
    (U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))
  refine WP.mono (shrTail_ok (hs₂.of_keeps K' (by decide)) (by omega)) fun u ⟨V, K₅, O₅⟩ =>
    ⟨?_, (K.trans K').trans (K₅.mono (by decide)), ?_⟩
  · have W : w32 s₁.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      O₁.w32 (by omega) (by omega)
    rw [val32_succ, O₅.val32 (by omega) (by omega), U₄.mem, U₃.mem, M₂, V₁,
      V, U₄.other _ (by decide), U₃.gpr, U₄.gpr, U₃.other _ (by decide), C₂, M₂, W]
    simp only [w32] at W
    rw [W]
    have E : (if 2 ^ 31 ≤ w32 s.mem base (src + 4 * j) then BitVec.allOnes 32 else 0).toNat =
        if 2 ^ 31 ≤ w32 s.mem base (src + 4 * j) then 2 ^ 32 - 1 else 0 := by
      split <;> rfl
    rw [E, sext32, Nat.add_sub_cancel, val32_succ s.mem base src j, pow32_succ,
      Nat.mul_comm (2 ^ 32) (2 ^ (32 * j))]
    simpa only [Nat.mul_assoc] using (shr_arith32 j (val32 s.mem base src j)
      (w32 s.mem base (src + 4 * j))
      (if 2 ^ 31 ≤ w32 s.mem base (src + 4 * j) then 2 ^ 32 - 1 else 0)
      (val32_lt s.mem base src j)).symm
  · intro x hx
    rw [O₅ x (by omega), U₄.mem, U₃.mem, M₂, O₁ x (by omega)]

end VG.Proof.Weierstrass.X86.Inv

end
