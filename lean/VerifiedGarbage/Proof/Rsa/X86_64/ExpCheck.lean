import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Rsa.X86_64.Checked
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA on x86-64: BoringSSL's limits on the public exponent

`expCheck` sets ZF exactly when `e` is within BoringSSL's limits
(`Spec.Rsa.exponentValid`), keeping memory and every register but `rax`,
`r10` and `r11` (`expCheck_ok`); `failOut` writes zeros to `out` and
returns 0 (`failOut_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-! ## Arithmetic -/

/-- `x`, saturated at `2^34 - 1` from `2^33`. -/
def sat (x : Nat) : Nat := if x < 2 ^ 33 then x else 2 ^ 34 - 1

theorem sat_lt (x : Nat) : sat x < 2 ^ 34 := by unfold sat; split <;> omega

theorem sat_step (x b : Nat) (hb : b < 256) : sat (256 * sat x + b) = sat (256 * x + b) := by
  unfold sat; split <;> (try split) <;> (try split) <;> omega

theorem exponentValid_sat (x : Nat) : Spec.Rsa.exponentValid (sat x) = Spec.Rsa.exponentValid x := by
  unfold sat
  split
  · rfl
  · rename_i h
    rw [show Spec.Rsa.exponentValid (2 ^ 34 - 1) = false from by decide]
    simp only [Spec.Rsa.exponentValid, h, decide_false, Bool.and_false]

/-- The masked saturation of `expStep`. -/
theorem sat_mask (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.ofNat 64 v >>> 33).toNat <
        BitVec.toNat (1 : BitVec 64)))) |||
      (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.ofNat 64 v >>> 33).toNat <
        BitVec.toNat (1 : BitVec 64)))) ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) >>> 30) =
      BitVec.ofNat 64 (sat v) := by
  have hs : (BitVec.ofNat 64 v >>> 33).toNat = v / 2 ^ 33 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
  rw [hs, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, show BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) =
    BitVec.allOnes 64 from by decide]
  unfold sat
  by_cases h : v < 2 ^ 33
  · rw [decide_eq_true (by omega), ite_eq_left_of_eq_true _ _ (eq_true h),
      show 0#64 - BitVec.setWidth 64 (BitVec.ofBool true) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes,
      BitVec.xor_self, BitVec.zero_ushiftRight, BitVec.or_zero]
  · rw [decide_eq_false (by omega), ite_eq_right_of_eq_false _ _ (eq_false h),
      show 0#64 - BitVec.setWidth 64 (BitVec.ofBool false) = 0#64 from by decide, BitVec.and_zero, BitVec.zero_or,
      BitVec.zero_xor]
    decide

/-- The next byte shifted in. -/
theorem step_y {x : Nat} (hx : x < 2 ^ 34) (b : Byte) :
    (BitVec.ofNat 64 x).rotateRight 56 + BitVec.setWidth 64 b = BitVec.ofNat 64 (256 * x + b.toNat) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, ror56_toNat _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]
  omega

theorem shr33_eq_zero {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 33 = 0#64) ↔ v < 2 ^ 33 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_zero, Nat.div_eq_zero_iff]
  omega

theorem low_eq_zero {v : Nat} (hv : v < 2 ^ 64) : ((BitVec.ofNat 64 v &&& 1) ^^^ 1 = 0#64) ↔ v % 2 = 1 := by
  rw [BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem neg_flag_eq_zero (c : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = 0#64) ↔ c = false := by
  cases c <;> decide

/-- The flag `expTest` sets. -/
theorem expTest_val {v : Nat} (hv : v < 2 ^ 64) :
    ((BitVec.ofNat 64 v >>> 33 ||| (BitVec.ofNat 64 v &&& (1 : BitVec 64)) ^^^ (1 : BitVec 64) |||
          0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.ofNat 64 v).toNat <
            BitVec.toNat (3 : BitVec 64))))) == 0) = Spec.Rsa.exponentValid v := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff,
    shr33_eq_zero hv, low_eq_zero hv, neg_flag_eq_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    show BitVec.toNat (3 : BitVec 64) = 3 from rfl]
  simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

/-! ## `expCheck` -/

theorem eByte_ea (t : State) {ep : Addr} {j : Nat} (h8 : t.gpr .r8 = ep) (h10 : t.gpr .r10 = BitVec.ofNat 64 j) :
    t.ea eByte = ep + BitVec.ofNat 64 j := by
  simp only [State.ea, eByte, h8, h10, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

/-- One byte of `e`. -/
theorem expStep_ok {t : State} {ep : Addr} {L j x : Nat} {b : Byte} (h8 : t.gpr .r8 = ep)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 L) (h10 : t.gpr .r10 = BitVec.ofNat 64 j)
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (sat x)) (hj : j < L) (hL : L < 2 ^ 63)
    (ha : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 j) 1) (hb : t.mem (ep + BitVec.ofNat 64 j) = b) :
    WP isa (.block expStep) t fun t' => t'.gpr .r11 = BitVec.ofNat 64 (sat (256 * x + b.toNat)) ∧
      t'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ t'.zf = some (decide (j + 1 = L)) ∧ t'.mem = t.mem ∧
      Keep [.rax, .r10, .r11] t t' := by
  have hy := step_y (sat_lt x) b
  have hv : 256 * sat x + b.toNat < 2 ^ 64 := by have := sat_lt x; have := b.isLt; omega
  refine WP.mono (WP.keep [.rax, .r10, .r11] (Q := fun t' => t'.gpr .r11 = BitVec.ofNat 64 (sat (256 * x + b.toNat)) ∧
      t'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ t'.zf = some (decide (j + 1 = L)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold expStep
  xrun [State.ea, eByte, h8, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, h9, h10, h11, ha, hb, hy, sat_mask _ hv, sat_step x _ b.isLt, ofNat_add_one,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show L < 2 ^ 64 by omega)]

/-- After `j` bytes of `e`. -/
structure ExpInv (s : State) (ep : Addr) (L : Nat) (eb : List Byte) (j : Nat) (t : State) : Prop where
  r8 : t.gpr .r8 = ep
  r9 : t.gpr .r9 = BitVec.ofNat 64 L
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (sat (pre eb j))
  mem : t.mem = s.mem
  keep : Keep [.rax, .r10, .r11] s t

/-- `expCheck`: ZF set exactly when the `L` bytes `eb` of `e` at `r8` are
within BoringSSL's limits. -/
theorem expCheck_ok {s : State} {ep : Addr} {L : Nat} {eb : List Byte} (h8 : s.gpr .r8 = ep)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1) (heb : eb = Spec.Rsa.bytesAt s.mem ep L) :
    WP isa expCheck s fun t => t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) ∧ t.mem = s.mem ∧
      Keep [.rax, .r10, .r11] s t := by
  have hlen : eb.length = L := by rw [heb]; simp [Spec.Rsa.bytesAt]
  unfold expCheck
  refine WP.seq (WP.mono (WP.keep [.r10, .r11] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 0 ∧
      t.gpr .r11 = BitVec.ofNat 64 (sat (pre eb 0)) ∧ t.mem = s.mem) (by xrun; rfl) rfl)
    fun t₀ ⟨⟨h10, h11, hm⟩, k₀⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := L) (by omega) (ExpInv s ep L eb) ?_ (fun t h => h)
    ⟨(k₀.gpr (by decide)).trans h8, (k₀.gpr (by decide)).trans h9, h10, h11, hm, k₀.mono (by decide)⟩)
    fun t₁ hI => ?_)
  · intro j _ hj t hI
    have hb : t.mem (ep + BitVec.ofNat 64 j) = eb[j]'(by omega) := by
      rw [hI.mem]; subst heb; simp [Spec.Rsa.bytesAt]
    refine WP.mono (expStep_ok hI.r8 hI.r9 hI.r10 hI.r11 hj hL (by rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj) hb)
      fun t' ⟨h11', h10', hz, hm', k'⟩ => ⟨hz, (k'.gpr (by decide)).trans hI.r8, (k'.gpr (by decide)).trans hI.r9, h10', ?_,
        hm'.trans hI.mem, (hI.keep.trans k').mono (by decide)⟩
    rw [h11', pre_succ eb (by omega)]
  · refine WP.mono (WP.keep [.rax, .r10, .r11] (Q := fun t => t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) ∧
        t.mem = t₁.mem) ?_ rfl) fun t ⟨⟨hz, hm'⟩, k⟩ => ⟨hz, hm'.trans hI.mem, (hI.keep.trans k).mono (by decide)⟩
    have hv : sat (pre eb L) < 2 ^ 64 := by have := sat_lt (pre eb L); omega
    unfold expTest
    xrun [hI.r11]
    rw [BitVec.and_self, expTest_val hv, exponentValid_sat, ← hlen, pre_len]

/-! ## `failOut` -/

/-- After `j` zeros from `s₀`. -/
structure ZeroInv (s₀ : State) (op : Addr) (k j : Nat) (t : State) : Prop where
  keep : Keep [.r10, .r11] s₀ t
  r10 : t.gpr .r10 = op + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (k - j)
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

/-- `failOut`: zeros to the `k` bytes at `rdi`, and 0 in `rax`. -/
theorem failOut_ok {s : State} {op : Addr} {k : Nat} (hdi : s.gpr .rdi = op) (hsi : s.gpr .rsi = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 63) (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa failOut s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧ t.gpr .rax = 0 ∧
      (∀ x, (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep [.rax, .r10, .r11] s t := by
  unfold failOut
  refine WP.seq (WP.mono (WP.keep [.rax, .r10, .r11] (Q := fun t => t.gpr .r10 = op ∧
      t.gpr .r11 = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by xrun [hdi, hsi]) rfl)
    fun s₁ ⟨⟨h10, h11, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := k) (by omega) (ZeroInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [h10, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [h11, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ?_
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.r10, .r11] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .r10 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .r11 = BitVec.ofNat 64 (k - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = k))) (by
      xrun [State.ea, at0, hI.r10, hI.r11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ k - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, h10', h11', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), h10', h11', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  refine ⟨?_, by rw [hI.keep.gpr (by decide), hax], fun x hx => by rw [hI.frame x hx, hm₁],
    (k₁.trans hI.keep).mono (by decide)⟩
  simp only [Spec.Rsa.bytesAt]
  exact List.ext_getElem (by simp) fun i h₁ _ => by simpa using hI.bytes i (by simpa using h₁)

end VG.Proof.Rsa.X86_64
