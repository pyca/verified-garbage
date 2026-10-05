import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Rsa.X86_64.Checked
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PdVerified

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck`. -/
section

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

theorem sat_lt (x : Nat) : VG.Proof.Rsa.X86_64.sat x < 2 ^ 34 := by unfold VG.Proof.Rsa.X86_64.sat; split <;> omega

theorem sat_step (x b : Nat) (hb : b < 256) : VG.Proof.Rsa.X86_64.sat (256 * VG.Proof.Rsa.X86_64.sat x + b) = VG.Proof.Rsa.X86_64.sat (256 * x + b) := by
  unfold VG.Proof.Rsa.X86_64.sat; split <;> (try split) <;> (try split) <;> omega

theorem exponentValid_sat (x : Nat) : Spec.Rsa.exponentValid (VG.Proof.Rsa.X86_64.sat x) = Spec.Rsa.exponentValid x := by
  unfold VG.Proof.Rsa.X86_64.sat
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
      BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.sat v) := by
  have hs : (BitVec.ofNat 64 v >>> 33).toNat = v / 2 ^ 33 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
  rw [hs, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, show BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) =
    BitVec.allOnes 64 from by decide]
  unfold VG.Proof.Rsa.X86_64.sat
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
    VG.Proof.Rsa.X86_64.shr33_eq_zero hv, VG.Proof.Rsa.X86_64.low_eq_zero hv, VG.Proof.Rsa.X86_64.neg_flag_eq_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
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
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.sat x)) (hj : j < L) (hL : L < 2 ^ 63)
    (ha : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 j) 1) (hb : t.mem (ep + BitVec.ofNat 64 j) = b) :
    WP isa (.block expStep) t fun t' => t'.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.sat (256 * x + b.toNat)) ∧
      t'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ t'.zf = some (decide (j + 1 = L)) ∧ t'.mem = t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .r10, .r11] t t' := by
  have hy := VG.Proof.Rsa.X86_64.step_y (VG.Proof.Rsa.X86_64.sat_lt x) b
  have hv : 256 * VG.Proof.Rsa.X86_64.sat x + b.toNat < 2 ^ 64 := by have := VG.Proof.Rsa.X86_64.sat_lt x; have := b.isLt; omega
  refine WP.mono (WP.keep [.rax, .r10, .r11] (Q := fun t' => t'.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.sat (256 * x + b.toNat)) ∧
      t'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ t'.zf = some (decide (j + 1 = L)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold expStep
  xrun [State.ea, eByte, h8, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, h9, h10, h11, ha, hb, hy, VG.Proof.Rsa.X86_64.sat_mask _ hv, VG.Proof.Rsa.X86_64.sat_step x _ b.isLt, ofNat_add_one,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show L < 2 ^ 64 by omega)]

/-- After `j` bytes of `e`. -/
structure ExpInv (s : State) (ep : Addr) (L : Nat) (eb : List Byte) (j : Nat) (t : State) : Prop where
  r8 : t.gpr .r8 = ep
  r9 : t.gpr .r9 = BitVec.ofNat 64 L
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.sat (VG.Proof.Bignum.X86_64.pre eb j))
  mem : t.mem = s.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .r10, .r11] s t

/-- `expCheck`: ZF set exactly when the `L` bytes `eb` of `e` at `r8` are
within BoringSSL's limits, and `e` saturated (`sat`) in `r11`. -/
theorem expCheckR_ok {s : State} {ep : Addr} {L : Nat} {eb : List Byte} (h8 : s.gpr .r8 = ep)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1) (heb : eb = Spec.Rsa.bytesAt s.mem ep L) :
    WP isa expCheck s fun t => t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) ∧ t.mem = s.mem ∧
      t.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip eb)) ∧ Keep [.rax, .r10, .r11] s t := by
  have hlen : eb.length = L := by rw [heb]; simp [Spec.Rsa.bytesAt]
  unfold expCheck
  refine WP.seq (WP.mono (WP.keep [.r10, .r11] (Q := fun t => t.gpr .r10 = BitVec.ofNat 64 0 ∧
      t.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Rsa.X86_64.sat (VG.Proof.Bignum.X86_64.pre eb 0)) ∧ t.mem = s.mem) (by xrun; rfl) rfl)
    fun t₀ ⟨⟨h10, h11, hm⟩, k₀⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := L) (by omega) (VG.Proof.Rsa.X86_64.ExpInv s ep L eb) ?_ (fun t h => h)
    ⟨(k₀.gpr (by decide)).trans h8, (k₀.gpr (by decide)).trans h9, h10, h11, hm, k₀.mono (by decide)⟩)
    fun t₁ hI => ?_)
  · intro j _ hj t hI
    have hb : t.mem (ep + BitVec.ofNat 64 j) = eb[j]'(by omega) := by
      rw [hI.mem]; subst heb; simp [Spec.Rsa.bytesAt]
    refine WP.mono (VG.Proof.Rsa.X86_64.expStep_ok hI.r8 hI.r9 hI.r10 hI.r11 hj hL (by rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj) hb)
      fun t' ⟨h11', h10', hz, hm', k'⟩ => ⟨hz, (k'.gpr (by decide)).trans hI.r8, (k'.gpr (by decide)).trans hI.r9, h10', ?_,
        hm'.trans hI.mem, (hI.keep.trans k').mono (by decide)⟩
    rw [h11', pre_succ eb (by omega)]
  · refine WP.mono (WP.keep [.rax, .r10, .r11] (Q := fun t => t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) ∧
        t.mem = t₁.mem ∧ t.gpr .r11 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip eb))) ?_ rfl)
      fun t ⟨⟨hz, hm', h11⟩, k⟩ => ⟨hz, hm'.trans hI.mem, h11, (hI.keep.trans k).mono (by decide)⟩
    have hv : sat (pre eb L) < 2 ^ 64 := by have := sat_lt (pre eb L); omega
    unfold expTest
    xrun [hI.r11]
    rw [BitVec.and_self, expTest_val hv, exponentValid_sat, ← hlen, pre_len]
    exact ⟨rfl, rfl⟩

/-- `expCheck`: ZF set exactly when the `L` bytes `eb` of `e` at `r8` are
within BoringSSL's limits. -/
theorem expCheck_ok {s : State} {ep : Addr} {L : Nat} {eb : List Byte} (h8 : s.gpr .r8 = ep)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 L) (hL1 : 1 ≤ L) (hL : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1) (heb : eb = Spec.Rsa.bytesAt s.mem ep L) :
    WP isa expCheck s fun t => t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) ∧ t.mem = s.mem ∧
      Keep [.rax, .r10, .r11] s t :=
  WP.mono (expCheckR_ok h8 h9 hL1 hL hrd heb) fun _ ⟨hz, hm, _, k⟩ => ⟨hz, hm, k⟩

/-! ## `failOut` -/

/-- After `j` zeros from `s₀`. -/
structure ZeroInv (s₀ : State) (op : Addr) (k j : Nat) (t : State) : Prop where
  keep : VG.Proof.MlKem.X86_64.Keep [.r10, .r11] s₀ t
  r10 : t.gpr .r10 = op + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (k - j)
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

/-- `failOut`: zeros to the `k` bytes at `rdi`, and 0 in `rax`. -/
theorem failOut_ok {s : State} {op : Addr} {k : Nat} (hdi : s.gpr .rdi = op) (hsi : s.gpr .rsi = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk : k < 2 ^ 63) (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa failOut s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧ t.gpr .rax = 0 ∧
      (∀ x, (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r10, .r11] s t := by
  unfold failOut
  refine WP.seq (WP.mono (WP.keep [.rax, .r10, .r11] (Q := fun t => t.gpr .r10 = op ∧
      t.gpr .r11 = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by xrun [hdi, hsi]) rfl)
    fun s₁ ⟨⟨h10, h11, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := k) (by omega) (VG.Proof.Rsa.X86_64.ZeroInv s₁ op k) ?_ (fun t h => h)
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
      rw [hm, VG.WriteBytes.writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  refine ⟨?_, by rw [hI.keep.gpr (by decide), hax], fun x hx => by rw [hI.frame x hx, hm₁],
    (k₁.trans hI.keep).mono (by decide)⟩
  simp only [Spec.Rsa.bytesAt]
  exact List.ext_getElem (by simp) fun i h₁ _ => by simpa using hI.bytes i (by simpa using h₁)

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.Guarded`. -/
section

/-!
# RSA on x86-64: a function guarded by the check of its public exponent

`guarded c` runs `expCheck`, then `failOut` if `e` is not within
BoringSSL's limits and `c` if it is. `expCheck` changes only `rax`, `r10`,
`r11` and the flags, so `c` runs from a state that agrees with the entry
state on its arguments, memory and permissions (`Same`): for a contract `k`
of `c` that depends only on those, `guarded c` is correct
(`guarded_correct`) and constant time (`guarded_ct`) whenever `c` is.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- `t` agrees with `s` on the argument registers, `rsp`, memory and
permissions. -/
structure Same (s t : State) : Prop where
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rsi
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = s.gpr .rcx
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9
  rsp : t.gpr .rsp = s.gpr .rsp
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Same.of_keep {s t : State} (k : VG.Proof.MlKem.X86_64.Keep [.rax, .r10, .r11] s t) (hm : t.mem = s.mem) : VG.Proof.Rsa.X86_64.Same s t :=
  ⟨k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), k.gpr (by decide),
    k.gpr (by decide), k.gpr (by decide), hm, k.2.1, k.2.2⟩

/-- The public exponent: the `r9` bytes at `r8`. -/
def eBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

/-- Whether the public exponent is within BoringSSL's limits. -/
def eValid (s : State) : Bool := Spec.Rsa.exponentValid (Spec.Rsa.os2ip (VG.Proof.Rsa.X86_64.eBytes s))

/-- What `guarded` needs of a state its contract allows: `out` (`rdi`) of
`out_len` (`rsi`) bytes, writable, not holding the return address; `e`
(`r8`) of `e_len` (`r9`) bytes, readable. -/
structure Geom (s : State) : Prop where
  k1 : 1 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat < 2 ^ 63
  out : ∀ j < (s.gpr .rsi).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  ret : ∀ b < 8, ∀ j < (s.gpr .rsi).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat < 2 ^ 63
  e : ∀ i < (s.gpr .r9).toNat, InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 i) 1

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `expCheck`, from the entry state. -/
theorem expCheck_entry {s : State} (g : VG.Proof.Rsa.X86_64.Geom s) :
    WP isa expCheck s fun t => t.zf = some (VG.Proof.Rsa.X86_64.eValid s) ∧ VG.Proof.Rsa.X86_64.Same s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide +kernel) (VG.Proof.Rsa.X86_64.expCheck_ok rfl (VG.Proof.Rsa.X86_64.ofNat_toNat _).symm g.L1 g.L2 g.e rfl)
    fun t ⟨hz, hm, k⟩ hmx => ⟨hz, Same.of_keep k hm, fun r hr => k.gpr (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hmx⟩

/-- `guarded c` is correct if `c` is, from states agreeing with the entry
state (`hpre`): with `c`'s postcondition if `e` is valid (`hok`), with zeros
and 0 if not (`hfail`). -/
theorem guarded_correct {c : Prog isa} {k : Contract isa} {post : State → State → Prop}
    (hc : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hgeom : ∀ s, k.pre s → VG.Proof.Rsa.X86_64.Geom s) (hpre : ∀ s t, VG.Proof.Rsa.X86_64.Same s t → k.pre s → k.pre t)
    (hok : ∀ s t s', k.pre s → VG.Proof.Rsa.X86_64.Same s t → VG.Proof.Rsa.X86_64.eValid s = true → k.post t s' → post s s')
    (hfail : ∀ s s', k.pre s → VG.Proof.Rsa.X86_64.eValid s = false →
      Spec.Rsa.bytesAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0 →
      s'.gpr .rax = 0 → post s s')
    (s : State) (h : k.pre s) : ∃ t s', Exec isa (guarded c) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  have g := hgeom s h
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.expCheck_entry g) fun t ⟨hz, hs, hcs, hmx⟩ => ?_)
  refine WP.ite (!VG.Proof.Rsa.X86_64.eValid s) (by simp [VG.X86_64.eval, hz]) (fun hb => ?_) (fun hb => ?_)
  · have hv : VG.Proof.Rsa.X86_64.eValid s = false := by simpa using hb
    refine WP.mono_mx (by decide +kernel) (VG.Proof.Rsa.X86_64.failOut_ok (s := t) (op := s.gpr .rdi) (k := (s.gpr .rsi).toNat)
      hs.rdi (by rw [hs.rsi, VG.Proof.Rsa.X86_64.ofNat_toNat]) g.k1 g.k2 (fun j hj => by rw [hs.wr]; exact g.out j hj))
      fun s' ⟨hb', hax, hfr, k'⟩ hmx' => ⟨⟨fun r hr => ?_, ?_, by rw [hmx', hmx]⟩, hfail s s' h hv hb' hax⟩
    · rw [k'.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hcs r hr]
    · refine Mem.readW_congr fun b hb => ?_
      rw [hfr _ fun j hj => g.ret b hb j hj, hs.mem]
  · have hv : VG.Proof.Rsa.X86_64.eValid s = true := by simpa using hb
    obtain ⟨tr, s', he, habi, hp⟩ := hc t (hpre s t hs h)
    refine ⟨tr, s', he, ⟨fun r hr => (habi.1 r hr).trans (hcs r hr), ?_, ?_⟩, hok s t s' h hs hv hp⟩
    · rw [← hs.rsp, ← hs.mem]; exact habi.2.1
    · rw [habi.2.2, hmx]

/-- Two runs of `c` from states its contract allows and agreeing on its
public data leak the same. -/
theorem relCT_of_ct {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (h : ConstantTime isa pre pub c) :
    RelCT isa (fun s₁ s₂ => pre s₁ ∧ pre s₂ ∧ pub s₁ s₂) c fun _ _ => True :=
  fun _ _ _ _ _ _ ⟨p₁, p₂, hp⟩ e₁ e₂ => ⟨h _ _ _ _ _ _ p₁ p₂ hp e₁ e₂, trivial⟩

/-- `guarded c` is constant time if `c` is: `expCheck` and `failOut` by the
taint analysis, from the pointers and lengths, and the branch on public
data. -/
theorem guarded_ct {c : Prog isa} {k : Contract isa} (hct : ConstantTime isa k.pre k.pub c)
    (hgeom : ∀ s, k.pre s → VG.Proof.Rsa.X86_64.Geom s) (hpre : ∀ s t, VG.Proof.Rsa.X86_64.Same s t → k.pre s → k.pre t)
    (hpub : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ →
      (∀ r ∈ [Reg.rdi, .rsi, .r8, .r9], s₁.gpr r = s₂.gpr r) ∧ VG.Proof.Rsa.X86_64.eBytes s₁ = VG.Proof.Rsa.X86_64.eBytes s₂)
    (hpubS : ∀ s₁ s₂ t₁ t₂, VG.Proof.Rsa.X86_64.Same s₁ t₁ → VG.Proof.Rsa.X86_64.Same s₂ t₂ → k.pub s₁ s₂ → k.pub t₁ t₂) :
    ConstantTime isa k.pre k.pub (guarded c) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have hexp := (RelCT.taint (A := taint) (Taint.ofRegs [.r8, .r9])
    (P := fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂)
    (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => Taint.agree_ofRegs fun r hr => (hpub _ _ p₁ p₂ hp).1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by taint_decide)).wpDep
    (F := fun (s t : State) => t.zf = some (VG.Proof.Rsa.X86_64.eValid s) ∧ VG.Proof.Rsa.X86_64.Same s t)
    fun s₁ s₂ ⟨p₁, p₂, _⟩ => ⟨WP.mono (VG.Proof.Rsa.X86_64.expCheck_entry (hgeom _ p₁)) fun _ h => ⟨h.1, h.2.1⟩,
      WP.mono (VG.Proof.Rsa.X86_64.expCheck_entry (hgeom _ p₂)) fun _ h => ⟨h.1, h.2.1⟩⟩
  refine RelCT.seq hexp (RelCT.ite ?_ ?_ ?_)
  · rintro u₁ u₂ ⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨z₁, -⟩, ⟨z₂, -⟩⟩
    simp only [VG.X86_64.eval, z₁, z₂, VG.Proof.Rsa.X86_64.eValid, (hpub _ _ p₁ p₂ hp).2]
  · refine (RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi]) (fun u₁ u₂ hu => ?_) (by taint_decide)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, s₁⟩, ⟨-, s₂⟩⟩, -⟩ := hu
    have hr := (hpub _ _ p₁ p₂ hp).1
    refine Taint.agree_ofRegs fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · rw [s₁.rdi, s₂.rdi]; exact hr _ (by simp)
    · rw [s₁.rsi, s₂.rsi]; exact hr _ (by simp)
  · refine (VG.Proof.Rsa.X86_64.relCT_of_ct hct).mono (fun u₁ u₂ hu => ?_) fun _ _ _ => trivial
    obtain ⟨⟨-, σ₁, σ₂, ⟨p₁, p₂, hp⟩, ⟨-, s₁⟩, ⟨-, s₂⟩⟩, -⟩ := hu
    exact ⟨hpre _ _ s₁ p₁, hpre _ _ s₂ p₂, hpubS _ _ _ _ s₁ s₂ hp⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PubChecked`. -/
section

/-!
# `vg_rsa_public_checked` and `vg_rsa_public_precomputed_checked` on x86-64

Each is `vg_rsa_public`'s or `vg_rsa_public_precomputed`'s code guarded by
the check of `e` (`guarded`), against the contracts on the registers of
those functions with the checked postcondition (`pubChkContract`,
`pdChkContract`), and from there against the shared contracts
(`publicChecked_verified`, `precomputedChecked_verified`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64

/-! ## The contracts on the registers -/

/-- `pubContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pubChkContract : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post s s' := Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- `pdContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pdChkContract : Contract isa where
  pre := pdContract.pre
  pub := pdContract.pub
  post s s' := ∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))

/-! ## What the contracts read of a state -/

theorem stackArg_same {s t : State} (h : VG.Proof.Rsa.X86_64.Same s t) (i : Nat) : stackArg t i = stackArg s i := by
  simp only [stackArg, stackArgAddr, h.rsp, h.mem]

theorem pubPre_same {s t : State} (h : VG.Proof.Rsa.X86_64.Same s t) : pubContract.pre t = pubContract.pre s := by
  simp only [pubContract, VG.Proof.Rsa.X86_64.stackArg_same h, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    h.rd, h.wr]

theorem pdPre_same {s t : State} (h : VG.Proof.Rsa.X86_64.Same s t) : pdContract.pre t = pdContract.pre s := by
  simp only [pdContract, VG.Proof.Rsa.X86_64.stackArg_same h, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    h.rd, h.wr]

theorem pubPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : VG.Proof.Rsa.X86_64.Same s₁ t₁) (h₂ : VG.Proof.Rsa.X86_64.Same s₂ t₂) (h : pubContract.pub s₁ s₂) :
    pubContract.pub t₁ t₂ := by
  simp only [pubContract, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    VG.Proof.Rsa.X86_64.stackArg_same h₁, VG.Proof.Rsa.X86_64.stackArg_same h₂, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₁.mem,
    h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₂.mem] at h ⊢
  exact h

theorem pdPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : VG.Proof.Rsa.X86_64.Same s₁ t₁) (h₂ : VG.Proof.Rsa.X86_64.Same s₂ t₂) (h : pdContract.pub s₁ s₂) :
    pdContract.pub t₁ t₂ := by
  simp only [pdContract, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    VG.Proof.Rsa.X86_64.stackArg_same h₁, VG.Proof.Rsa.X86_64.stackArg_same h₂, h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.rsp, h₁.mem,
    h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, h₂.rsp, h₂.mem] at h ⊢
  exact h

theorem pub_rsi {s : State} (h : pubContract.pre s) : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat := by
  simp only [pubContract] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hol, -⟩ := h
  exact hol

theorem pubGeom {s : State} (h : pubContract.pre s) : VG.Proof.Rsa.X86_64.Geom s := by
  have c := codeCtx_of h
  have hsi := VG.Proof.Rsa.X86_64.pub_rsi h
  have hk2 := c.hk2
  have hL2 := c.hL2
  refine ⟨by have := c.hk1; omega, by omega, fun j hj => c.hout j (by omega),
    fun b hb j hj => (c.hret b hb).2 j (by omega), c.hL1, by omega, fun i hi => c.heb.rd i (by
      rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)⟩

theorem pdGeom {s : State} (h : pdContract.pre s) : VG.Proof.Rsa.X86_64.Geom s := by
  have c := pdCtx_of h
  have hk2 := c.hk2
  have hL2 := c.hL2
  exact ⟨by have := c.hk1; omega, by omega, c.hout, fun b hb j hj => (c.hret b hb).2 j hj, c.hL1, by omega,
    fun i hi => c.heb.rd i (by rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)⟩

/-! ## `vg_rsa_public_checked` -/

theorem publicChecked_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa publicChecked s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s' := by
  refine VG.Proof.Rsa.X86_64.guarded_correct code_correct (fun _ h => VG.Proof.Rsa.X86_64.pubGeom h) (fun s t hs h => (VG.Proof.Rsa.X86_64.pubPre_same hs).symm ▸ h) ?_ ?_ s h
  · intro s t s' _ hs hv hp
    simp only [pubContract, VG.Proof.Rsa.X86_64.stackArg_same hs, hs.rdi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [VG.Proof.Rsa.X86_64.pubChkContract, Spec.Rsa.publicOpChecked]
    simp only [VG.Proof.Rsa.X86_64.eValid, VG.Proof.Rsa.X86_64.eBytes] at hv
    simp only [hv, ↓reduceIte]; exact hp
  · intro s s' h hv hb hax
    have hsi := VG.Proof.Rsa.X86_64.pub_rsi h
    simp only [VG.Proof.Rsa.X86_64.eValid, VG.Proof.Rsa.X86_64.eBytes] at hv
    simp only [VG.Proof.Rsa.X86_64.pubChkContract, Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, by rw [← hsi]; exact hb⟩

theorem publicChecked_constantTime : ConstantTime isa pubContract.pre pubContract.pub publicChecked :=
  VG.Proof.Rsa.X86_64.guarded_ct code_constantTime (fun _ h => VG.Proof.Rsa.X86_64.pubGeom h) (fun s t hs h => (VG.Proof.Rsa.X86_64.pubPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => VG.Proof.Rsa.X86_64.pubPub_same h₁ h₂ hp

theorem publicChecked_implies : pubChkContract.Implies (Spec.Rsa.publicCheckedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Rsa.X86_64.pubChkContract, pubContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Rsa.X86_64.pubChkContract, pubContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Rsa.X86_64.pubChkContract, pubContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Rsa.X86_64.pubChkContract, pubContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Rsa.X86_64.pubChkContract, pubContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, VG.Proof.Rsa.X86_64.pubChkContract, pubContract, stackArgs_four, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Bignum.X86_64.satState

theorem publicChecked_verified : Verified target publicChecked (Spec.Rsa.publicCheckedContract abi) :=
  have hct : ConstantTime isa pubChkContract.pre pubChkContract.pub publicChecked := VG.Proof.Rsa.X86_64.publicChecked_constantTime
  Verified.of_correct (k := VG.Proof.Rsa.X86_64.pubChkContract) VG.Proof.Rsa.X86_64.publicChecked_correct hct VG.Proof.Rsa.X86_64.publicChecked_implies

/-! ## `vg_rsa_public_precomputed_checked` -/

theorem precomputedChecked_correct (M : Mont)
    (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (precomputedChecked M.mm) s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s' := by
  refine VG.Proof.Rsa.X86_64.guarded_correct (pdCode_correct M hmx) (fun _ h => VG.Proof.Rsa.X86_64.pdGeom h) (fun s t hs h => (VG.Proof.Rsa.X86_64.pdPre_same hs).symm ▸ h)
    ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, VG.Proof.Rsa.X86_64.stackArg_same hs, hs.rdi, hs.rsi, hs.rdx, hs.rcx, hs.r8, hs.r9, hs.mem] at hp
    simp only [VG.Proof.Rsa.X86_64.eValid, VG.Proof.Rsa.X86_64.eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [VG.Proof.Rsa.X86_64.eValid, VG.Proof.Rsa.X86_64.eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

theorem precomputedChecked_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (precomputedChecked M.mm) :=
  VG.Proof.Rsa.X86_64.guarded_ct (pdCode_constantTime (M := M)) (fun _ h => VG.Proof.Rsa.X86_64.pdGeom h) (fun s t hs h => (VG.Proof.Rsa.X86_64.pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => VG.Proof.Rsa.X86_64.pdPub_same h₁ h₂ hp

theorem precomputedChecked_implies :
    pdChkContract.Implies (Spec.Rsa.publicPrecomputedCheckedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Rsa.X86_64.pdChkContract, pdContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Rsa.X86_64.pdChkContract, pdContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Rsa.X86_64.pdChkContract, pdContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Rsa.X86_64.pdChkContract, pdContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Rsa.X86_64.pdChkContract, pdContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hw, he⟩ := leak_eq2 (by simp [Spec.Rsa.wordsAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hw, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, VG.Proof.Rsa.X86_64.pdChkContract, pdContract, stackArgs_four, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using pdSatState

/-- `vg_rsa_public_precomputed_checked` with Montgomery multiplication `M`,
given that its code never loads MXCSR (which the registration file
evaluates). -/
theorem precomputedChecked_verified (M : Mont)
    (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (precomputedChecked M.mm) (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  have hct : ConstantTime isa pdChkContract.pre pdChkContract.pub (precomputedChecked M.mm) :=
    VG.Proof.Rsa.X86_64.precomputedChecked_constantTime M
  Verified.of_correct (k := VG.Proof.Rsa.X86_64.pdChkContract) (VG.Proof.Rsa.X86_64.precomputedChecked_correct M hmx) hct VG.Proof.Rsa.X86_64.precomputedChecked_implies

end VG.Proof.Rsa.X86_64

end
