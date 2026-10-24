module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scan
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ffdh_generate_key` on PPC64LE: the smear and the cut

`smear_ok`: the bits of the octet in `r14` below its top one, that one too
(`smearN`). `cut_ok`: `rand`'s `k` octets at `R` to x at `X`, zeros before
the index `ld` in `r22`, and'ed with the octet in `r14` at it, kept after it
(`KeyScalar.cut`), without a branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Ffdh.KeyScalar
open VG.Proof.MillerRabin.PPC64LE (mask)

/-! ## The smear -/

theorem smear_nat : ∀ n < 256, (let a := BitVec.ofNat 64 n ||| BitVec.ofNat 64 n >>> 1
    let b := a ||| a >>> 2
    b ||| b >>> 4) = BitVec.ofNat 64 (smearN n) := by decide +kernel

/-- `smear`: `r14 :=` `smearN` of its octet. -/
theorem smear_ok (s : State) {b : Byte} (h14 : s.gpr .r14 = b.setWidth 64) :
    WP isa (.block smear) s fun t =>
      (t.gpr .r14 = (BitVec.ofNat 8 (smearN b.toNat)).setWidth 64 ∧ t.mem = s.mem) ∧ Keep [.r14, .r16] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold smear
  prun [h14]
  have e : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by apply BitVec.eq_of_toNat_eq; simp
  have e2 : (BitVec.ofNat 8 (smearN b.toNat)).setWidth 64 = BitVec.ofNat 64 (smearN b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    have := smearN_lt _ b.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e, e2]
  exact smear_nat _ b.isLt

/-! ## Masks of the index -/

theorem lt_mask {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    0#64 - ((BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63) = mask (decide (j < l)) := by
  have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63 = BitVec.ofNat 64 (if j < l then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    split <;> omega
  rw [e]
  by_cases h : j < l <;> simp [h]

theorem eq_mask {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    0#64 - (((BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 l) - 1#64) >>> 63) = mask (decide (j = l)) := by
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 l) = BitVec.ofNat 64 (j ^^^ l) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hj hl) (by decide))]
  have hlt : j ^^^ l < 2 ^ 32 := Nat.xor_lt_two_pow hj hl
  have hz : j ^^^ l = 0 ↔ j = l := ⟨fun h => by
    have := congrArg (· ^^^ l) h
    simpa [Nat.xor_assoc] using this, fun h => by rw [h, Nat.xor_self]⟩
  have e : ((BitVec.ofNat 64 (j ^^^ l)) - 1#64) >>> 63 = BitVec.ofNat 64 (if j = l then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  rw [hx, e]
  by_cases h : j = l <;> simp [h]

theorem or_xor_mask (x : BitVec 64) (c : Bool) : (x ||| mask c) ^^^ mask c = if c then 0 else x := by
  cases c
  · show (x ||| 0) ^^^ 0 = x
    simp
  · show (x ||| BitVec.allOnes 64) ^^^ BitVec.allOnes 64 = 0
    rw [BitVec.or_allOnes, BitVec.xor_self]; rfl

/-- The octet the cut stores. -/
theorem cut_byte (b t : Byte) (lt eq : Bool) :
    (b.setWidth 64 &&& (if lt then 0 else if eq then t.setWidth 64 else 255#64)).setWidth 8 =
      if lt then 0 else if eq then b &&& t else b := by
  cases lt <;> cases eq <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
    apply BitVec.eq_of_toNat_eq <;> simp [BitVec.toNat_and]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt b.isLt]

theorem sel255 (v : BitVec 64) (c : Bool) : ((255#64 ^^^ v) &&& mask c) ^^^ 255#64 = if c then v else 255#64 := by
  rw [BitVec.xor_comm _ 255#64, sel]

/-! ## The cut -/

/-- The registers the cut writes. -/
def cutRegs : List Reg := [.r0, .r4, .r6, .r16, .r17, .r18, .r19, .r20, .r24, .r25]

/-- What the cut holds after `j` octets. -/
def CutInv (s : State) (R X : Addr) (k ld : Nat) (tb : Byte) (j : Nat) (t : State) : Prop :=
  t.gpr .r24 = off R j ∧ t.gpr .r25 = off X j ∧ t.gpr .r4 = BitVec.ofNat 64 j ∧ t.gpr .r22 = BitVec.ofNat 64 ld ∧
    t.gpr .r14 = tb.setWidth 64 ∧ Outside X 0 j s.mem t.mem ∧
    (∀ i < j, t.mem (off X i) = (cut (Spec.Rsa.bytesAt s.mem R k) ld tb).getD i 0) ∧ Keep cutRegs s t

theorem cutBody_ok {s t : State} {R X : Addr} {k ld j : Nat} {tb : Byte} (hj : j < k) (hk : k < 2 ^ 32)
    (hld : ld < k) (hx : Scr s X k) (hrd : InRegions (s.rd ++ s.wr) (off R j) 1)
    (hsep : ∀ y, ofs X y < k → off R j ≠ y) (h : CutInv s R X k ld tb j t) :
    WP isa (.block (cutBody ++ ([.subi .r6 .r6 1] : List Instr))) t fun u =>
      CutInv s R X k ld tb (j + 1) u ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 := by
  obtain ⟨t24, t25, t4, t9, t14, tout, tx, tk⟩ := h
  have hb : t.mem (off R j) = s.mem (off R j) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    exact hsep _ (by omega) rfl
  have hrd' : InRegions (t.rd ++ t.wr) (off R j) 1 := by rw [tk.rd, tk.wr]; exact hrd
  have hst : InRegions t.wr (off X j) 1 := (hx.congr tk.wr).st (d := j) (n := 1) (by omega)
  have hnw := hx.nowrap
  unfold cutBody
  refine WP.mono (WP.keep cutRegs (Q := fun u => u.gpr .r24 = off R (j + 1) ∧ u.gpr .r25 = off X (j + 1) ∧
      u.gpr .r4 = BitVec.ofNat 64 (j + 1) ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
      u.mem = t.mem.write (off X j) 1 (((s.mem (off R j)).setWidth 64 &&&
        (if decide (j < ld) then 0 else if decide (j = ld) then tb.setWidth 64 else 255#64)).setWidth 8)) ?_ (by decide))
    fun u ⟨⟨u24, u25, u4, u6, um⟩, ku⟩ => ⟨⟨u24, u25, u4, ?_, ?_, ?_, ?_, (tk.trans ku).mono (by decide)⟩, u6⟩
  · prun [t24, t25, t4, t9, t14, exec_lbz' (show Reg.r24 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd',
      exec_stb (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hst, BitVec.add_zero, Pub.read1_setWidth,
      hb, lt_mask (show j < 2 ^ 32 by omega) (show ld < 2 ^ 32 by omega),
      eq_mask (show j < 2 ^ 32 by omega) (show ld < 2 ^ 32 by omega), sel255, or_xor_mask]
    rw [BitVec.ofNat_add]
  · rw [ku.gpr .r22 (by decide), t9]
  · rw [ku.gpr .r14 (by decide), t14]
  · rw [um]
    exact (tout.mono (Nat.le_refl _) (by omega)).trans ((write1_outside t.mem X (d := j) _ (by omega)).mono
      (by omega) (by omega))
  · intro i hi
    rw [um]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [write1_outside t.mem X (d := j) _ (by omega) _ (by rw [Bignum.PPC64LE.ofs_off0 X (by omega)]; omega)]
      exact tx i hi
    · rw [write1_self, cut_byte]
      have hl : (Spec.Rsa.bytesAt s.mem R k).length = k := by simp [Spec.Rsa.bytesAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [cut_length tb (by omega), hl]; omega),
        Option.getD_some, cut_get tb (by omega) (by omega)]
      have hr : (Spec.Rsa.bytesAt s.mem R k)[i]'(by omega) = s.mem (off R i) := by
        simp [Spec.Rsa.bytesAt, off]
      rw [hr]
      by_cases h1 : i < ld
      · simp [h1]
      · by_cases h2 : i = ld <;> simp [h1, h2]

/-- The cut of `rand`'s `k` octets at `R` (`r24`) into x at `X` (`r25`). -/
theorem cut_ok {s : State} {R X : Addr} {k ld : Nat} {tb : Byte} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32) (hld : ld < k)
    (hx : Scr s X k) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hsep : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) (h24 : s.gpr .r24 = off R 0) (h25 : s.gpr .r25 = off X 0)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 0) (h22 : s.gpr .r22 = BitVec.ofNat 64 ld) (h14 : s.gpr .r14 = tb.setWidth 64)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) :
    WP isa (countLoop .r6 cutBody) s fun t =>
      (Spec.Rsa.bytesAt t.mem X k = cut (Spec.Rsa.bytesAt s.mem R k) ld tb ∧ Outside X 0 k s.mem t.mem) ∧
        Keep cutRegs s t := by
  refine WP.mono (wp_countdown (cnt := .r6) (N := k) (by omega) (by omega) (CutInv s R X k ld tb)
    (fun j hj t ht _ => cutBody_ok hj hk hld hx (hrd j hj) (hsep j hj) ht)
    ⟨h24, h25, h4, h22, h14, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), Keep.refl _ _⟩ h6)
    fun t ⟨_, _, _, _, _, tout, tx, kt⟩ => ⟨⟨?_, tout⟩, kt⟩
  have hl : (Spec.Rsa.bytesAt s.mem R k).length = k := by simp [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by rw [cut_length tb (by omega), hl]; simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
  have e : (Spec.Rsa.bytesAt t.mem X k)[i] = t.mem (off X i) := by simp [Spec.Rsa.bytesAt, off]
  rw [e, tx i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## The mask of x -/

/-- The masked loop: x's `k` octets (`r25`) and'ed with the mask of `c` in `r17`. -/
theorem masked_ok {s : State} {X : Addr} {k : Nat} {c : Bool} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32) (hx : Scr s X k)
    (h25 : s.gpr .r25 = off X 0) (h17 : s.gpr .r17 = mask c) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) :
    WP isa (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1]) s
      fun t => (Spec.Rsa.bytesAt t.mem X k = (if c then Spec.Rsa.bytesAt s.mem X k else List.replicate k 0) ∧
        Outside X 0 k s.mem t.mem) ∧ Keep [.r6, .r16, .r25] s t := by
  have hnw := hx.nowrap
  let Inv : Nat → State → Prop := fun j t => t.gpr .r25 = off X j ∧ t.gpr .r17 = mask c ∧
    Outside X 0 j s.mem t.mem ∧ (∀ i < j, t.mem (off X i) = if c then s.mem (off X i) else 0) ∧
    Keep [.r6, .r16, .r25] s t
  refine WP.mono (wp_countdown (cnt := .r6) (N := k) (by omega) (by omega) Inv
    (fun j hj t ⟨t25, t17, tout, tz, tk⟩ _ => ?_) ⟨h25, h17, Outside.refl _ _ _ _, fun _ h => absurd h (by omega),
      Keep.refl _ _⟩ h6) fun t ⟨_, _, tout, tz, kt⟩ => ⟨⟨?_, tout⟩, kt⟩
  · have hst : InRegions t.wr (off X j) 1 := (hx.congr tk.wr).st (d := j) (n := 1) (by omega)
    have hrd : InRegions (t.rd ++ t.wr) (off X j) 1 := (hx.congr tk.wr).ld (d := j) (n := 1) (by omega)
    have hb : t.mem (off X j) = s.mem (off X j) :=
      tout _ (Or.inr (by rw [Bignum.PPC64LE.ofs_off0 X (by omega)]; omega))
    refine WP.mono (WP.keep [.r6, .r16, .r25] (Q := fun u => u.gpr .r25 = off X (j + 1) ∧ u.gpr .r17 = mask c ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
        u.mem = t.mem.write (off X j) 1 (if c then s.mem (off X j) else 0)) (by
      prun [t25, t17, exec_lbz' (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
        exec_stb (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hst, BitVec.add_zero,
        Pub.read1_setWidth, hb, Pub.mask_byte])
      (by decide)) fun u ⟨⟨u25, u17, u6, um⟩, ku⟩ =>
        ⟨⟨u25, u17, ?_, fun i hi => ?_, (tk.trans ku).mono (by decide)⟩, u6⟩
    · rw [um]
      exact (tout.mono (Nat.le_refl _) (by omega)).trans ((write1_outside t.mem X (d := j) _ (by omega)).mono
        (by omega) (by omega))
    · rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [write1_outside t.mem X (d := j) _ (by omega) _ (by rw [Bignum.PPC64LE.ofs_off0 X (by omega)]; omega)]
        exact tz i hi
      · exact write1_self _ _ _
  · apply List.ext_getElem (by cases c <;> simp [Spec.Rsa.bytesAt])
    intro i h1 _
    have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
    have e : ∀ m : Mem, (Spec.Rsa.bytesAt m X k)[i]'(by simp [Spec.Rsa.bytesAt]; omega) = m (off X i) :=
      fun m => by simp [Spec.Rsa.bytesAt, off]
    rw [e, tz i hi]
    cases c
    · simp
    · simp only [ite_true]; rw [e]

end VG.Proof.Ffdh.PPC64LE.GenerateKey
