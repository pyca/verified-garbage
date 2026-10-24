module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecOut
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the selection

The validity and `*msg_len` (`selInit_ok`), the output's loop, and the
result and our return address (`finish_ok`): `selPart_ok`, from `SCN` to
`Fin`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

/-- `AM`. -/
abbrev amOf (s : State) (kd : List Byte) : List Byte :=
  Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .r7).toNat

/-- The validity of `EM`, as the scan found it. -/
abbrev vOfEM (s : State) (EM : List Byte) : Bool := Proof.RsaPkcs1Enc.vEM EM (s.gpr .r7).toNat

/-- The selected length. -/
abbrev lenOf (s : State) (EM : List Byte) (kd : List Byte) : Nat :=
  Proof.RsaPkcs1Enc.lselOf (vOfEM s EM) ((firstZero EM (s.gpr .r7).toNat).getD 0)
    (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd)) (s.gpr .r7).toNat

theorem sep_lt (EM : List Byte) {k : Nat} (hk : 0 < k) : (firstZero EM k).getD 0 < k := by
  cases h : firstZero EM k with
  | none => simp; omega
  | some i => exact (Proof.RsaPkcs1Enc.firstZero_some h).2.1

/-- At the end of the body: the output and `*msg_len` written, the result in
`r3` and our return address in the link register. -/
structure Fin (s : State) (R : BitVec 64) (EM AM : List Byte) (v ok : Bool) (len : Nat) (u : State) : Prop
    extends Fr3 s R u where
  r3 : u.gpr .r3 = R
  lr : u.lr = s.lr
  out : ∀ i < (s.gpr .r7).toNat, u.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
    outByte v ok ((s.gpr .r7).toNat - len) i (EM.getD i 1) (AM.getD i 0)
  ml : u.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 len &&& bm ok

section
variable {s : State} (h : DPre s) {R : BitVec 64}
include h

theorem outInit_ok {t : State} (hc : Fr3 s R t) (h12 : t.gpr .r12 = fb s) :
    WP isa (.block outInit) t fun u => (u.mem = t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) (t.gpr .r6) ∧
      u.gpr .r10 = scA s sAM ∧ u.gpr .r9 = 0) ∧ Keep [.r10, .r9] t u := by
  have c1 : oML < 2 ^ 15 ∧ oML % 4 = 0 := by decide
  have c2 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c3 : sAM < 2 ^ 15 := by decide
  have i1 := slotIn (u := t) hc.wr (d := oML) (by decide) (by decide)
  have i2 := slotIn (u := t) hc.wr (d := oScr) (by decide) (by decide)
  have hw : InRegions t.wr (s.gpr .r5 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, hc.wr, h.hwr]; exact ⟨mlR s, by simp, Region.contains_self _ _⟩
  have rS : ∀ v : BitVec 64, (t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) v).readW (fb s + BitVec.ofNat 64 oScr) 64 =
      stackArg s 13 := fun v => by
    have hf : Frame [mlR s] t.mem (t.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 0) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by rw [BitVec.add_zero]; exact Region.contains_self _ _)
    rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.km.sub_left (frame_sub s (by decide))) (by decide)]
    exact hc.sl.scr
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold outInit scr
  prun [h12, c1, c2, c3, i1, i2, hc.sl.ml, hw, rS, exec_addi (show Reg.r10 ≠ .r0 by decide) c3]
  rfl

omit h in
theorem finish_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block finish) t fun u => u.gpr .r3 = R ∧ u.lr = s.lr ∧ u.mem = t.mem ∧ u.sp = t.sp ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ ∀ r ∈ preserved, u.gpr r = t.gpr r := by
  have c1 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR < 2 ^ 15 ∧ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR % 4 = 0 := by decide
  have c2 : oLr < 2 ^ 15 ∧ oLr % 4 = 0 := by decide
  have i1 := slotIn (u := t) hc.wr (d := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) (by decide) (by decide)
  have i2 := slotIn (u := t) hc.wr (d := oLr) (by decide) (by decide)
  unfold finish
  prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.r, hc.sl.lr, exec_mtlr]
  intro r hr
  have : r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r12 := by revert r; decide
  simp only [this, ↓reduceIte]

/-- The selection: the validity, `*msg_len`, the output and the end. -/
theorem selPart_ok {EM kd : List Byte} {t : State} (hs : SCN s R EM kd t)
    (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa selPart t (Fin s R EM (amOf s kd) (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) (lenOf s EM kd)) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hs.amr.post
  have hsep := sep_lt EM (k := (s.gpr .r7).toNat) (by omega)
  have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .r7).toNat (clOf kd)
  refine WP.seq (WP.mono (validBlock_ok hc (outIn h hc (by omega)) (outIn h hc (by omega)) hs.r5 hs.r3 hs.al hs.r0 hs.r8
    (by omega) hR) fun t₁ ⟨⟨m₁, x11, x7, x5, x4, x6, x3, x12⟩, k₁⟩ => ?_)
  -- The values the block computed.
  have e0 : t.mem (s.gpr .r3 + BitVec.ofNat 64 0) = EM.getD 0 1 := by rw [← hc.em, bytes_getD' _ _ (by omega)]
  have e1 : t.mem (s.gpr .r3 + BitVec.ofNat 64 1) = EM.getD 1 1 := by rw [← hc.em, bytes_getD' _ _ (by omega)]
  have eL : (if Proof.RsaPkcs1Enc.vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM (s.gpr .r7).toNat).isSome
      ((firstZero EM (s.gpr .r7).toNat).getD 0) then s.gpr .r7 - BitVec.ofNat 64 ((firstZero EM (s.gpr .r7).toNat).getD 0) -
        BitVec.ofNat 64 1 else BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))) =
      BitVec.ofNat 64 (lenOf s EM kd) := by
    simp only [lenOf, vOfEM, Proof.RsaPkcs1Enc.vEM, Proof.RsaPkcs1Enc.lselOf]
    split
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega),
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    · rfl
  have hlen : lenOf s EM kd ≤ (s.gpr .r7).toNat := by
    simp only [lenOf, Proof.RsaPkcs1Enc.lselOf]; split <;> omega
  simp only [e0, e1] at x5 x6 x3
  rw [eL] at x6 x3
  rw [show s.gpr .r7 - BitVec.ofNat 64 (lenOf s EM kd) = BitVec.ofNat 64 ((s.gpr .r7).toNat - lenOf s EM kd) by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega] at x3
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  -- `*msg_len`.
  refine WP.seq (WP.mono (outInit_ok h hc₁.fr3 x12) fun t₂ ⟨⟨m₂, x10, x9⟩, k₂⟩ => ?_)
  rw [x6] at m₂
  have hY : Region.Sub ⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩ (mlR s) := by rw [BitVec.add_zero]; exact fun _ h => h
  have F₂ : Frame [⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₂ : Fr3 s R t₂ := hc₁.fr3.store h k₂.rd k₂.wr k₂.sp (fun r hr => k₂.gpr r (by revert r; decide)) (.inr rfl) hY F₂
  have bk : ∀ (X : Region), X.Disjoint (mlR s) → X.len ≤ 2 ^ 64 → ∀ i < X.len,
      t₂.mem (X.base + BitVec.ofNat 64 i) = t.mem (X.base + BitVec.ofNat 64 i) := fun X hX hl i hi => by
    rw [F₂.bytes (fun Y hY' => by rw [List.mem_singleton.mp hY']; exact hX.sub_right hY) hl hi, m₁]
  have hwo := h.wo; have h4 := h.h4
  have g : ∀ r, r ∉ [Reg.r10, .r9] → r ∉ [Reg.r12, .r11, .r7, .r10, .r9, .r4, .r5, .r6, .r3] → t₂.gpr r = t.gpr r :=
    fun r h₁ h₂ => (k₂.gpr r h₁).trans (k₁.gpr r h₂)
  have h0 : OInv s R (BitVec.ofNat 64 (lenOf s EM kd) &&& bm (decide (R ^^^ BitVec.ofNat 64 1 = 0))) EM (amOf s kd)
      (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ((s.gpr .r7).toNat - lenOf s EM kd) 0 t₂ :=
    { fr := hc₂
      ml := by rw [m₂, BitVec.add_zero, Mem.readW_writeW_self64]
      r9 := by rw [x9]; rfl
      r11 := by rw [k₂.gpr _ (by decide), x11, BitVec.add_zero]
      r10 := by rw [x10, BitVec.add_zero]
      r4 := by rw [k₂.gpr _ (by decide), x4]
      r5 := by rw [k₂.gpr _ (by decide), x5]
      r3 := by rw [k₂.gpr _ (by decide), x3]
      r0 := by rw [g _ (by decide) (by decide), hs.r0]
      r8 := by rw [g _ (by decide) (by decide), hs.r8]
      done := fun j hj => absurd hj (Nat.not_lt_zero _)
      todo := fun j _ hj => by
        rw [show s.gpr .r3 = (oR s).base from rfl, bk (oR s) h.om (by show (s.gpr .r4).toNat ≤ 2 ^ 64; omega) j
          (by show j < (s.gpr .r4).toNat; omega), show (oR s).base = s.gpr .r3 from rfl, ← hc.em, bytes_getD' _ _ hj]
      am := fun j hj => by
        rw [show scA s sAM = (⟨scA s sAM, (s.gpr .r7).toNat⟩ : Region).base from rfl,
          bk ⟨scA s sAM, (s.gpr .r7).toNat⟩ ((h.ms.symm.sub_left (sub_trans (scSub (by unfold sAM scrBytes; omega))
            (sc_sub h)))) (by show (s.gpr .r7).toNat ≤ 2 ^ 64; omega) j hj]
        have ham : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .r7).toNat = amOf s kd := hs.amr.am
        rw [← ham, bytes_getD' _ _ hj] }
  refine WP.seq (WP.mono (selLoop_ok h (by omega) h0 (by rw [k₂.gpr _ (by decide), x7])) fun t₃ h₃ => ?_)
  refine WP.mono (finish_ok h₃.fr) fun u ⟨u3, ul, um, usp, urd, uwr, uh⟩ => ?_
  have hc₃ := h₃.fr
  exact ⟨⟨usp.trans hc₃.sp, urd.trans hc₃.rd, uwr.trans hc₃.wr, fun r hr => (uh r hr).trans (hc₃.hi r hr),
    um ▸ hc₃.mem, um ▸ hc₃.sl, um ▸ hc₃.r⟩, u3, ul, fun i hi => by rw [um]; exact h₃.done i hi,
    by rw [um]; exact h₃.ml⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
