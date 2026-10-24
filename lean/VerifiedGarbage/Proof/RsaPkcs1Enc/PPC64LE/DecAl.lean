module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecIrprf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the alternative length

The mask of the candidates, `bitMask (k - 11)`, by doublings (`maskPart_ok`),
and the alternative length, the last masked candidate of `CL` not above
`k - 11` (`alPart_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (bitMask altStep)

/-- The borrow of `a - b`, for values below `2 ^ 63`. -/
theorem borrow (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if b ≤ a then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> omega

/-- The select by a mask from a borrow. -/
theorem xor_sel (a c : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((a ^^^ c) &&& (BitVec.ofNat 64 (if p then 0 else 1) - BitVec.ofNat 64 1)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [hp, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

theorem read1_64 (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = (m a).setWidth 64 := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp

theorem maskBody_ok {t : State} :
    WP isa (.block [.add .r8 .r8 .r8, .addi .r8 .r8 1, .sub .r10 .r8 .r9, .lsr .d .r10 .r10 63]) t
      fun u => (u.mem = t.mem ∧ u.gpr .r8 = t.gpr .r8 + t.gpr .r8 + BitVec.ofNat 64 1 ∧
        u.gpr .r10 = (t.gpr .r8 + t.gpr .r8 + BitVec.ofNat 64 1 - t.gpr .r9) >>> 63) ∧ Keep [.r8, .r10] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  prun [exec_addi (show Reg.r8 ≠ .r0 by decide) (show 1 < 2 ^ 15 by decide)]

theorem dbl (p : Nat) (h1 : 1 ≤ p) (h : p * 2 < 2 ^ 34) :
    BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (p * 2 - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An iteration of the mask's loop: `2 ^ j - 1` to `2 ^ (j + 1) - 1`, and whether to go on. -/
theorem maskStep_ok {x j : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (hj : j < Spec.RsaPkcs1Enc.bitLength x)
    {u : State} (hu8 : u.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1)) (hu9 : u.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (.block [.add .r8 .r8 .r8, .addi .r8 .r8 1, .sub .r10 .r8 .r9, .lsr .d .r10 .r10 63]) u
      fun w => (w.mem = u.mem ∧ Keep [.r8, .r10] u w ∧ w.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1)) ∧
        ((w.gpr .r10).toNat ≠ 0 ↔ j + 1 ≠ Spec.RsaPkcs1Enc.bitLength x) := by
  have hlt := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega) hj
  have hpj : 2 ^ (j + 1) < 2 ^ 34 := by
    rw [Nat.pow_succ]; generalize 2 ^ j = p at *; omega
  have e8 : BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ ..] at hpj ⊢
    exact dbl _ Nat.one_le_two_pow hpj
  refine WP.mono maskBody_ok fun w ⟨⟨wm, w8, w10⟩, kw⟩ => ⟨⟨wm, kw, by rw [w8, hu8, e8]⟩, ?_⟩
  rw [w10, hu8, hu9, e8, borrow _ _ (by omega) (by omega), BitVec.toNat_ofNat]
  by_cases he : j + 1 = Spec.RsaPkcs1Enc.bitLength x
  · have h1 := Proof.RsaPkcs1Enc.bitMask_ge (x := x) (by omega)
    rw [he]
    simp only [show x ≤ 2 ^ Spec.RsaPkcs1Enc.bitLength x - 1 from h1, ↓reduceIte]; omega
  · have h1 := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j + 1) (by omega) (by omega)
    simp only [show ¬ x ≤ 2 ^ (j + 1) - 1 by omega, ↓reduceIte]; omega

theorem bitLength_pos {x : Nat} (hx1 : 1 ≤ x) : 0 < Spec.RsaPkcs1Enc.bitLength x := by
  simp only [Spec.RsaPkcs1Enc.bitLength]; split <;> omega

theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h8 : t₀.gpr .r8 = BitVec.ofNat 64 0)
    (h9 : t₀.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r8, .r10] t₀ u ∧ u.gpr .r8 = BitVec.ofNat 64 (bitMask x) :=
  VG.Proof.Bignum.PPC64LE.count_loop (bitLength_pos hx1) (fun j u => u.mem = t₀.mem ∧ Keep [.r8, .r10] t₀ u ∧
    u.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1))
    (fun _ hj u ⟨hm, hk, hu8⟩ => WP.mono (maskStep_ok hx1 hx hj hu8
      (by rw [hk.gpr _ (by decide), h9])) fun _ ⟨⟨wm, kw, w8⟩, w10⟩ => ⟨⟨wm.trans hm, hk.trans' kw, w8⟩, w10⟩)
    ⟨rfl, Keep.refl _ _, h8⟩

theorem cand_bv (a b : Byte) {M : Nat} (hM : M < 2 ^ 64) :
    (a.setWidth 64 <<< 8 + b.setWidth 64) &&& BitVec.ofNat 64 M =
      BitVec.ofNat 64 ((256 * a.toNat + b.toNat) &&& M) := by
  have ha := a.isLt
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  have hl : (256 * a.toNat + b.toNat) &&& M ≤ 256 * a.toNat + b.toNat := Nat.and_le_left
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt (a := M) hM, Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8 + b.toNat) (by omega), show a.toNat * 2 ^ 8 = 256 * a.toNat by omega,
    Nat.mod_eq_of_lt (by omega)]

theorem alBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 1) 1) :
    WP isa (.block alBody) t fun u => (u.mem = t.mem ∧
      u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 2 ∧ u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1 ∧
      u.gpr .r6 = t.gpr .r6 ^^^ ((t.gpr .r6 ^^^ (((t.mem (t.gpr .r11 + BitVec.ofNat 64 0)).setWidth 64 <<< 8 +
          (t.mem (t.gpr .r11 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .r8)) &&&
        (((t.gpr .r9 - (((t.mem (t.gpr .r11 + BitVec.ofNat 64 0)).setWidth 64 <<< 8 +
          (t.mem (t.gpr .r11 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .r8)) >>> 63) - BitVec.ofNat 64 1))) ∧
      Keep [.r10, .r5, .r4, .r6, .r11, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold alBody
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 h0,
    exec_lbz (s := (t.write .r10 ((t.mem.read (t.gpr .r11 + BitVec.ofNat 64 0) 1).setWidth 64)).write .r10
      (((t.mem.read (t.gpr .r11 + BitVec.ofNat 64 0) 1).setWidth 64) <<< 8))
      (show Reg.r11 ≠ .r0 by decide) c1 (by exact h1),
    exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide)]
  simp only [read1_64]

theorem bytes_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem alLoop_ok {t₀ : State} {x M : Nat} {CL : List Byte} {B : Addr}
    (hx : x < 2 ^ 32) (hM : M = bitMask x) (hMl : M < 2 ^ 32)
    (hm : ∀ i < 256, t₀.mem (B + BitVec.ofNat 64 i) = CL.getD i 0)
    (hr : ∀ i < 256, InRegions (t₀.rd ++ t₀.wr) (B + BitVec.ofNat 64 i) 1)
    (h8 : t₀.gpr .r8 = BitVec.ofNat 64 M) (h9 : t₀.gpr .r9 = BitVec.ofNat 64 x) (h11 : t₀.gpr .r11 = B)
    (h7 : t₀.gpr .r7 = BitVec.ofNat 64 128) (h6 : t₀.gpr .r6 = 0) :
    WP isa alLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r10, .r5, .r4, .r6, .r11, .r7] t₀ u ∧
      u.gpr .r6 = BitVec.ofNat 64 ((List.range 128).foldl (altStep (x + 11) CL) 0) := by
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := 128) (by decide) (by decide)
    (fun j u => u.mem = t₀.mem ∧ Keep [.r10, .r5, .r4, .r6, .r11, .r7] t₀ u ∧ u.gpr .r11 = B + BitVec.ofNat 64 (2 * j) ∧
      u.gpr .r6 = BitVec.ofNat 64 ((List.range j).foldl (altStep (x + 11) CL) 0))
    (fun j hj u ⟨um, ku, u11, u6⟩ _ => ?_) ⟨rfl, Keep.refl _ _, by rw [h11]; exact (BitVec.add_zero _).symm, h6⟩
    h7 |>.mono fun u ⟨a, b, _, c⟩ => ⟨a, b, c⟩
  have hr0 := hr (2 * j) (by omega)
  have hr1 := hr (2 * j + 1) (by omega)
  rw [← ku.rd, ← ku.wr] at hr0 hr1
  have u8 : u.gpr .r8 = BitVec.ofNat 64 M := (ku.gpr _ (by decide)).trans h8
  have u9 : u.gpr .r9 = BitVec.ofNat 64 x := (ku.gpr _ (by decide)).trans h9
  refine WP.mono (alBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) (by rw [u11, Offset.add_add]; exact hr1))
    fun w ⟨⟨wm, w11, w7, w6⟩, kw⟩ => ⟨⟨wm.trans um, ku.trans' kw, by rw [w11, u11, Offset.add_add]; rfl, ?_⟩, w7⟩
  rw [w6, u6, u8, u9, u11, BitVec.add_zero, Offset.add_add, um, hm _ (by omega), hm _ (by omega),
    cand_bv _ _ (by omega), Proof.RsaPkcs1Enc.foldl_range_succ]
  have hc : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M < 2 ^ 32 :=
    Nat.lt_of_le_of_lt Nat.and_le_right hMl
  rw [borrow _ _ (by omega) (by omega), xor_sel]
  have he : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M =
      Spec.Rsa.os2ip [CL.getD (2 * j) 0, CL.getD (2 * j + 1) 0] % 2 ^ Spec.RsaPkcs1Enc.bitLength (x + 11 - 11) := by
    rw [Proof.RsaPkcs1Enc.cand_eq, Nat.add_sub_cancel, hM, Proof.RsaPkcs1Enc.bitMask, Nat.and_two_pow_sub_one_eq_mod]
  rw [he]
  simp only [altStep, Nat.add_sub_cancel]
  split <;> rfl

/-! ## The parts -/

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

omit h in
theorem AMR.regs {t u : State} (hl : AMR s R EM kd t) (hk : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10,
    .r11, .r12] t u) (hm : u.mem = t.mem) : AMR s R EM kd u :=
  ⟨hl.post.regs hk.rd hk.wr hk.sp hm fun r hr => hk.gpr r (by revert r; decide), by rw [hm]; exact hl.cl,
    by rw [hm]; exact hl.am⟩

/-- After the mask: `bitMask (k - 11)` in `r8` and `k - 11` in `r9`. -/
structure MK (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  r8 : t.gpr .r8 = BitVec.ofNat 64 (bitMask ((s.gpr .r7).toNat - 11))
  r9 : t.gpr .r9 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11)

theorem maskPart_ok {t : State} (hl : AMR s R EM kd t) : WP isa maskPart t (MK s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hl.post
  have c1 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oK) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r9, .r8] (Q := fun u => u.mem = t.mem ∧
    u.gpr .r9 = s.gpr .r7 - BitVec.ofNat 64 11 ∧ u.gpr .r8 = BitVec.ofNat 64 0) ?_ rfl)
    fun t₁ ⟨⟨m₁, x9, x8⟩, k₁⟩ => ?_)
  · unfold maskInit
    prun [fp, exec_addSp0, hc.sp, c1, i1, hc.sl.k]
  have e9 : s.gpr .r7 - BitVec.ofNat 64 11 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e9] at x9
  exact WP.mono (maskLoop_ok (x := (s.gpr .r7).toNat - 11) (by omega) (by omega) x8 x9) fun u ⟨um, ku, u8⟩ =>
    ⟨hl.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁), u8,
      (ku.gpr _ (by decide)).trans x9⟩

/-- `CL`. -/
abbrev clOf (kd : List Byte) : List Byte := Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After the alternative length. -/
structure AL (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  al : t.gpr .r6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))

theorem alPart_ok {t : State} (hm : MK s R EM kd t) : WP isa alPart t (AL s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hm.amr.post
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sCL < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r6] (Q := fun u => u.mem = t.mem ∧
    u.gpr .r11 = scA s sCL ∧ u.gpr .r7 = BitVec.ofNat 64 128 ∧ u.gpr .r6 = BitVec.ofNat 64 0) ?_ rfl)
    fun t₁ ⟨⟨m₁, x11, x7, x6⟩, k₁⟩ => ?_)
  · unfold alInit scr
    prun [fp, exec_addSp0, hc.sp, c1, c2, i1, hc.sl.scr, exec_addi (show Reg.r11 ≠ .r0 by decide) c2]
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  have hcl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = clOf kd := hm.amr.cl
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .r7).toNat - 11) (by omega)
  refine WP.mono (alLoop_ok (x := (s.gpr .r7).toNat - 11) (M := bitMask ((s.gpr .r7).toNat - 11)) (CL := clOf kd)
    (B := scA s sCL) (by omega) rfl (by omega)
    (fun i hi => by rw [← hcl, bytes_getD _ _ hi, m₁])
    (fun i hi => by rw [Offset.add_add]; exact scInR h hc₁.wr (a := sCL + i) (n := 1) (by unfold sCL scrBytes; omega))
    (by rw [k₁.gpr _ (by decide), hm.r8]) (by rw [k₁.gpr _ (by decide), hm.r9]) x11 x7 x6) fun u ⟨um, ku, u6⟩ =>
    ⟨hm.amr.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁),
      by rw [u6, Nat.sub_add_cancel (by omega)]; rfl⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
