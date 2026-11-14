module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecIrprf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPkcs1Enc.PPC64LE.DecAl`, which only this module used -/

section

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

variable {pc : Bool}

/-- The borrow of `a - b`, for values below `2 ^ 63`. -/
theorem borrow (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if b ≤ a then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> omega_arith

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
  have hlt := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega_using [hx1]) hj
  have hpj : 2 ^ (j + 1) < 2 ^ 34 := by
    rw [Nat.pow_succ]; generalize 2 ^ j = p at *; omega_using [hx, hlt]
  have e8 : BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ ..] at hpj ⊢
    exact dbl _ Nat.one_le_two_pow hpj
  refine WP.mono maskBody_ok fun w ⟨⟨wm, w8, w10⟩, kw⟩ => ⟨⟨wm, kw, by rw [w8, hu8, e8]⟩, ?_⟩
  rw [w10, hu8, hu9, e8, borrow _ _ (by omega_using [hpj]) (by omega_using [hx]), BitVec.toNat_ofNat]
  by_cases he : j + 1 = Spec.RsaPkcs1Enc.bitLength x
  · have h1 := Proof.RsaPkcs1Enc.bitMask_ge (x := x) (by omega_using [hx1])
    rw [he]
    simp only [show x ≤ 2 ^ Spec.RsaPkcs1Enc.bitLength x - 1 from h1, ↓reduceIte]; omega_using []
  · have h1 := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j + 1) (by omega_using [hx1]) (by omega_using [hj, he])
    simp only [show ¬ x ≤ 2 ^ (j + 1) - 1 by omega_using [h1], ↓reduceIte]; omega_using [he]

theorem bitLength_pos {x : Nat} (hx1 : 1 ≤ x) : 0 < Spec.RsaPkcs1Enc.bitLength x := by
  simp only [Spec.RsaPkcs1Enc.bitLength]; split <;> omega_arith

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
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := b.toNat) (by omega_using []),
    Nat.mod_eq_of_lt (a := M) hM, Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8) (by omega_using []),
    Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8 + b.toNat) (by omega_using []), show a.toNat * 2 ^ 8 = 256 * a.toNat by omega_using [],
    Nat.mod_eq_of_lt (by omega_using [hl])]

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
  have hr0 := hr (2 * j) (by omega_using [hj])
  have hr1 := hr (2 * j + 1) (by omega_using [hj])
  rw [← ku.rd, ← ku.wr] at hr0 hr1
  have u8 : u.gpr .r8 = BitVec.ofNat 64 M := (ku.gpr _ (by decide)).trans h8
  have u9 : u.gpr .r9 = BitVec.ofNat 64 x := (ku.gpr _ (by decide)).trans h9
  refine WP.mono (alBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) (by rw [u11, Offset.add_add]; exact hr1))
    fun w ⟨⟨wm, w11, w7, w6⟩, kw⟩ => ⟨⟨wm.trans um, ku.trans' kw, by rw [w11, u11, Offset.add_add]; rfl, ?_⟩, w7⟩
  rw [w6, u6, u8, u9, u11, BitVec.add_zero, Offset.add_add, um, hm _ (by omega_using [hj]), hm _ (by omega_using [hj]),
    cand_bv _ _ (by omega_using [hMl]), Proof.RsaPkcs1Enc.foldl_range_succ]
  have hc : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M < 2 ^ 32 :=
    Nat.lt_of_le_of_lt Nat.and_le_right hMl
  rw [borrow _ _ (by omega_using [hx]) (by omega_using [hc]), xor_sel]
  have he : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M =
      Spec.Rsa.os2ip [CL.getD (2 * j) 0, CL.getD (2 * j + 1) 0] % 2 ^ Spec.RsaPkcs1Enc.bitLength (x + 11 - 11) := by
    rw [Proof.RsaPkcs1Enc.cand_eq, Nat.add_sub_cancel, hM, Proof.RsaPkcs1Enc.bitMask, Nat.and_two_pow_sub_one_eq_mod]
  rw [he]
  simp only [altStep, Nat.add_sub_cancel]
  split <;> rfl

/-! ## The parts -/

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
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
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hk64]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  rw [e9] at x9
  exact WP.mono (maskLoop_ok (x := (s.gpr .r7).toNat - 11) (by omega_using [hk64]) (by omega_using [hk]) x8 x9) fun u ⟨um, ku, u8⟩ =>
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
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .r7).toNat - 11) (by omega_using [hk64])
  refine WP.mono (alLoop_ok (x := (s.gpr .r7).toNat - 11) (M := bitMask ((s.gpr .r7).toNat - 11)) (CL := clOf kd)
    (B := scA s sCL) (by omega_using [hk]) rfl (by omega_using [hk, hM])
    (fun i hi => by rw [← hcl, bytes_getD _ _ hi, m₁])
    (fun i hi => by rw [Offset.add_add]; exact scInR h hc₁.wr (a := sCL + i) (n := 1) (by unfold sCL scrBytes; omega_using [hi]))
    (by rw [k₁.gpr _ (by decide), hm.r8]) (by rw [k₁.gpr _ (by decide), hm.r9]) x11 x7 x6) fun u ⟨um, ku, u6⟩ =>
    ⟨hm.amr.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁),
      by rw [u6, Nat.sub_add_cancel (by omega_using [hk64])]; rfl⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the scan of `EM`

The first zero of `EM` from index 2 (`scanPart_ok`): whether there is one as
a mask in `r5`, and where in `r3`, as `firstZero` says.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero)

variable {pc : Bool}

/-- A Boolean as a mask. -/
def bm (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem zero_mask (b : Byte) :
    (0 : BitVec 64) - ((b.setWidth 64 - BitVec.ofNat 64 1) >>> 63) = bm (decide (b = 0)) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have hl := b.isLt
    have e : b.setWidth 64 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (b.toNat - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hb]),
        BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using []
    have e2 : BitVec.ofNat 64 (b.toNat - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega_using []
    rw [e, e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem scanBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (h0' : t.gpr .r0 = 0) (h8 : t.gpr .r8 = BitVec.allOnes 64) :
    WP isa (.block scanBody) t fun u => (u.mem = t.mem ∧ u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧
      u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1 ∧ u.gpr .r4 = t.gpr .r4 + BitVec.ofNat 64 1 ∧
      u.gpr .r5 = t.gpr .r5 ||| bm (decide (t.mem (t.gpr .r11 + BitVec.ofNat 64 0) = 0)) ∧
      u.gpr .r3 = t.gpr .r3 ||| ((t.gpr .r5 ^^^ BitVec.allOnes 64) &&&
        bm (decide (t.mem (t.gpr .r11 + BitVec.ofNat 64 0) = 0)) &&& t.gpr .r4)) ∧
      Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold scanBody
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 h0, exec_addi (show Reg.r4 ≠ .r0 by decide) c1,
    exec_addi (show Reg.r11 ≠ .r0 by decide) c1, h0', h8]
  simp only [read1_64, zero_mask]
  exact ⟨trivial, trivial⟩

theorem firstZero_succ (EM : List Byte) (j : Nat) :
    firstZero EM (2 + (j + 1)) = match firstZero EM (2 + j) with
      | some i => some i
      | none => if EM.getD (2 + j) 1 = 0 then some (2 + j) else none := by
  show firstZero EM ((2 + j) + 1) = _
  rw [firstZero]
  cases firstZero EM (2 + j) with
  | some i => rfl
  | none => simp

theorem r3_pos (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm true &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  show 0#64 ||| ((0#64 ^^^ BitVec.allOnes 64) &&& BitVec.allOnes 64 &&& BitVec.ofNat 64 n) = _
  rw [BitVec.zero_xor, BitVec.and_allOnes, BitVec.allOnes_and, BitVec.zero_or]

theorem r3_neg (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm false &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bm]

theorem scanLoop_ok {t₀ : State} {O : Addr} {EM : List Byte} {k : Nat} (hk : 3 ≤ k) (hk2 : k < 2 ^ 32)
    (hEM : ∀ i < k, t₀.mem (O + BitVec.ofNat 64 i) = EM.getD i 1)
    (hr : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (O + BitVec.ofNat 64 i) 1)
    (h11 : t₀.gpr .r11 = O + BitVec.ofNat 64 2) (h7 : t₀.gpr .r7 = BitVec.ofNat 64 (k - 2))
    (h4 : t₀.gpr .r4 = BitVec.ofNat 64 2) (h5 : t₀.gpr .r5 = 0) (h3 : t₀.gpr .r3 = 0)
    (h0 : t₀.gpr .r0 = 0) (h8 : t₀.gpr .r8 = BitVec.allOnes 64) :
    WP isa scanLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t₀ u ∧
      u.gpr .r5 = bm (firstZero EM k).isSome ∧ u.gpr .r3 = BitVec.ofNat 64 ((firstZero EM k).getD 0) := by
  refine (VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := k - 2) (by omega_using [hk2]) (by omega_using [hk])
    (fun j u => u.mem = t₀.mem ∧ Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t₀ u ∧
      u.gpr .r11 = O + BitVec.ofNat 64 (2 + j) ∧ u.gpr .r4 = BitVec.ofNat 64 (2 + j) ∧
      u.gpr .r5 = bm (firstZero EM (2 + j)).isSome ∧ u.gpr .r3 = BitVec.ofNat 64 ((firstZero EM (2 + j)).getD 0))
    (fun j hj u ⟨um, ku, u11, u4, u5, u3⟩ _ => ?_)
    ⟨rfl, Keep.refl _ _, h11, h4, by rw [h5]; rfl, by rw [h3]; rfl⟩ h7).mono
    fun u ⟨um, ku, _, _, u5, u3⟩ => by
      rw [show 2 + (k - 2) = k by omega_using [hk]] at u5 u3
      exact ⟨um, ku, u5, u3⟩
  have hr0 := hr (2 + j) (by omega_using [hj])
  rw [← ku.rd, ← ku.wr] at hr0
  have hb : u.mem (u.gpr .r11 + BitVec.ofNat 64 0) = EM.getD (2 + j) 1 := by
    rw [u11, BitVec.add_zero, um, hEM _ (by omega_using [hj])]
  refine WP.mono (scanBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) ((ku.gpr _ (by decide)).trans h0)
    ((ku.gpr _ (by decide)).trans h8))
    fun w ⟨⟨wm, w11, w7, w4, w5, w3⟩, kw⟩ => ⟨⟨wm.trans um, ku.trans' kw, by rw [w11, u11, Offset.add_add]; rfl,
      by rw [w4, u4, ← BitVec.ofNat_add]; rfl, ?_, ?_⟩, w7⟩
  · rw [w5, u5, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i => simp only [Option.isSome_some, bm, ite_true, BitVec.allOnes_or]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, bm, hz, decide_true, Bool.false_eq_true, ite_true, ite_false,
          Option.isSome_some]
        rfl
      · simp only [Option.isSome_none, bm, hz, decide_false, Bool.false_eq_true, ite_false]
        rfl
  · rw [w3, u3, u5, u4, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i =>
      simp only [Option.isSome_some, bm, ite_true, BitVec.xor_self, BitVec.zero_and, BitVec.or_zero,
        Option.getD_some]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, hz, decide_true, ite_true, Option.getD_none, Option.getD_some]
        exact r3_pos _
      · simp only [Option.isSome_none, hz, decide_false, ite_false, Option.getD_none]
        exact r3_neg _

theorem bytes_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

/-- After the scan. -/
structure SCN (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  al : t.gpr .r6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))
  r5 : t.gpr .r5 = bm (firstZero EM (s.gpr .r7).toNat).isSome
  r3 : t.gpr .r3 = BitVec.ofNat 64 ((firstZero EM (s.gpr .r7).toNat).getD 0)
  r0 : t.gpr .r0 = 0
  r8 : t.gpr .r8 = BitVec.allOnes 64

/-- A byte of `out` is accessible. -/
theorem outIn {t : State} (hc : Post s R EM t) {i : Nat} (hi : i < (s.gpr .r7).toNat) :
    InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h4] at this
  exact ⟨oR s, by rw [hc.wr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem scanPart_ok {t : State} (hl : AL s R EM kd t) : WP isa scanPart t (SCN s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hl.amr.post
  have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  have e7 : s.gpr .r7 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hk64]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r4, .r5, .r3, .r0, .r8]
    (Q := fun u => u.mem = t.mem ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
      u.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ u.gpr .r4 = BitVec.ofNat 64 2 ∧ u.gpr .r5 = 0 ∧
      u.gpr .r3 = 0 ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64) ?_ rfl)
    fun t₁ ⟨⟨m₁, x11, x7, x4, x5, x3, x0, x8⟩, k₁⟩ => ?_)
  · unfold scanInit
    prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, e7,
      exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide),
      exec_subi (show Reg.r7 ≠ .r0 by decide) (show 2 ≤ 2 ^ 15 by decide),
      exec_subi (show Reg.r8 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]
    exact ⟨rfl, rfl, rfl, by decide⟩
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  refine WP.mono (scanLoop_ok (O := s.gpr .r3) (EM := EM) (k := (s.gpr .r7).toNat) (by omega_using [hk64]) (by omega_using [hk])
    (fun i hi => by rw [← hc₁.em, bytes_getD' _ _ hi]) (fun i hi => outIn h hc₁ hi) x11 x7 x4 x5 x3 x0 x8)
    fun u ⟨um, ku, u5, u3⟩ => ⟨hl.amr.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁),
      by rw [ku.gpr _ (by decide), k₁.gpr _ (by decide), hl.al], u5, u3, by rw [ku.gpr _ (by decide), x0],
      by rw [ku.gpr _ (by decide), x8]⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
