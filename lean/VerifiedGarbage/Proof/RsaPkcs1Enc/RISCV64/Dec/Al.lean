module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Irprf
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the alternative length

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecAl.lean`): the mask of the candidates,
`bitMask (k - 11)`, by doublings (`maskPart_ok`), and the alternative length,
the last masked candidate of `CL` not above `k - 11` (`alPart_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
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

theorem maskBody_ok {t : State} :
    WP isa (.block [.add .t4 .t4 .t4, .addi .t4 .t4 1, .sub .t5 .t4 .t3, .shift .srl .d .t5 .t5 63]) t
      fun u => Only [.t4, .t5] t u ∧ u.gpr .t4 = t.gpr .t4 + t.gpr .t4 + BitVec.ofNat 64 1 ∧
        u.gpr .t5 = (t.gpr .t4 + t.gpr .t4 + BitVec.ofNat 64 1 - t.gpr .t3) >>> 63 :=
  wp_add fun v₁ p₁ f₁ => wp_addi (imm := 1) (fun v₂ p₂ f₂ => wp_sub fun v₃ p₃ f₃ => wp_srl (sh := 63)
    fun v₄ p₄ f₄ => wp_nil ⟨(p₁.trans (p₂.trans (p₃.trans p₄))).mono, by rw [p₄.get .t4, p₃.get .t4, f₂, f₁],
      by rw [f₄, f₃, f₂, f₁, p₂.get .t3, p₁.get .t3]⟩) (by decide)

theorem dbl (p : Nat) (h1 : 1 ≤ p) (h : p * 2 < 2 ^ 34) :
    BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (p * 2 - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An iteration of the mask's loop: `2 ^ j - 1` to `2 ^ (j + 1) - 1`, and whether to go on. -/
theorem maskStep_ok {x j : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (hj : j < Spec.RsaPkcs1Enc.bitLength x)
    {u : State} (hu4 : u.gpr .t4 = BitVec.ofNat 64 (2 ^ j - 1)) (hu3 : u.gpr .t3 = BitVec.ofNat 64 x) :
    WP isa (.block [.add .t4 .t4 .t4, .addi .t4 .t4 1, .sub .t5 .t4 .t3, .shift .srl .d .t5 .t5 63]) u
      fun w => (Only [.t4, .t5] u w ∧ w.gpr .t4 = BitVec.ofNat 64 (2 ^ (j + 1) - 1)) ∧
        ((w.gpr .t5).toNat ≠ 0 ↔ j + 1 ≠ Spec.RsaPkcs1Enc.bitLength x) := by
  have hlt := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega) hj
  have hpj : 2 ^ (j + 1) < 2 ^ 34 := by
    rw [Nat.pow_succ]; generalize 2 ^ j = p at *; omega
  have e8 : BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ ..] at hpj ⊢
    exact dbl _ Nat.one_le_two_pow hpj
  refine WP.mono maskBody_ok fun w ⟨kw, w4, w5⟩ => ⟨⟨kw, by rw [w4, hu4, e8]⟩, ?_⟩
  rw [w5, hu4, hu3, e8, borrow _ _ (by omega) (by omega), BitVec.toNat_ofNat]
  by_cases he : j + 1 = Spec.RsaPkcs1Enc.bitLength x
  · have h1 := Proof.RsaPkcs1Enc.bitMask_ge (x := x) (by omega)
    rw [he]
    simp only [show x ≤ 2 ^ Spec.RsaPkcs1Enc.bitLength x - 1 from h1, ↓reduceIte]; omega
  · have h1 := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j + 1) (by omega) (by omega)
    simp only [show ¬ x ≤ 2 ^ (j + 1) - 1 by omega, ↓reduceIte]; omega

theorem bitLength_pos {x : Nat} (hx1 : 1 ≤ x) : 0 < Spec.RsaPkcs1Enc.bitLength x := by
  simp only [Spec.RsaPkcs1Enc.bitLength]; split <;> omega

theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h4 : t₀.gpr .t4 = BitVec.ofNat 64 0)
    (h3 : t₀.gpr .t3 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun u => Only [.t4, .t5] t₀ u ∧ u.gpr .t4 = BitVec.ofNat 64 (bitMask x) :=
  VG.Proof.Bignum.RISCV64.count_loop (bitLength_pos hx1) (fun j u => Only [.t4, .t5] t₀ u ∧
    u.gpr .t4 = BitVec.ofNat 64 (2 ^ j - 1))
    (fun _ hj u ⟨hk, hu4⟩ => WP.mono (maskStep_ok hx1 hx hj hu4
      (by rw [hk.get .t3, h3])) fun _ ⟨⟨kw, w4⟩, w5⟩ => ⟨⟨(hk.trans kw).mono, w4⟩, w5⟩)
    ⟨Only.refl _ _, h4⟩

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

/-- The candidate at `t1`, masked by `t4`. -/
abbrev cand (t : State) : BitVec 64 :=
  ((t.mem (t.gpr .t1 + BitVec.ofNat 64 0)).setWidth 64 <<< 8 +
    (t.mem (t.gpr .t1 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .t4

theorem alBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .t1 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (t.gpr .t1 + BitVec.ofNat 64 1) 1) :
    WP isa (.block alBody) t fun u => Only [.a0, .a1, .a2, .t6, .t1, .t2] t u ∧
      u.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 2 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
      u.gpr .t6 = t.gpr .t6 ^^^ ((t.gpr .t6 ^^^ cand t) &&& (((t.gpr .t3 - cand t) >>> 63) - BitVec.ofNat 64 1)) := by
  unfold alBody
  refine wp_lbu rfl h0 fun v₁ p₁ f₁ => wp_sll (sh := 8) fun v₂ p₂ f₂ =>
    wp_lbu (a := t.gpr .t1 + BitVec.ofNat 64 1) (by rw [p₂.get .t1, p₁.get .t1])
      (by rw [p₂.rd, p₂.wr, p₁.rd, p₁.wr]; exact h1) fun v₃ p₃ f₃ =>
    wp_add fun v₄ p₄ f₄ => wp_and fun v₅ p₅ f₅ => wp_sub fun v₆ p₆ f₆ => wp_srl (sh := 63) fun v₇ p₇ f₇ =>
    wp_subi (imm := 1) (fun v₈ p₈ f₈ => wp_xor fun v₉ p₉ f₉ => wp_and fun v₁₀ p₁₀ f₁₀ =>
    wp_xor fun v₁₁ p₁₁ f₁₁ => wp_addi (imm := 2) (fun v₁₂ p₁₂ f₁₂ => wp_subi (imm := 1) (fun v₁₃ p₁₃ f₁₃ =>
      wp_nil ?_) (by decide)) (by decide)) (by decide)
  have O₁ : Only [.a0, .a1, .a2, .t6, .t1, .t2] t v₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  have O₂ : Only [.a0, .a1, .a2, .t6, .t1, .t2] v₅ v₉ := (p₆.trans (p₇.trans (p₈.trans p₉))).mono
  have O₃ : Only [.a0, .a1, .a2, .t6, .t1, .t2] v₉ v₁₃ := (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃))).mono
  have O : Only [.a0, .a1, .a2, .t6, .t1, .t2] t v₁₃ := (O₁.trans (O₂.trans O₃)).mono
  have c : v₅.gpr .a0 = cand t := by
    rw [f₅, f₄, p₃.get .a0, f₂, f₁, f₃, p₂.mem, p₁.mem, p₄.get .t4, p₃.get .t4, p₂.get .t4, p₁.get .t4]
  refine ⟨O, ?_, ?_, ?_⟩
  · rw [p₁₃.get .t1, f₁₂, p₁₁.get .t1, p₁₀.get .t1, p₉.get .t1, p₈.get .t1, p₇.get .t1, p₆.get .t1, p₅.get .t1,
      p₄.get .t1, p₃.get .t1, p₂.get .t1, p₁.get .t1]
  · rw [f₁₃, p₁₂.get .t2, p₁₁.get .t2, p₁₀.get .t2, p₉.get .t2, p₈.get .t2, p₇.get .t2, p₆.get .t2, p₅.get .t2,
      p₄.get .t2, p₃.get .t2, p₂.get .t2, p₁.get .t2]
  · have g6 : v₅.gpr .t6 = t.gpr .t6 := by
      rw [p₅.get .t6, p₄.get .t6, p₃.get .t6, p₂.get .t6, p₁.get .t6]
    have g3 : v₅.gpr .t3 = t.gpr .t3 := by
      rw [p₅.get .t3, p₄.get .t3, p₃.get .t3, p₂.get .t3, p₁.get .t3]
    rw [p₁₃.get .t6, p₁₂.get .t6, f₁₁, f₁₀, f₉, p₉.get .a1, f₈, f₇, f₆, p₁₀.get .t6, p₉.get .t6, p₈.get .t6,
      p₇.get .t6, p₆.get .t6, p₈.get .a0, p₇.get .a0, p₆.get .a0, g6, g3, c]

theorem bytes_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem alLoop_ok {t₀ : State} {x M : Nat} {CL : List Byte} {B : Addr}
    (hx : x < 2 ^ 32) (hM : M = bitMask x) (hMl : M < 2 ^ 32)
    (hm : ∀ i < 256, t₀.mem (B + BitVec.ofNat 64 i) = CL.getD i 0)
    (hr : ∀ i < 256, InRegions (t₀.rd ++ t₀.wr) (B + BitVec.ofNat 64 i) 1)
    (h4 : t₀.gpr .t4 = BitVec.ofNat 64 M) (h3 : t₀.gpr .t3 = BitVec.ofNat 64 x) (h1 : t₀.gpr .t1 = B)
    (h2 : t₀.gpr .t2 = BitVec.ofNat 64 128) (h6 : t₀.gpr .t6 = 0) :
    WP isa alLoop t₀ fun u => Only [.a0, .a1, .a2, .t6, .t1, .t2] t₀ u ∧
      u.gpr .t6 = BitVec.ofNat 64 ((List.range 128).foldl (altStep (x + 11) CL) 0) := by
  refine VG.Proof.Bignum.RISCV64.wp_countdown (cnt := .t2) (N := 128) (by decide) (by decide)
    (fun j u => Only [.a0, .a1, .a2, .t6, .t1, .t2] t₀ u ∧ u.gpr .t1 = B + BitVec.ofNat 64 (2 * j) ∧
      u.gpr .t6 = BitVec.ofNat 64 ((List.range j).foldl (altStep (x + 11) CL) 0))
    (fun j hj u ⟨ku, u1, u6⟩ _ => ?_) ⟨Only.refl _ _, by rw [h1]; exact (BitVec.add_zero _).symm, h6⟩
    h2 |>.mono fun u ⟨a, _, c⟩ => ⟨a, c⟩
  have hr0 := hr (2 * j) (by omega)
  have hr1 := hr (2 * j + 1) (by omega)
  rw [← ku.rd, ← ku.wr] at hr0 hr1
  have u4 : u.gpr .t4 = BitVec.ofNat 64 M := (ku.get .t4).trans h4
  have u3 : u.gpr .t3 = BitVec.ofNat 64 x := (ku.get .t3).trans h3
  refine WP.mono (alBody_ok (by rw [u1, Offset.add_add]; exact hr0) (by rw [u1, Offset.add_add]; exact hr1))
    fun w ⟨kw, w1, w2, w6⟩ => ⟨⟨(ku.trans kw).mono, by rw [w1, u1, Offset.add_add, show 2 * j + 2 = 2 * (j + 1) by omega], ?_⟩, w2⟩
  rw [w6, u6]
  unfold cand
  rw [u4, u3, u1, Offset.add_add, Offset.add_add, Nat.add_zero (2 * j), ku.mem, hm _ (by omega), hm _ (by omega),
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

/-- `AMR` is kept by code writing only registers it does not keep. -/
theorem AMR.only {t u : State} (hl : AMR s R EM kd t) {rs : List Reg} (o : Only rs t u)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : AMR s R EM kd u :=
  ⟨hl.toPost.keep h o.keep (ws := []) (by rw [o.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr) hrs h7,
    by rw [o.mem]; exact hl.cl, by rw [o.mem]; exact hl.am⟩

/-- After the mask: `bitMask (k - 11)` in `t4` and `k - 11` in `t3`. -/
structure MK (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends AMR s R EM kd t where
  t4 : t.gpr .t4 = BitVec.ofNat 64 (bitMask ((s.gpr .a4).toNat - 11))
  t3 : t.gpr .t3 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 11)

theorem maskPart_ok {t : State} (hl : AMR s R EM kd t) : WP isa maskPart t (MK s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold maskPart maskInit
  refine WP.seq (wp_subi (imm := 11) (fun v₁ p₁ f₁ => wp_li (imm := 0) (by decide) fun t₁ p₂ f₂ =>
    wp_nil ?_) (by decide))
  have O : Only [.t3, .t4] t t₁ := (p₁.trans p₂).mono
  have e3 : t₁.gpr .t3 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 11) := by
    rw [p₂.get .t3, f₁, hl.s1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact WP.mono (maskLoop_ok (x := (s.gpr .a4).toNat - 11) (by omega) (by omega) f₂ e3) fun u ⟨ku, u4⟩ =>
    ⟨(hl.only h O).only h ku, u4, (ku.get .t3).trans e3⟩

/-- `CL`. -/
abbrev clOf (kd : List Byte) : List Byte := Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After the alternative length. -/
structure AL (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends AMR s R EM kd t where
  al : t.gpr .t6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd))
  t3 : t.gpr .t3 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 11)

theorem alPart_ok {t : State} (hm : MK s R EM kd t) : WP isa alPart t (AL s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold alPart alInit
  refine WP.seq (wp_addi (imm := sCL) (fun v₁ p₁ f₁ => wp_li (imm := 128) (by decide) fun v₂ p₂ f₂ =>
    wp_li (imm := 0) (by decide) fun t₁ p₃ f₃ => wp_nil ?_) (by decide))
  have O : Only [.t1, .t2, .t6] t t₁ := (p₁.trans (p₂.trans p₃)).mono
  have P₁ := hm.toAMR.only h O
  have hcl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = clOf kd := hm.cl
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .a4).toNat - 11) (by omega)
  refine WP.mono (alLoop_ok (x := (s.gpr .a4).toNat - 11) (M := bitMask ((s.gpr .a4).toNat - 11)) (CL := clOf kd)
    (B := scA s sCL) (by omega) rfl (by omega)
    (fun i hi => by rw [← hcl, bytes_getD _ _ hi, O.mem])
    (fun i hi => by
      rw [Offset.add_add]
      obtain ⟨r, hr, hc⟩ := scIn h P₁.wr (a := sCL + i) (l := 1) (by unfold sCL scrBytes; omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [O.get .t4, hm.t4]) (by rw [O.get .t3, hm.t3])
    (by rw [p₃.get .t1, p₂.get .t1, f₁, hm.s0]) (by rw [p₃.get .t2, f₂]) f₃) fun u ⟨ku, u6⟩ =>
    ⟨P₁.only h ku, by rw [u6, Nat.sub_add_cancel (by omega)]; rfl, by rw [ku.get .t3, O.get .t3, hm.t3]⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
