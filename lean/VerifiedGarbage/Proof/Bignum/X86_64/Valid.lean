import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.Positivity
import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Framework.WriteBytes
import Mathlib.Data.Int.ModEq

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Double`. -/
section

/-!
# Multiword arithmetic on x86-64: doubling modulo `m`

`double mo acc tmp o`: `[o] := 2 [o] mod m` for `[o] < m` (`double_ok`): the
double into the accumulator (`w + 1` words, the carry chain's carry kept in
`rbp` as in `subMod`), then `subMod` and `selectAcc`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `adc`, as numbers. -/
theorem adc_toNat (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat + 2 ^ 64 *
      (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, hc]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- After `j` words of `double`'s loop: `A_j + 2^(64 j) c = 2 O_j`. -/
structure DblInv (s₀ : State) (B : Addr) (Z eA eo : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
    wv t.mem B eA j + 2 ^ (64 * j) * c.toNat = 2 * wv s₀.mem B eo j

theorem dblStep_ok {s₀ : State} {B : Addr} {Z w eA eo : Nat}
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) {j : Nat} (hj : j < w) {t : State}
    (hI : VG.Proof.Bignum.X86_64.DblInv s₀ B Z eA eo j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax),
        .store (ix .r8 .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.DblInv s₀ B Z eA eo (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = 2 * (VG.Proof.Bignum.X86_64.word t.mem B (eo + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tbx hI.r14, hbp, cf_mask,
      hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    rw [VG.Proof.Bignum.X86_64.adc_toNat]
    show (VG.Proof.Bignum.X86_64.word t.mem B (eo + 8 * j)).toNat + (VG.Proof.Bignum.X86_64.word t.mem B (eo + 8 * j)).toNat + c.toNat = _
    omega
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eo + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `[o] := 2 [o] mod m`, for `[o] < m = [mo]`. -/
theorem double_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hO : wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) :
    WP isa (double mo acc tmp o) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = 2 * wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w % wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w k ∨ VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold double
  refine WP.seq (WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w mo) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w tmp) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧
      t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr o) (by unfold sArr; omega),
      hl (sArr mo) (by unfold sArr; omega), hl (sArr acc) (by unfold sArr; omega), hl sW (by decide),
      hl (sArr tmp) (by unfold sArr; omega), hH.harr o ho, hH.harr mo hmo, hH.harr acc hacc,
      hH.harr tmp htmp, hH.hw]) rfl)
    fun s₁ ⟨⟨hbx, h10, h8, h12, hsi₁, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.DblInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w acc) (VG.Proof.Bignum.X86_64.slot w o) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (VG.Proof.Bignum.X86_64.DblInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w acc) (VG.Proof.Bignum.X86_64.slot w o)) h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.dblStep_ok h8 hbx h12 (by omega) (by have := sl acc hacc; omega)
      (by have := sl o ho; omega) (by have := sp (Ne.symm d3); omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w acc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = B := ((k₁.trans hI.keep).gpr (by decide)).trans hdi
  have s₂si : s₂.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w tmp) := (hI.keep.gpr (by decide)).trans hsi₁
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w tmp) ∧
      ∃ v : BitVec 64, v.toNat = c.toNat ∧ t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w acc + 8 * w)) v)
    (by
      unfold cfFromRbp
      xrun [State.ea, ix, s₂si, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show VG.Proof.Bignum.X86_64.slot w acc + 8 * w + 8 ≤ Z by have := sl acc hacc; omega), sx0]
      refine ⟨_, ?_, rfl⟩
      cases c <;> rfl) rfl) fun s₃ ⟨⟨hsi, v, hv, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := (hI.keep.trans k₃)
  have o3 : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w acc) (8 * (w + 1)) s₁.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B v (by have := sl acc hacc; omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₁] at o3
  have fN : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w mo) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w :=
    o3.wv (by have := sp (Ne.symm d1); omega) (by have := sl mo hmo; omega)
  have fO : wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w o) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w := by rw [hm₁]
  have hTl : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w acc) w := by
    rw [hm₃]; exact (VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B v (by have := sl acc hacc; omega)).wv (Or.inl (by omega))
      (by have := sl acc hacc; omega)
  have hTw : (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc + 8 * w)).toNat = c.toNat := by
    rw [hm₃, VG.Proof.Bignum.X86_64.word_writeW_self, hv]
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans h10)
    hsi ((k13.gpr (by decide)).trans h12) (by omega) hw' (by have := sl acc hacc; omega)
    (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega) (by have := sp d2; omega)
    (by have := sp d6; omega)) fun s₄ ⟨c', lt, hbp', hlt, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr (by decide)).trans h8) ((k₄.gpr (by decide)).trans hsi)
    ((k14.gpr (by decide)).trans hbx) ((k14.gpr (by decide)).trans h12) hbp' (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w acc) w = wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) w :=
    ho₄.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  rw [fN] at hD
  rw [fO] at hval
  have hN0 : 0 < wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w := by omega
  refine ⟨?_, ?_, ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · rw [hv', hacc₄, hlt, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) w) (Tw := c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w tmp) w) (m := wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : c.toNat < c'.toNat <;> simp [h, hTl]
  · have a3 : Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) o3 (Nat.le_refl _) (by omega)
    have a4 : Arrays B w [acc, tmp, o] s₃.mem s₄.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₄ (Nat.le_refl _) (by omega)
    have a5 : Arrays B w [acc, tmp, o] s₄.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a4).trans a5

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Bytes`. -/
section

/-!
# Multiword arithmetic on x86-64: bytes and words

`loadBE` reads `k` bytes, most significant first, into the `⌈k / 8⌉` words of
an array: as a number, OS2IP of the bytes (`loadBE_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide

theorem and7_eq (p : Nat) (hp : p < 2 ^ 64) : (BitVec.ofNat 64 p &&& 7 == 0) = decide (p % 8 = 0) := by
  have h : (BitVec.ofNat 64 p &&& 7).toNat = p % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
      show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h0 : p % 8 = 0
  · simp only [h0, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, h0]; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; rw [← h, he]; rfl

theorem shr3_eq (p : Nat) (hp : p < 2 ^ 64) : BitVec.ofNat 64 p >>> 3 = BitVec.ofNat 64 (p / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem test_eq (x : BitVec 64) : (x &&& x == 0) = (x == 0) := by rw [BitVec.and_self]

theorem ror56_toNat (x : BitVec 64) (h : x.toNat < 2 ^ 56) : (x.rotateRight 56).toNat = x.toNat * 256 := by
  rw [BitVec.toNat_rotateRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.div_eq_of_lt (by simpa using h), Nat.zero_or]
  simp only [show 56 % 64 = 56 from rfl, show 64 - 56 = 8 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- `loadByte`: `p := p - 1`, `rax := 256 rax + byte`, `r14 += 1`, ZF iff
`8 ∣ p - 1`. -/
theorem loadByte_ok {t : State} {p : Nat} {a : Addr} {b : Byte} (hp1 : 1 ≤ p) (hp : p < 2 ^ 63)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 p) (hax : (t.gpr .rax).toNat < 2 ^ 56) (h14 : t.gpr .r14 = a)
    (ha : InRegions (t.rd ++ t.wr) a 1) (hb : t.mem a = b) :
    WP isa (.block loadByte) t fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (p - 1) ∧ (t'.gpr .rax).toNat = (t.gpr .rax).toNat * 256 + b.toNat ∧
      t'.gpr .r14 = a + 1 ∧ t'.zf = some (decide ((p - 1) % 8 = 0)) ∧ t'.mem = t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] t t' := by
  have hpred : BitVec.ofNat 64 p - 1 = BitVec.ofNat 64 (p - 1) := ofNat64_pred hp1 (by omega)
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r14] (c := .block loadByte) (Q := fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (p - 1) ∧ (t'.gpr .rax).toNat = (t.gpr .rax).toNat * 256 + b.toNat ∧
      t'.gpr .r14 = a + 1 ∧ t'.zf = some (decide ((p - 1) % 8 = 0)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold loadByte
  xrun [State.ea, at0, hdx, h14, hpred, ha, hb, VG.Proof.Bignum.X86_64.sx7, VG.Proof.Bignum.X86_64.and7_eq (p - 1) (by omega),
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  rw [BitVec.toNat_add, VG.Proof.Bignum.X86_64.ror56_toNat _ hax, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (b := 2 ^ 64)
    (by have := b.isLt; omega), Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- `storeWord`: `rax` as word `p / 8` of the array at `rbx = B + ed`. -/
theorem storeWord_ok {t : State} {B : Addr} {Z ed p : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hp : p < 2 ^ 63)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 p) (hbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed) (hed : ed + 8 * (p / 8) + 8 ≤ Z) :
    WP isa (.block storeWord) t fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (ed + 8 * (p / 8))) (t.gpr .rax) ∧ t'.gpr .rax = 0 ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbp] t t' := by
  refine WP.mono (WP.keep [.rax, .rbp] (c := .block storeWord) (Q := fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (ed + 8 * (p / 8))) (t.gpr .rax) ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold storeWord
  xrun [State.ea, ix, hdx, VG.Proof.Bignum.X86_64.shr3_eq p (by omega), addr0 hbx rfl, hs.st hed]

/-! ## The loop of `loadBE` -/

/-- OS2IP of the first `i` bytes. -/
def pre (bs : List Byte) (i : Nat) : Nat := Spec.Rsa.os2ip (bs.take i)

theorem pre_succ (bs : List Byte) {i : Nat} (hi : i < bs.length) :
    VG.Proof.Bignum.X86_64.pre bs (i + 1) = 256 * VG.Proof.Bignum.X86_64.pre bs i + (bs[i]).toNat := by
  unfold VG.Proof.Bignum.X86_64.pre Spec.Rsa.os2ip
  rw [← List.take_concat_get hi, List.concat_eq_append, List.foldl_append]
  rfl

theorem pre_zero (bs : List Byte) : VG.Proof.Bignum.X86_64.pre bs 0 = 0 := rfl

theorem pre_len (bs : List Byte) : VG.Proof.Bignum.X86_64.pre bs bs.length = Spec.Rsa.os2ip bs := by
  unfold VG.Proof.Bignum.X86_64.pre; rw [List.take_length]

theorem pow256 (a : Nat) : (256 : Nat) ^ (8 * a) = 2 ^ (64 * a) := by
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

/-- Words that are the base-`2⁶⁴` digits of `V` make `V mod 2^(64 n)`. -/
theorem wv_digits {m : Mem} {B : Addr} {ed V : Nat} (n : Nat)
    (h : ∀ q < n, VG.Proof.Bignum.X86_64.word m B (ed + 8 * q) = BitVec.ofNat 64 (V / 256 ^ (8 * q))) :
    wv m B ed n = V % 2 ^ (64 * n) := by
  induction n with
  | zero => simp [wv, Nat.mod_one]
  | succ n ih =>
    rw [wv, ih fun q hq => h q (by omega), h n (by omega), BitVec.toNat_ofNat, VG.Proof.Bignum.X86_64.pow256,
      show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add, Nat.mod_mul]

/-- After `i` bytes of `loadBE` from `s₀`, with `p = k - i` bytes left. -/
structure LInv (s₀ : State) (B : Addr) (Z ed k w : Nat) (src : Addr) (bs : List Byte) (i : Nat)
    (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s₀ t
  rdx : t.gpr .rdx = BitVec.ofNat 64 (k - i)
  r14 : t.gpr .r14 = src + BitVec.ofNat 64 i
  rax : (t.gpr .rax).toNat = VG.Proof.Bignum.X86_64.pre bs i % 256 ^ ((8 - (k - i) % 8) % 8)
  words : ∀ q < w, k - i ≤ 8 * q → VG.Proof.Bignum.X86_64.word t.mem B (ed + 8 * q) = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.pre bs i / 256 ^ (8 * q - (k - i)))
  out : VG.Proof.Bignum.X86_64.Outside B ed (8 * w) s₀.mem t.mem

theorem loadStep_ok {s₀ : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hk : bs.length = k) (hk' : k < 2 ^ 31) (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < k), s₀.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, VG.Proof.Bignum.X86_64.ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ VG.Proof.Bignum.X86_64.ofs B (src + BitVec.ofNat 64 i))
    {i : Nat} (hi : i < k) {t : State} (hI : VG.Proof.Bignum.X86_64.LInv s₀ B Z ed k w src bs i t) :
    WP isa (.seq (.block loadByte) (.seq (.ite .e (.block storeWord) (.block []))
      (.block [.alu .test .rdx (.reg .rdx)]))) t fun t' =>
      t'.zf = some (decide (i + 1 = k)) ∧ VG.Proof.Bignum.X86_64.LInv s₀ B Z ed k w src bs (i + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed := (hI.keep.gpr (by decide)).trans hbx
  have hr7 : (8 - (k - i) % 8) % 8 ≤ 7 := by omega
  have hax : (t.gpr .rax).toNat < 2 ^ 56 := by
    rw [hI.rax]
    have : 256 ^ ((8 - (k - i) % 8) % 8) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) hr7
    have := Nat.mod_lt (VG.Proof.Bignum.X86_64.pre bs i) (show 0 < 256 ^ ((8 - (k - i) % 8) % 8) by positivity)
    have : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
    omega
  have hb : t.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega) := by
    rw [hI.out _ (hsep i hi)]; exact hbytes i hi
  have hld : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hsrc i hi
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.loadByte_ok (p := k - i) (by omega) (by omega) hI.rdx hax hI.r14 hld hb)
    fun t₁ ⟨hdx₁, hax₁, h14₁, hz₁, hm₁, k₁⟩ => ?_)
  have hpre := VG.Proof.Bignum.X86_64.pre_succ bs (i := i) (by omega)
  -- The new partial word.
  have hax₁' : (t₁.gpr .rax).toNat = VG.Proof.Bignum.X86_64.pre bs (i + 1) % 256 ^ ((8 - (k - i) % 8) % 8 + 1) := by
    rw [hax₁, hI.rax, hpre, VG.Proof.Bignum.bytes_mod_step _ _ _ (bs[i]'(by omega)).isLt]
    grind
  have hs₁ := hI.scr.congr k₁.2.2
  have tbx₁ : t₁.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed := (k₁.gpr (by decide)).trans tbx
  -- The old words, one byte on.
  have hwords : ∀ q < w, k - i ≤ 8 * q → VG.Proof.Bignum.X86_64.word t.mem B (ed + 8 * q) =
      BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.pre bs (i + 1) / 256 ^ (8 * q - (k - (i + 1)))) := by
    intro q hq hle
    rw [hI.words q hq hle, hpre, show 8 * q - (k - (i + 1)) = 8 * q - (k - i) + 1 by omega,
      VG.Proof.Bignum.bytes_div_step _ _ _ (bs[i]'(by omega)).isLt]
  by_cases hz : (k - i - 1) % 8 = 0
  · -- A word is complete: it is stored.
    refine WP.seq (WP.ite true (by simp [VG.X86_64.eval, hz₁, hz]) (fun _ => ?_) (by simp))
    refine WP.mono (VG.Proof.Bignum.X86_64.storeWord_ok hs₁ (p := k - i - 1) (by omega) hdx₁ tbx₁ (by omega))
      fun t₂ ⟨hm₂, hax₂, k₂⟩ => ?_
    refine WP.mono (WP.keep [.rdx] (c := .block [.alu .test .rdx (.reg .rdx)])
      (Q := fun t' => t'.zf = some (decide (i + 1 = k)) ∧ t'.mem = t₂.mem ∧
        t'.gpr .rdx = BitVec.ofNat 64 (k - i - 1)) (by
        xrun [(k₂.gpr (by decide) : t₂.gpr .rdx = t₁.gpr .rdx), hdx₁, VG.Proof.Bignum.X86_64.test_eq,
          ofNat64_beq_zero (show k - i - 1 < 2 ^ 64 by omega)]
        exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩) rfl)
      fun t' ⟨⟨hz', hm', hdx'⟩, k'⟩ => ⟨hz', ?_⟩
    refine ⟨hs₁.congr (k'.2.2.trans k₂.2.2), ((hI.keep.trans k₁).trans (k₂.trans k')).mono (by decide),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdx']; congr 1
    · rw [(k'.gpr (by decide) : t'.gpr .r14 = t₂.gpr .r14), (k₂.gpr (by decide) : t₂.gpr .r14 = t₁.gpr .r14),
        h14₁, BitVec.add_assoc, ofNat_add_one]
    · rw [(k'.gpr (by decide) : t'.gpr .rax = t₂.gpr .rax), hax₂,
        show (8 - (k - (i + 1)) % 8) % 8 = 0 by omega, Nat.pow_zero, Nat.mod_one]; rfl
    · intro q hq hle
      rw [hm', hm₂, hm₁]
      by_cases hq' : 8 * q = k - i - 1
      · have : q = (k - i - 1) / 8 := by omega
        subst this
        rw [VG.Proof.Bignum.X86_64.word_writeW_self, show 8 * ((k - i - 1) / 8) - (k - (i + 1)) = 0 by omega, Nat.pow_zero,
          Nat.div_one]
        apply BitVec.eq_of_toNat_eq
        rw [hax₁', BitVec.toNat_ofNat, show (8 - (k - i) % 8) % 8 + 1 = 8 by omega,
          VG.Proof.Bignum.pow256_8]
      · rw [(VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]
        exact hwords q hq (by omega)
    · rw [hm', hm₂, hm₁]
      intro x hx
      rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega) x (by omega)]
      exact hI.out x hx
  · -- No word is complete.
    refine WP.seq (WP.ite false (by simp [VG.X86_64.eval, hz₁, hz]) (by simp) (fun _ => WP.block_nil ?_))
    refine WP.mono (WP.keep [.rdx] (c := .block [.alu .test .rdx (.reg .rdx)])
      (Q := fun t' => t'.zf = some (decide (i + 1 = k)) ∧ t'.mem = t₁.mem ∧
        t'.gpr .rdx = BitVec.ofNat 64 (k - i - 1)) (by
        xrun [hdx₁, VG.Proof.Bignum.X86_64.test_eq, ofNat64_beq_zero (show k - i - 1 < 2 ^ 64 by omega)]
        exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩) rfl)
      fun t' ⟨⟨hz', hm', hdx'⟩, k'⟩ => ⟨hz', ?_⟩
    refine ⟨hs₁.congr k'.2.2, ((hI.keep.trans k₁).trans k').mono (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdx']; congr 1
    · rw [(k'.gpr (by decide) : t'.gpr .r14 = t₁.gpr .r14), h14₁, BitVec.add_assoc, ofNat_add_one]
    · rw [(k'.gpr (by decide) : t'.gpr .rax = t₁.gpr .rax), hax₁',
        show (8 - (k - i) % 8) % 8 + 1 = (8 - (k - (i + 1)) % 8) % 8 by omega]
    · intro q hq hle
      rw [hm', hm₁]
      exact hwords q hq (by omega)
    · rw [hm', hm₁]; exact hI.out

theorem pre_lt (bs : List Byte) {i : Nat} (hi : i ≤ bs.length) : VG.Proof.Bignum.X86_64.pre bs i < 256 ^ i := by
  induction i with
  | zero => exact Nat.one_pos
  | succ i ih =>
    rw [VG.Proof.Bignum.X86_64.pre_succ bs (by omega), Nat.pow_succ]
    have := ih (by omega)
    have := (bs[i]'(by omega)).isLt
    omega

/-- `loadBE`: the `k` bytes at `rsi`, most significant first, as the
`w = ⌈k / 8⌉` words of the array at `rbx`. -/
theorem loadBE_ok {s : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hsi : s.gpr .rsi = src) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed) (hk : bs.length = k) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < k), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, VG.Proof.Bignum.X86_64.ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ VG.Proof.Bignum.X86_64.ofs B (src + BitVec.ofNat 64 i)) :
    WP isa loadBE s fun t =>
      wv t.mem B ed w = Spec.Rsa.os2ip bs ∧ VG.Proof.Bignum.X86_64.Outside B ed (8 * w) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s t := by
  unfold loadBE
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx, .r14] (Q := fun t => t.gpr .rax = 0 ∧
      t.gpr .rdx = BitVec.ofNat 64 k ∧ t.gpr .r14 = src ∧ t.mem = s.mem) (by xrun [hcx, hsi]) rfl)
    fun s₁ ⟨⟨hax, hdx, h14, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine wp_upto (a := 0) (N := k) (by omega) (VG.Proof.Bignum.X86_64.LInv s B Z ed k w src bs) ?_
    (fun t hI => ⟨?_, hI.out, hI.keep⟩) ⟨hs₁, k₁.mono (by decide), by rw [hdx, Nat.sub_zero], by
      rw [h14]; exact (BitVec.add_zero src).symm, by rw [hax, VG.Proof.Bignum.X86_64.pre_zero]; rfl,
      fun q hq hle => absurd hle (by omega), by rw [hm₁]; exact Outside.refl _ _ _ _⟩
  · intro i _ hi t hI
    exact VG.Proof.Bignum.X86_64.loadStep_ok hk hk' hw hed hbx hsrc hbytes hsep hi hI
  · rw [VG.Proof.Bignum.X86_64.wv_digits w fun q hq => by rw [hI.words q hq (by omega), Nat.sub_self, Nat.sub_zero],
      ← hk, VG.Proof.Bignum.X86_64.pre_len, Nat.mod_eq_of_lt]
    have := VG.Proof.Bignum.X86_64.pre_lt bs (Nat.le_refl _)
    rw [VG.Proof.Bignum.X86_64.pre_len, hk] at this
    have : (256 : Nat) ^ k ≤ 2 ^ (64 * w) := by
      rw [← VG.Proof.Bignum.X86_64.pow256]; exact Nat.pow_le_pow_right (by decide) (by omega)
    omega

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.CrtArith`. -/
section

/-!
# Multiword arithmetic on x86-64: addition and subtraction modulo `m`

`addMod o a b`: `[o] := [a] + [b] mod m` (`addMod_ok`), as `double` does
for `2 [o]`. `subModArr o a b`: `[o] := [a] - [b] mod m` (`subModArr_ok`):
`subMod`'s loop into the accumulator, then `m` added under the mask of its
borrow.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## Addition -/

/-- After `j` words of `addMod`'s loop: `A_j + 2^(64 j) c = a_j + b_j`. -/
structure AddInv (s₀ : State) (B : Addr) (Z eA ea eb : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
    wv t.mem B eA j + 2 ^ (64 * j) * c.toNat = wv s₀.mem B ea j + wv s₀.mem B eb j

theorem addStep_ok {s₀ : State} {B : Addr} {Z w eA ea eb : Nat}
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B ea) (h9 : s₀.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (sa : ea + 8 * w ≤ eA ∨ eA + 8 * w ≤ ea) (sb : eb + 8 * w ≤ eA ∨ eA + 8 * w ≤ eb)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Bignum.X86_64.AddInv s₀ B Z eA ea eb j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
        .store (ix .r8 .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.AddInv s₀ B Z eA ea eb (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B ea := (hI.keep.gpr (by decide)).trans hbx
  have t9 : t.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb := (hI.keep.gpr (by decide)).trans h9
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat =
          (VG.Proof.Bignum.X86_64.word t.mem B (ea + 8 * j)).toNat + (VG.Proof.Bignum.X86_64.word t.mem B (eb + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tbx hI.r14, addr0 t9 hI.r14, hbp, cf_mask,
      hI.scr.ld (show ea + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eb + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, rfl, VG.Proof.Bignum.X86_64.adc_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (ea + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (ea + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eb + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eb + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, hy] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `[o] := [a] + [b] mod m`, for `[a], [b] < m = [aN]`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aTmp) (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc)
    (hA : wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w)
    (hB : wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w) :
    WP isa (addMod o a b) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = (wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w + wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w) %
        wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, Public.aTmp, o] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w k ∨ VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hacc : Public.aAcc < 8 := by decide
  have htmp : Public.aTmp < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  have d5 : Public.aAcc ≠ Public.aN := by decide
  have d6 : Public.aAcc ≠ Public.aTmp := by decide
  have d7 : Public.aTmp ≠ Public.aN := by decide
  unfold addMod
  refine WP.seq (WP.mono (WP.keep [.rbx, .r9, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aN) ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aTmp) ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide),
      hl sW (by decide), hl (sArr Public.aTmp) (by decide), hH.harr a ha, hH.harr b hb, hH.harr Public.aN hmo,
      hH.harr Public.aAcc hacc, hH.harr Public.aTmp htmp, hH.hw]) rfl)
    fun s₁ ⟨⟨hbx, h9, h10, h8, h12, hsi₁, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.AddInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w Public.aAcc) (VG.Proof.Bignum.X86_64.slot w a) (VG.Proof.Bignum.X86_64.slot w b) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (VG.Proof.Bignum.X86_64.AddInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w Public.aAcc) (VG.Proof.Bignum.X86_64.slot w a) (VG.Proof.Bignum.X86_64.slot w b)) h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.addStep_ok h8 hbx h9 h12 (by omega) (by have := sl _ hacc; omega)
      (by have := sl a ha; omega) (by have := sl b hb; omega) (by have := sp d3; omega)
      (by have := sp d4; omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = B := ((k₁.trans hI.keep).gpr (by decide)).trans hdi
  have s₂si : s₂.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aTmp) := (hI.keep.gpr (by decide)).trans hsi₁
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have ho₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (8 * sArr o) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) := by
    rw [hI.out.word (by have := hdr_lt_slot w Public.aAcc (show sArr o < 32 by unfold sArr; omega); omega) (by
      have := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega); omega), hm₁]
    exact hH.harr o ho
  have hX : ∀ v : BitVec 64, (s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aAcc + 8 * w)) v).readW (VG.Proof.Bignum.X86_64.off B (8 * sArr o)) 64 =
      VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) := fun v => by
    have h1 := hdr_lt_slot w Public.aAcc (show sArr o < 32 by unfold sArr; omega)
    have h2 := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega)
    exact ((VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B v (by have := sl _ hacc; omega)).word (Or.inl (by omega)) (by omega)).trans ho₂
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp, .rbx] (Q := fun t => t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aTmp) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧
      ∃ v : BitVec 64, v.toNat = c.toNat ∧ t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aAcc + 8 * w)) v)
    (by
      unfold cfFromRbp
      xrun [State.ea, ix, hdr, s₂di, hdrOff, s₂si, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show VG.Proof.Bignum.X86_64.slot w Public.aAcc + 8 * w + 8 ≤ Z by have := sl _ hacc; omega), sx0,
        hl₂ (sArr o) (by unfold sArr; omega), hX]
      refine ⟨_, ?_, rfl⟩
      cases c <;> rfl) rfl) fun s₃ ⟨⟨hsi, hbx₃, v, hv, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := (hI.keep.trans k₃)
  have o3 : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) (8 * (w + 1)) s₁.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B v (by have := sl _ hacc; omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₁] at o3
  have fN : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w :=
    o3.wv (by have := sp d5; omega) (by have := sl _ hmo; omega)
  have hTl : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w := by
    rw [hm₃]; exact (VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B v (by have := sl _ hacc; omega)).wv (Or.inl (by omega))
      (by have := sl _ hacc; omega)
  have hTw : (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc + 8 * w)).toNat = c.toNat := by
    rw [hm₃, VG.Proof.Bignum.X86_64.word_writeW_self, hv]
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans h10)
    hsi ((k13.gpr (by decide)).trans h12) (by omega) hw' (by have := sl _ hacc; omega)
    (by have := sl _ hmo; omega) (by have := sl _ htmp; omega) (by have := sp d6; omega)
    (by have := sp d7; omega)) fun s₄ ⟨c', lt, hbp', hlt, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr (by decide)).trans h8) ((k₄.gpr (by decide)).trans hsi)
    ((k₄.gpr (by decide)).trans hbx₃) ((k14.gpr (by decide)).trans h12) hbp' (by omega) hw'
    (by have := sl _ hacc; omega) (by have := sl _ htmp; omega) (by have := sl o ho; omega)
    (by have := sp d1; omega) (by have := sp d2; omega)) fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w = wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w :=
    ho₄.wv (by have := sp d6; omega) (by have := sl _ hacc; omega)
  rw [fN] at hD
  rw [hm₁] at hval
  have hN0 : 0 < wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w := by omega
  refine ⟨?_, ?_, ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · rw [hv', hacc₄, hlt, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w) (Tw := c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B (VG.Proof.Bignum.X86_64.slot w Public.aTmp) w) (m := wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : c.toNat < c'.toNat <;> simp [h, hTl]
  · have a3 : Arrays B w [Public.aAcc, Public.aTmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := Public.aAcc) (by simp) o3 (Nat.le_refl _) (by omega)
    have a4 : Arrays B w [Public.aAcc, Public.aTmp, o] s₃.mem s₄.mem :=
      Arrays.of_outside (j := Public.aTmp) (by simp) ho₄ (Nat.le_refl _) (by omega)
    have a5 : Arrays B w [Public.aAcc, Public.aTmp, o] s₄.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a4).trans a5

/-! ## Subtraction -/

theorem and_mask (a : BitVec 64) (c : Bool) : (a &&& VG.Proof.Bignum.X86_64.mask c).toNat = if c then a.toNat else 0 := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]

/-- After `j` words of the second loop of `subModArr`:
`O_j + 2^(64 j) c' = (c ? m_j : 0) + A_j`. -/
structure MaInv (s₀ : State) (B : Addr) (Z eo eN eA : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eo (8 * j) s₀.mem t.mem
  val : ∃ c' : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧
    wv t.mem B eo j + 2 ^ (64 * j) * c'.toNat = (if c then wv s₀.mem B eN j else 0) + wv s₀.mem B eA j

theorem maStep_ok {s₀ : State} {B : Addr} {Z w eo eN eA : Nat} {c : Bool}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA)
    (h15 : s₀.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (ho : eo + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z)
    (sN : eN + 8 * w ≤ eo ∨ eo + 8 * w ≤ eN) (sA : eA + 8 * w ≤ eo ∨ eo + 8 * w ≤ eA)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Bignum.X86_64.MaInv s₀ B Z eo eN eA c j t) :
    WP isa (.block (([.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp,
        .alu .adc .rax (.mem (ix .r8 .r14)), .store (ix .rbx .r14) .rax, cfToRbp] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.MaInv s₀ B Z eo eN eA c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (hI.keep.gpr (by decide)).trans h10
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c₀, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eo + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat =
          (VG.Proof.Bignum.X86_64.word t.mem B (eN + 8 * j) &&& VG.Proof.Bignum.X86_64.mask c).toNat + (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j)).toNat + c₀.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, addr0 t8 hI.r14, hbp, t15, cf_mask,
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, rfl, VG.Proof.Bignum.X86_64.adc_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eN + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, hy, VG.Proof.Bignum.X86_64.and_mask] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    cases c
    · simp only [ite_false, Bool.false_eq_true] at hr hval ⊢
      grind
    · simp only [ite_true] at hr hval ⊢
      grind

/-- `[o] := [a] - [b] mod m`, for `[a], [b] < m = [aN]`. -/
theorem subModArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ Public.aAcc) (d2 : o ≠ Public.aN) (d3 : a ≠ Public.aAcc) (d4 : b ≠ Public.aAcc)
    (hA : wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w)
    (hB : wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w) :
    WP isa (seqs (subModArr o a b)) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = (wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w + wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w -
        wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w) % wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w ∧
      Arrays B w [Public.aAcc, o] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w k ∨ VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hacc : Public.aAcc < 8 := by decide
  have hmo : Public.aN < 8 := by decide
  have d5 : Public.aAcc ≠ Public.aN := by decide
  unfold subModArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r8, .r10, .rsi, .r12, .rbp] (Q := fun t =>
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hH.harr a ha, hH.harr b hb, hH.harr Public.aAcc hacc, hH.hw]) rfl)
    fun s₁ ⟨⟨h8, h10, hsi, h12, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      SubInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w a) (VG.Proof.Bignum.X86_64.slot w b) (VG.Proof.Bignum.X86_64.slot w Public.aAcc) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (SubInv s₁ B Z (VG.Proof.Bignum.X86_64.slot w a) (VG.Proof.Bignum.X86_64.slot w b) (VG.Proof.Bignum.X86_64.slot w Public.aAcc)) h0
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega) (by have := sl a ha; omega)
      (by have := sl b hb; omega) (by have := sl _ hacc; omega) (by have := sp d3; omega)
      (by have := sp d4; omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  rw [hm₁] at hval
  have k12 := k₁.trans hI.keep
  have s₂di : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have fh : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₂.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi => by
    rw [hI.out.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega)) (by
      have := hdr_lt_slot w 8 hi; omega), hm₁]
  refine WP.seq (WP.mono (WP.keep [.r15, .rbp, .r10, .r8, .rbx] (Q := fun t => t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c ∧
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aN) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, s₂di, hdrOff, hl₂ (sArr Public.aN) (by decide),
      hl₂ (sArr Public.aAcc) (by decide), hl₂ (sArr o) (by unfold sArr; omega), hc,
      (fh _ (by decide)).trans (hH.harr Public.aN hmo), (fh _ (by decide)).trans (hH.harr Public.aAcc hacc),
      (fh _ (by unfold sArr; omega)).trans (hH.harr o ho)]) rfl)
    fun s₃ ⟨⟨h15, hbp₃, h10₃, h8₃, hbx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := k12.trans k₃
  have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 w := ((hI.keep.trans k₃).gpr (by decide)).trans h12
  have h0' : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₃.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₃ t → t.cf = s₃.cf →
      VG.Proof.Bignum.X86_64.MaInv s₃ B Z (VG.Proof.Bignum.X86_64.slot w o) (VG.Proof.Bignum.X86_64.slot w Public.aN) (VG.Proof.Bignum.X86_64.slot w Public.aAcc) c 0 t := fun t h14 hm k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp₃, by rw [hm]; cases c <;> rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (VG.Proof.Bignum.X86_64.MaInv s₃ B Z (VG.Proof.Bignum.X86_64.slot w o) (VG.Proof.Bignum.X86_64.slot w Public.aN) (VG.Proof.Bignum.X86_64.slot w Public.aAcc) c) h0'
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.maStep_ok hbx₃ h10₃ h8₃ h15 h12₃ (by omega) (by have := sl o ho; omega)
      (by have := sl _ hmo; omega) (by have := sl _ hacc; omega) (by have := sp (Ne.symm d2); omega)
      (by have := sp (Ne.symm d1); omega) hj hI)) fun t hI' => ?_
  obtain ⟨c', -, hv⟩ := hI'.val
  have oA : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) (8 * w) s.mem s₃.mem := by rw [hm₃, ← hm₁]; exact hI.out
  have fN : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w = wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w :=
    oA.wv (by have := sp d5; omega) (by have := sl _ hmo; omega)
  have fA : wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w = wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w := by rw [hm₃]
  rw [fN, fA] at hv
  have hN := wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w
  have hR := wv_lt t.mem B (VG.Proof.Bignum.X86_64.slot w o) w
  have hAc := wv_lt s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w
  refine ⟨?_, ?_, ((k13.trans hI'.keep)).mono (by decide)⟩
  · generalize wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w Public.aAcc) w = D at *
    generalize wv s.mem B (VG.Proof.Bignum.X86_64.slot w Public.aN) w = N at *
    generalize wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w = x at *
    generalize wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w = y at *
    generalize wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = r at *
    generalize (2 : Nat) ^ (64 * w) = R at *
    have hc1 := Bool.toNat_le c
    have hc2 := Bool.toNat_le c'
    cases c <;> cases c' <;> simp only [ite_true, ite_false, Bool.false_eq_true, Bool.toNat_true,
      Bool.toNat_false] at hv hval ⊢
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by omega)]; omega)
      | (rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
  · have a1 : Arrays B w [Public.aAcc, o] s.mem s₃.mem :=
      Arrays.of_outside (j := Public.aAcc) (by simp) oA (Nat.le_refl _) (by omega)
    have a2 : Arrays B w [Public.aAcc, o] s₃.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hI'.out (Nat.le_refl _) (by omega)
    exact a1.trans a2

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Store`. -/
section

/-!
# Multiword arithmetic on x86-64: words to bytes

`storeBE` writes the `w` words of an array (`rbx`), each masked with `r15`
(0 or all ones, `mask c`), as `k` bytes most significant first at `rsi`:
I2OSP of the number if `c`, and zeros otherwise (`storeBE_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

theorem and_mask_toNat (x : BitVec 64) (c : Bool) : (x &&& VG.Proof.Bignum.X86_64.mask c).toNat = if c then x.toNat else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

theorem shr8_toNat (x : BitVec 64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A word of a number of `w` words. -/
theorem word_of_wv (m : Mem) (B : Addr) (ed w : Nat) {q : Nat} (hq : q < w) :
    (VG.Proof.Bignum.X86_64.word m B (ed + 8 * q)).toNat = wv m B ed w / 2 ^ (64 * q) % 2 ^ 64 := by
  have h := wv_add m B ed q (w - q)
  rw [show q + (w - q) = w by omega] at h
  obtain ⟨r, hr⟩ : ∃ r, w - q = r + 1 := ⟨w - q - 1, by omega⟩
  rw [hr, show r + 1 = 1 + r by omega, wv_add, show (wv m B (ed + 8 * q) 1) = (VG.Proof.Bignum.X86_64.word m B (ed + 8 * q)).toNat
    by simp [wv]] at h
  rw [h]
  have hl := wv_lt m B ed q
  have hw := (VG.Proof.Bignum.X86_64.word m B (ed + 8 * q)).isLt
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, Nat.zero_add,
    show 64 * 1 = 64 from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

theorem out_ne {out : Addr} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    out + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro he
  apply h
  have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
    have := congrArg (fun x => x - out) he
    simpa only [Offset.add_sub_cancel_left] using this
  have := congrArg BitVec.toNat h2
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

/-- After `p` bytes of `storeBE` from `s`: the bytes `k - 1 - j` for `j < p`
are the bytes `j` of `Y_m` (the number, or 0, by the mask), and `rax`
holds what is left of the current word. -/
structure SInv (s : State) (out : Addr) (k : Nat) (Ym : Nat) (p : Nat) (t : State) : Prop where
  wr : t.wr = s.wr
  rd : t.rd = s.rd
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s t
  rdx : t.gpr .rdx = BitVec.ofNat 64 p
  r14 : t.gpr .r14 = out + BitVec.ofNat 64 (k - p)
  rax : p % 8 ≠ 0 → (t.gpr .rax).toNat = Ym / 256 ^ p % 256 ^ (8 - p % 8)
  bytes : ∀ j < p, t.mem (out + BitVec.ofNat 64 (k - 1 - j)) = BitVec.ofNat 8 (Ym / 256 ^ j)
  frame : ∀ x, (∀ j < p, x ≠ out + BitVec.ofNat 64 (k - 1 - j)) → t.mem x = s.mem x

theorem storeStep_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (h15 : s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (hk' : k < 2 ^ 31) (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 j))
    {p : Nat} (hp : p < k) {t : State}
    (hI : VG.Proof.Bignum.X86_64.SInv s out k (if c then wv s.mem B ed w else 0) p t) :
    WP isa (.seq (.block [.mov .rbp (.reg .rdx), .alu .and .rbp (.imm 7)])
      (.seq (.ite .e (.block [.mov .rbp (.reg .rdx), .shift .shr .rbp 3, .mov .rax (.mem (ix .rbx .rbp)),
          .alu .and .rax (.reg .r15)]) (.block []))
        (.block [.alu .sub .r14 (.imm 1), .store8 (at0 .r14) .rax, .shift .shr .rax 8,
          .alu .add .rdx (.imm 1), .alu .cmp .rdx (.reg .rcx)]))) t fun t' =>
      t'.zf = some (decide (p + 1 = k)) ∧ VG.Proof.Bignum.X86_64.SInv s out k (if c then wv s.mem B ed w else 0) (p + 1) t' := by
  have hn := hs.nowrap
  set Ym := if c then wv s.mem B ed w else 0 with hYm
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed := (hI.keep.gpr (by decide)).trans hbx
  have tcx : t.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have t15 : t.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (hI.keep.gpr (by decide)).trans h15
  have hts : VG.Proof.Bignum.X86_64.Scr t B Z := hs.congr hI.wr
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t₁ => t₁.zf = some (decide (p % 8 = 0)) ∧ t₁.mem = t.mem)
    (by xrun [hI.rdx, VG.Proof.Bignum.X86_64.sx7, VG.Proof.Bignum.X86_64.and7_eq p (by omega)]) rfl) fun t₁ ⟨⟨hz₁, hm₁⟩, k₁⟩ => ?_)
  -- After the optional load: `rax` holds bytes `p, …` of `Y_m` up to the word's end.
  have hload : WP isa (.ite .e (.block [.mov .rbp (.reg .rdx), .shift .shr .rbp 3,
      .mov .rax (.mem (ix .rbx .rbp)), .alu .and .rax (.reg .r15)]) (.block [])) t₁ fun t₂ =>
      (t₂.gpr .rax).toNat = Ym / 256 ^ p % 256 ^ (8 - p % 8) ∧ t₂.mem = t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbp] t₁ t₂ := by
    by_cases hz : p % 8 = 0
    · refine WP.ite true (by simp [VG.X86_64.eval, hz₁, hz]) (fun _ => ?_) (by simp)
      have t₁dx : t₁.gpr .rdx = BitVec.ofNat 64 p := (k₁.gpr (by decide)).trans hI.rdx
      have t₁bx : t₁.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed := (k₁.gpr (by decide)).trans tbx
      have t₁15 : t₁.gpr .r15 = VG.Proof.Bignum.X86_64.mask c := (k₁.gpr (by decide)).trans t15
      have hq : p / 8 < w := by omega
      have hwd : VG.Proof.Bignum.X86_64.word t₁.mem B (ed + 8 * (p / 8)) = VG.Proof.Bignum.X86_64.word s.mem B (ed + 8 * (p / 8)) := by
        rw [hm₁]
        exact Mem.readW_congr fun i hi => (hI.frame _ fun j hj => by
          intro he
          have h1 := hsep (k - 1 - j) (by omega)
          rw [← he, VG.Proof.Bignum.X86_64.ofs_off B (by omega)] at h1
          omega).symm |>.symm
      refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₂ =>
          t₂.gpr .rax = VG.Proof.Bignum.X86_64.word s.mem B (ed + 8 * (p / 8)) &&& VG.Proof.Bignum.X86_64.mask c ∧ t₂.mem = t₁.mem) (by
        xrun [State.ea, ix, t₁dx, VG.Proof.Bignum.X86_64.shr3_eq p (by omega), addr0 t₁bx rfl, t₁15,
          (by rw [k₁.2.1, k₁.2.2, hI.rd, hI.wr]; exact hs.ld (show ed + 8 * (p / 8) + 8 ≤ Z by omega) :
            InRegions (t₁.rd ++ t₁.wr) (off B (ed + 8 * (p / 8))) 8), hwd]) rfl)
        fun t₂ ⟨⟨hax, hm₂⟩, k₂⟩ => ⟨?_, hm₂.trans hm₁, k₂⟩
      rw [hax, VG.Proof.Bignum.X86_64.and_mask_toNat, VG.Proof.Bignum.X86_64.word_of_wv _ _ _ _ hq, show 8 - p % 8 = 8 by omega, VG.Proof.Bignum.pow256_8,
        show 64 * (p / 8) = 8 * p by omega, show (256 : Nat) ^ p = 2 ^ (8 * p) by
          rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]]
      simp only [hYm]
      cases c <;> simp
    · refine WP.ite false (by simp [VG.X86_64.eval, hz₁, hz]) (by simp) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [(k₁.gpr (by decide) : t₁.gpr .rax = t.gpr .rax)]; exact hI.rax hz, hm₁, Keep.refl _ _⟩
  refine WP.seq (WP.mono hload fun t₂ ⟨hax₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have t₂14 : t₂.gpr .r14 = out + BitVec.ofNat 64 (k - p) := (k12.gpr (by decide)).trans hI.r14
  have t₂dx : t₂.gpr .rdx = BitVec.ofNat 64 p := (k12.gpr (by decide)).trans hI.rdx
  have t₂cx : t₂.gpr .rcx = BitVec.ofNat 64 k := (k12.gpr (by decide)).trans tcx
  have e14 : out + BitVec.ofNat 64 (k - p) - 1 = out + BitVec.ofNat 64 (k - 1 - p) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_ofNat_sub out (by omega),
      show k - p - 1 = k - 1 - p by omega]
  have hst : InRegions t₂.wr (out + BitVec.ofNat 64 (k - 1 - p)) 1 := by
    rw [k12.2.2, hI.wr]; exact hout _ (by omega)
  refine WP.mono (WP.keep [.rax, .rdx, .r14] (Q := fun t' =>
      t'.mem = t₂.mem.writeW (out + BitVec.ofNat 64 (k - 1 - p)) ((t₂.gpr .rax).setWidth 8) ∧
      t'.gpr .rax = t₂.gpr .rax >>> 8 ∧ t'.gpr .rdx = BitVec.ofNat 64 (p + 1) ∧
      t'.gpr .r14 = out + BitVec.ofNat 64 (k - 1 - p) ∧ t'.zf = some (decide (p + 1 = k))) (by
    xrun [State.ea, at0, t₂14, t₂dx, t₂cx, e14, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst,
      ofNat_add_one, ofNat_sub_beq (show p + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hax', hdx', h14', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  have hbyte : (t₂.gpr .rax).setWidth 8 = BitVec.ofNat 8 (Ym / 256 ^ p) := by
    rw [← BitVec.ofNat_toNat, hax₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Dvd.intro_left
      (256 ^ (8 - p % 8 - 1)) (by rw [← Nat.pow_succ]; congr 1; omega))]
  refine ⟨k'.2.2.trans (k12.2.2.trans hI.wr), k'.2.1.trans (k12.2.1.trans hI.rd),
    ((hI.keep.trans k12).trans k').mono (by decide), hdx', by rw [h14']; congr 2; omega, ?_, ?_, ?_⟩
  · intro hz
    rw [hax', VG.Proof.Bignum.X86_64.shr8_toNat, hax₂, show 8 - p % 8 = 1 + (8 - (p + 1) % 8) by omega, Nat.pow_add,
      Nat.pow_one, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · intro j hj
    rw [hm', hm₂, VG.WriteBytes.writeW8_apply]
    by_cases hjp : j = p
    · subst hjp; simp [hbyte]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Bignum.X86_64.out_ne (by omega) (by omega) (by omega)))]
      exact hI.bytes j (by omega)
  · intro x hx
    rw [hm', hm₂, VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx p (by omega)))]
    exact hI.frame x fun j hj => hx j (by omega)

/-- `storeBE`: the number at `rbx` (`w` words), masked by `r15 = mask c`, as
`k` bytes at `rsi`, most significant first: I2OSP of it, or of 0. -/
theorem storeBE_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B ed) (hsi : s.gpr .rsi = out)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (h15 : s.gpr .r15 = VG.Proof.Bignum.X86_64.mask c) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ VG.Proof.Bignum.X86_64.ofs B (out + BitVec.ofNat 64 j)) :
    WP isa storeBE s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s t := by
  unfold storeBE
  refine WP.seq (WP.mono (WP.keep [.rdx, .r14] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 0 ∧
      t.gpr .r14 = out + BitVec.ofNat 64 k ∧ t.mem = s.mem) (by xrun [hsi, hcx]) rfl)
    fun s₁ ⟨⟨hdx, h14, hm₁⟩, k₁⟩ => ?_)
  refine wp_upto (a := 0) (N := k) (by omega) (VG.Proof.Bignum.X86_64.SInv s out k (if c then wv s.mem B ed w else 0)) ?_
    (fun t hI => ⟨?_, ?_, hI.wr, hI.rd, hI.keep⟩)
    ⟨k₁.2.2, k₁.2.1, k₁.mono (by decide), hdx, by rw [h14, Nat.sub_zero], fun h => absurd rfl h,
      fun j hj => absurd hj (by omega), fun x _ => by rw [hm₁]⟩
  · intro p _ hp t hI
    exact VG.Proof.Bignum.X86_64.storeStep_ok hs hbx hcx h15 hk' hw hed hout hsep hp hI
  · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
    intro i h1 h2
    have hik : i < k := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Spec.Rsa.i2osp]
    have := hI.bytes (k - 1 - i) (by omega)
    rwa [show k - 1 - (k - 1 - i) = i by omega] at this
  · intro x hx
    exact hI.frame x fun j hj => hx _ (by omega)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Setup`. -/
section

/-!
# Multiword arithmetic on x86-64: setting up

`minv`: `-m₀⁻¹ mod 2⁶⁴` for an odd `m₀` (`minv_ok`), by five steps of
Newton's iteration from `x = m₀`, which is right modulo 8.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum (newton_step emod_pow_weaken odd_sq)

theorem toNat_ofNat_modEq (n : Nat) : ((BitVec.ofNat 64 n).toNat : Int) ≡ n [ZMOD 2 ^ 64] := by
  rw [BitVec.toNat_ofNat]; push_cast; exact Int.mod_modEq _ _

theorem toNat_two_sub_modEq (y : BitVec 64) :
    ((BitVec.setWidth 64 (2 : BitVec 32) - y).toNat : Int) ≡ 2 - y.toNat [ZMOD 2 ^ 64] := by
  rw [BitVec.toNat_sub, show (BitVec.setWidth 64 (2 : BitVec 32)).toNat = 2 from rfl]
  have hy := y.isLt
  have : ((2 ^ 64 - y.toNat + 2 : Nat) : Int) = 2 - y.toNat + 2 ^ 64 := by push_cast [Nat.cast_sub hy.le]; omega
  rw [Int.natCast_emod, this]
  refine (Int.mod_modEq _ _).trans ?_
  show (2 - (y.toNat : Int) + 2 ^ 64) % 2 ^ 64 = (2 - (y.toNat : Int)) % 2 ^ 64
  exact Int.add_emod_right _ _

/-- The value of a Newton step, modulo `2⁶⁴`. -/
theorem newton_val (a x : BitVec 64) :
    ((BitVec.ofNat 64 (x.toNat * (BitVec.setWidth 64 (2 : BitVec 32) -
      BitVec.ofNat 64 (a.toNat * x.toNat)).toNat)).toNat : Int) ≡
      x.toNat * (2 - a.toNat * x.toNat) [ZMOD 2 ^ 64] := by
  refine (VG.Proof.Bignum.X86_64.toNat_ofNat_modEq _).trans ?_
  push_cast
  refine Int.ModEq.mul_left _ ((VG.Proof.Bignum.X86_64.toNat_two_sub_modEq _).trans (Int.ModEq.sub_left 2 ?_))
  exact VG.Proof.Bignum.X86_64.toNat_ofNat_modEq _

theorem newton_ok (t : State) :
    WP isa (.block newton) t fun t' =>
      (((t'.gpr .rcx).toNat : Int) - (t.gpr .rcx).toNat * (2 - (t.gpr .rbx).toNat * (t.gpr .rcx).toNat)) %
        (2 ^ 64 : Int) = 0 ∧ t'.gpr .rbx = t.gpr .rbx ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi] (c := .block newton) (Q := fun t' =>
    (((t'.gpr .rcx).toNat : Int) - (t.gpr .rcx).toNat * (2 - (t.gpr .rbx).toNat * (t.gpr .rcx).toNat)) %
        (2 ^ 64 : Int) = 0 ∧ t'.gpr .rbx = t.gpr .rbx ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold newton
  xrun
  exact Int.emod_eq_zero_of_dvd (VG.Proof.Bignum.X86_64.newton_val _ _).symm.dvd

/-- A Newton step on the state: `a x' ≡ 1 (mod 2^(2j))` from `a x ≡ 1 (mod 2^j)`. -/
theorem newton_step_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .rbx).toNat : Int) * (t.gpr .rcx).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      (((t'.gpr .rbx).toNat : Int) * (t'.gpr .rcx).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
      t'.gpr .rbx = t.gpr .rbx ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi] t t' :=
  WP.mono (VG.Proof.Bignum.X86_64.newton_ok t) fun t' ⟨hv, hb, hm, k⟩ => ⟨by rw [hb]; exact newton_step hj h hv, hb, hm, k⟩

/-- Negating an inverse: `a (-x) + 1 ≡ 0` from `a x ≡ 1 (mod 2⁶⁴)`. -/
theorem neg_inv {a x : Nat} (hx : x < 2 ^ 64) (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) :
    (a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  have hr : (((2 ^ 64 - x + 0) % 2 ^ 64 : Nat) : Int) ≡ -(x : Int) [ZMOD 2 ^ 64] := by
    rw [Int.natCast_emod]
    refine (Int.mod_modEq _ _).trans ?_
    unfold Int.ModEq
    omega
  have h2 : ((a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1 : Nat) : Int) ≡ -((a : Int) * x - 1) [ZMOD 2 ^ 64] := by
    push_cast
    have := (hr.mul_left (a : Int)).add_right 1
    refine this.trans ?_
    rw [show (a : Int) * -(x : Int) + 1 = -((a : Int) * x - 1) by rw [Int.mul_neg]; omega]
  have h3 : -((a : Int) * x - 1) ≡ 0 [ZMOD 2 ^ 64] := by
    unfold Int.ModEq
    rw [Int.emod_eq_zero_of_dvd (dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))]
    rfl
  have h4 := h2.trans h3
  exact_mod_cast h4

/-- `minv`: `-m₀⁻¹ mod 2⁶⁴` into `r15`, for the odd `m₀` in `rbx`. -/
theorem minv_ok (s : State) (hodd : (s.gpr .rbx).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      ((s.gpr .rbx).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem := by
  unfold minv
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx] (c := .block [.mov .rcx (.reg .rbx)]) (Q := fun t =>
    t.gpr .rcx = s.gpr .rbx ∧ t.mem = s.mem) (by xrun) rfl) fun t₀ ⟨⟨h₀, hm₀⟩, k₀⟩ => ?_
  have hb₀ : t₀.gpr .rbx = s.gpr .rbx := k₀.gpr (by decide)
  have e₀ : (((t₀.gpr .rbx).toNat : Int) * (t₀.gpr .rcx).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [hb₀, h₀]
    have h1 := odd_sq _ hodd
    have h2 : (((s.gpr .rbx).toNat : Int) * (s.gpr .rbx).toNat) % 8 = 1 := by exact_mod_cast h1
    show (((s.gpr .rbx).toNat : Int) * (s.gpr .rbx).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.newton_step_ok t₀ (j := 3) (by norm_num) e₀) fun t₁ ⟨e₁, hb₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.newton_step_ok t₁ (j := 6) (by norm_num) e₁) fun t₂ ⟨e₂, hb₂, hm₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.newton_step_ok t₂ (j := 12) (by norm_num) e₂) fun t₃ ⟨e₃, hb₃, hm₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.newton_step_ok t₃ (j := 24) (by norm_num) e₃) fun t₄ ⟨e₄, hb₄, hm₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.newton_step_ok t₄ (j := 32) (by norm_num) (emod_pow_weaken (by norm_num) e₄))
    fun t₅ ⟨e₅, hb₅, hm₅, k₅⟩ => ?_
  have hb : t₅.gpr .rbx = s.gpr .rbx := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans hb₀))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = 0 - t₅.gpr .rcx ∧ t.mem = t₅.mem)
    (by xrun; rfl) rfl) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨?_, (kk.trans k).mono (by decide), ?_⟩
  · rw [h15, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
    exact VG.Proof.Bignum.X86_64.neg_inv (t₅.gpr .rcx).isLt e₅
  · rw [hm, hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]

/-! ## The arrays' bases -/

theorem setBase_ok {t : State} {B : Addr} {Z w j : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hdi : t.gpr .rdi = B)
    (hj : j < 8) (hZ : 8 * sArr 8 ≤ Z) (hdx : t.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j))
    (hax : t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (setBase j)) t fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sArr j)) (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) ∧
      t'.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w (j + 1)) ∧ VG.Proof.MlKem.X86_64.Keep [.rdx] t t' := by
  have h8 : 8 * sArr j + 8 ≤ 8 * sArr 8 := by unfold sArr; omega
  have hst : InRegions t.wr (VG.Proof.Bignum.X86_64.off B (8 * sArr j)) 8 := hs.st (by omega)
  refine WP.mono (WP.keep [.rdx] (c := .block (setBase j)) (Q := fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sArr j)) (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) ∧
      t'.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w (j + 1))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold setBase
  xrun [State.ea, hdr, hdi, hdrOff, hst, hdx, hax]
  rw [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  unfold VG.Proof.Bignum.X86_64.slot; rw [Nat.add_mul, Nat.one_mul]; omega

theorem setBasesN_ok {B : Addr} {Z w : Nat} (hZ : 8 * sArr 8 ≤ Z) :
    ∀ n ≤ 8, ∀ t : State, VG.Proof.Bignum.X86_64.Scr t B Z → t.gpr .rdi = B → t.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w 0) →
      t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2)) →
      WP isa (.block ((List.range n).flatMap setBase)) t fun t' =>
        (∀ j < n, VG.Proof.Bignum.X86_64.word t'.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) ∧ t'.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w n) ∧
        VG.Proof.Bignum.X86_64.Outside B (8 * sArr 0) (8 * n) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdx] t t' := by
  intro n
  induction n with
  | zero =>
    intro _ t _ _ hdx _
    exact WP.block_nil ⟨fun j hj => absurd hj (by omega), hdx, Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    intro hn t hs hdi hdx hax
    have hnZ := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) t hs hdi hdx hax) fun t₁ ⟨hw₁, hdx₁, ho₁, k₁⟩ => ?_
    refine WP.mono (VG.Proof.Bignum.X86_64.setBase_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) (by omega) hZ hdx₁
      ((k₁.gpr (by decide)).trans hax)) fun t' ⟨hm, hdx', k'⟩ => ⟨?_, hdx', ?_, k₁.trans k' |>.mono (by decide)⟩
    · intro j hj
      rw [hm]
      by_cases hjn : j = n
      · subst hjn; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
      · rw [(VG.Proof.Bignum.X86_64.writeW_outside t₁.mem B _ (by unfold sArr at *; omega)).word
          (by unfold sArr; omega) (by unfold sArr; omega)]
        exact hw₁ j (by omega)
    · rw [hm]
      intro x hx
      rw [VG.Proof.Bignum.X86_64.writeW_outside t₁.mem B _ (by unfold sArr; omega) x (by unfold sArr at *; omega)]
      exact ho₁ x (by omega)

/-- `setBases`: the arrays' bases into the header, for `w` in `r12`. -/
theorem setBases_ok {s : State} {B : Addr} {Z w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hZ : 8 * sArr 8 ≤ Z) :
    WP isa (.block setBases) s fun t =>
      (∀ j < 8, VG.Proof.Bignum.X86_64.word t.mem B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)) ∧
      VG.Proof.Bignum.X86_64.Outside B (8 * sArr 0) 64 s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t := by
  unfold setBases
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .rdx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w 0) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨hax, hdx, hm⟩, k⟩ => ?_
  · xrun [h12, hdi, sx_ofNat (show hdrBytes < 2 ^ 31 by decide)]
    refine ⟨?_, by simp [VG.Proof.Bignum.X86_64.off, VG.Proof.Bignum.X86_64.slot]⟩
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
    simp only [← BitVec.ofNat_add]
    congr 1; omega
  refine WP.mono (VG.Proof.Bignum.X86_64.setBasesN_ok hZ 8 (by omega) t (hs.congr k.2.2) ((k.gpr (by decide)).trans hdi) hdx hax)
    fun t' ⟨hw', _, ho, k'⟩ => ⟨hw', by rw [← hm]; exact ho, (k.trans k').mono (by decide)⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.R2`. -/
section

/-!
# Multiword arithmetic on x86-64: `R² mod m`

* `setWord o i`: `[o] := rdx · 2^(64 i)` (`setWord_ok`).
* `topBit`: the top bit of the nonzero `rax`: `rdx := 2^j`, `rcx := 64 - j`
  (`topBit_ok`).
* `doubles`: `[o] := 2^c [o] mod m` for the count `c` in `rcx` (`doubles_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `[o] := v 2^(64 i)` for `v` in `rdx` and the word index `i` in `ri`. -/
theorem setWord_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {o : Nat} (ho : o < 8) {ri : Reg} (hri : ri ∉ [.rax, .r8, .r14])
    {i : Nat} (hi : i < w) (hix : s.gpr ri = BitVec.ofNat 64 i) :
    WP isa (setWord o ri) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = (s.gpr .rdx).toNat * 2 ^ (64 * i) ∧
      VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w o) (8 * (w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r8, .r14] s t := by
  have hn := hs.nowrap
  have sl : VG.Proof.Bignum.X86_64.slot w o + 8 * (w + 2) ≤ Z := (slot_le ho).trans hZ
  unfold setWord
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sArr o + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega); omega), hH.harr o ho]) rfl)
    fun s₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroAccLoop_ok (hs.congr k₁.2.2) h8 ((k₁.gpr (by decide)).trans h12) hw hw' sl)
    fun s₂ ⟨hz, ho₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have s₂8 : s₂.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) := (k₂.gpr (by decide)).trans h8
  have s₂i : s₂.gpr ri = BitVec.ofNat 64 i := (k12.gpr (fun h => hri ((List.Perm.swap Reg.rax Reg.r8 [Reg.r14]).mem_iff.1 h))).trans hix
  have s₂dx : s₂.gpr .rdx = s.gpr .rdx := k12.gpr (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o + 8 * i)) (s.gpr .rdx))
    (by xrun [State.ea, ix, addr0 s₂8 s₂i, (hs.congr (k12.2.2)).st (show VG.Proof.Bignum.X86_64.slot w o + 8 * i + 8 ≤ Z by omega),
      s₂dx]) rfl) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k12.trans k).mono (by decide)⟩
  · -- `[o]` is zero but word `i`.
    have hz' := (wv_eq_zero_iff _ _ _ _).mp hz
    rw [wv_single t.mem B (VG.Proof.Bignum.X86_64.slot w o) w hi fun q hq hne => by
      rw [hm, (VG.Proof.Bignum.X86_64.writeW_outside s₂.mem B _ (by omega)).word (by omega) (by omega)]
      exact hz' q (by omega), hm, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm]
    intro x hx
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega)]
    exact ho₂ x hx |>.trans (by rw [hm₁])

/-! ## The top bit -/

theorem shr1_ofNat (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem cmp1_eq (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n - 1 == 0) = decide (n = 1) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
  exact ofNat_sub_beq hn (by decide)

theorem div_pow_succ (T j : Nat) : T / 2 ^ j / 2 = T / 2 ^ (j + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- `topBit`: `rdx := 2^j`, `rcx := 64 - j` for `j` the top bit of `rax ≠ 0`. -/
theorem topBit_ok {s : State} {T : Nat} (hT : s.gpr .rax = BitVec.ofNat 64 T) (hT0 : 0 < T)
    (hT1 : T < 2 ^ 64) :
    WP isa topBit s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (2 ^ T.log2) ∧ t.gpr .rcx = BitVec.ofNat 64 (64 - T.log2) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t := by
  have hL : T.log2 < 64 := (Nat.log2_lt (by omega)).mpr hT1
  have hle := Nat.log2_self_le (n := T) (by omega)
  have hlt := Nat.lt_log2_self (n := T)
  unfold topBit
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 (2 ^ 0) ∧
      t.gpr .rcx = BitVec.ofNat 64 (64 - 0) ∧ t.zf = some (decide (T = 1)) ∧ t.mem = s.mem ∧
      t.gpr .rax = BitVec.ofNat 64 (T / 2 ^ 0))
    (by xrun [hT, VG.Proof.Bignum.X86_64.cmp1_eq T hT1]; simp) rfl) fun s₁ ⟨⟨hdx, hcx, hz, hm, s₁ax⟩, k₁⟩ => ?_)
  by_cases h1 : T = 1
  · subst h1
    refine WP.ite true (by simp [VG.X86_64.eval, hz]) (fun _ => WP.block_nil ⟨?_, ?_, hm, k₁.mono (by decide)⟩) (by simp)
    · rw [hdx]; rfl
    · rw [hcx]; rfl
  refine WP.ite false (by simp [VG.X86_64.eval, hz, h1]) (by simp) (fun _ => ?_)
  -- The loop: after `j` halvings, `rax = T / 2^j`, `rdx = 2^j`, `rcx = 64 - j`.
  refine WP.loop (M := isa) (fun n t => ∃ j, n = T.log2 - j ∧ j < T.log2 ∧
      t.gpr .rax = BitVec.ofNat 64 (T / 2 ^ j) ∧ t.gpr .rdx = BitVec.ofNat 64 (2 ^ j) ∧
      t.gpr .rcx = BitVec.ofNat 64 (64 - j) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t) ?_ _ s₁
    ⟨0, rfl, by
      have : 2 ^ 1 ≤ T := by omega
      exact (Nat.le_log2 (by omega)).mpr this, s₁ax, hdx, hcx, hm, k₁.mono (by decide)⟩
  rintro n t ⟨j, rfl, hj, hax, hdx', hcx', hm', k⟩
  have hTj : T / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  have hpj : 2 ^ j < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
      t'.gpr .rdx = BitVec.ofNat 64 (2 ^ (j + 1)) ∧ t'.gpr .rcx = BitVec.ofNat 64 (64 - (j + 1)) ∧
      t'.zf = some (decide (T / 2 ^ (j + 1) = 1)) ∧ t'.mem = t.mem) (by
    xrun [hax, hdx', hcx', VG.Proof.Bignum.X86_64.shr1_ofNat _ hTj, VG.Proof.Bignum.X86_64.div_pow_succ, ← BitVec.ofNat_add]
    refine ⟨by rw [Nat.pow_succ, Nat.mul_two], ?_, ?_⟩
    · rw [ofNat64_pred (by omega) (by omega)]; congr 1
    · exact ofNat_sub_beq (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1) (by decide)) rfl) fun t' ⟨⟨hax', hdx'', hcx'', hz', hm''⟩, k'⟩ => ?_
  -- `T / 2^(j+1) = 1` iff `j + 1` is the top bit.
  have key : T / 2 ^ (j + 1) = 1 ↔ j + 1 = T.log2 := by
    constructor
    · intro h
      have h1 : 2 ^ (j + 1) ≤ T := by
        have := Nat.div_mul_le_self T (2 ^ (j + 1)); rw [h, Nat.one_mul] at this; exact this
      have h2 : T < 2 ^ (j + 2) := by
        have := Nat.lt_mul_div_succ T (show 0 < 2 ^ (j + 1) by positivity)
        rw [h] at this; rw [Nat.pow_succ]; omega
      have := (Nat.le_log2 (by omega)).mpr h1
      have := (Nat.log2_lt (by omega)).mpr h2
      omega
    · intro h
      rw [← h] at hle hlt
      exact Nat.div_eq_of_lt_le (by rw [Nat.one_mul]; exact hle) (by rw [Nat.pow_succ] at hlt; omega)
  by_cases he : j + 1 = T.log2
  · refine .inl ⟨by simp [VG.X86_64.eval, hz', key.mpr he], ?_, ?_, hm''.trans hm', (k.trans k').mono (by decide)⟩
    · rw [hdx'', he]
    · rw [hcx'', he]
  · refine .inr ⟨by simp [VG.X86_64.eval, hz', (not_congr key).mpr he], T.log2 - (j + 1), by omega, j + 1, rfl, by omega,
      hax', hdx'', hcx'', hm''.trans hm', (k.trans k').mono (by decide)⟩

/-! ## Repeated doubling -/

/-- After `j` of `c` doublings of `O` modulo `N` from `s`, counted in slot
`sl`. -/
structure DblsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (mo acc tmp o sl c O N j : Nat)
    (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : Hdr t.mem B w minv
  cnt : VG.Proof.Bignum.X86_64.word t.mem B (8 * sl) = BitVec.ofNat 64 (c - j)
  ov : wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = 2 ^ j * O % N
  nv : wv t.mem B (VG.Proof.Bignum.X86_64.slot w mo) w = N
  frm : Frm B [(VG.Proof.Bignum.X86_64.slot w acc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w tmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w o, 8 * (w + 2)), (8 * sl, 8)]
    s.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs s t

/-- `doubles`' count of `double`s. -/
abbrev dblCount (sl : Nat) : List Instr :=
  [.mov .rcx (.mem (hdr sl)), .alu .sub .rcx (.imm 1), .store (hdr sl) .rcx]

/-- One doubling of `doubles`, and its count. -/
theorem dblIter_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {c O N j : Nat} (hc' : c < 2 ^ 31) (hN0 : 0 < N) (hj : j < c)
    (hI : VG.Proof.Bignum.X86_64.DblsInv s B Z w minv mo acc tmp o sl c O N j t) :
    WP isa (.seq (double mo acc tmp o) (.block (VG.Proof.Bignum.X86_64.dblCount sl))) t fun t' =>
      t'.zf = some (decide (j + 1 = c)) ∧ VG.Proof.Bignum.X86_64.DblsInv s B Z w minv mo acc tmp o sl c O N (j + 1) t' := by
  have hn := hI.scr.nowrap
  have sl8 : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have sp : ∀ {j k}, j ≠ k → VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w k ∨ VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j :=
    fun h => slot_sep h
  have hhs : ∀ j, 8 * sl + 8 ≤ VG.Proof.Bignum.X86_64.slot w j := fun j => hdr_lt_slot w j hsl'
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 (by
      rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t₁ ⟨hv₁, ha₁, k₁'⟩ => ?_)
  have hst₁ := hI.scr.congr k₁'.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁'.gpr (by decide)).trans hI.rdi
  have hH₁ := ha₁.hdr hI.hdr
  have hcnt₁ : VG.Proof.Bignum.X86_64.word t₁.mem B (8 * sl) = BitVec.ofNat 64 (c - j) := by
    rw [ha₁.word_eq (fun j' hj' => Or.inl (by simp at hj'; rcases hj' with rfl | rfl | rfl <;> exact hhs _))
      (by omega), hI.cnt]
  have hld : InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * sl)) 8 := hst₁.ld (by have := hhs 8; omega)
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.mem = t₁.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sl))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.zf = some (decide (c - (j + 1) = 0))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hld, hst₁.st (show 8 * sl + 8 ≤ Z by have := hhs 8; omega), hcnt₁,
      ofNat64_pred (show 1 ≤ c - j by omega) (by omega), ofNat64_beq_zero (show c - j - 1 < 2 ^ 64 by omega)]
    exact ⟨by congr 2, by congr 1⟩) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨?_, ?_⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  have o' : VG.Proof.Bignum.X86_64.Outside B (8 * sl) 8 t₁.mem t'.mem := by rw [hm']; exact VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega)
  refine ⟨hst₁.congr k'.2.2, (k'.gpr (by decide)).trans hdi₁, by rw [hm']; exact Hdr.store hH₁ hsl hsl' _,
    by rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self], ?_, ?_, ?_, ((hI.keep.trans k₁').trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs o; omega) (by have := sl8 o ho; omega), hv₁, hI.ov, hI.nv, Nat.mul_mod,
      Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.pow_succ']
  · rw [o'.wv (by have := hhs mo; omega) (by have := sl8 mo hmo; omega),
      ha₁.wv_eq (fun j' hj' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl | rfl
        · have := sp d1; omega
        · have := sp d6; omega
        · have := sp d8; omega) (by have := sl8 mo hmo; omega), hI.nv]
  · exact (hI.frm.trans (Frm.of_arrays ha₁ (by simp))).trans (Frm.of_outside o' (by simp))

/-- `doubles`' start: the count `c` into slot `sl`. -/
theorem dblStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {mo acc tmp o sl : Nat}
    (hmo : mo < 8) (ho : o < 8) (hsl : 16 ≤ sl) (hsl' : sl < 32) {c : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hO : wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) :
    WP isa (.block [.store (hdr sl) .rcx]) s (VG.Proof.Bignum.X86_64.DblsInv s B Z w minv mo acc tmp o sl c
      (wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w) (wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) 0) := by
  have hn := hs.nowrap
  have sl8 : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have hhs : ∀ j, 8 * sl + 8 ≤ VG.Proof.Bignum.X86_64.slot w j := fun j => hdr_lt_slot w j hsl'
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sl)) (s.gpr .rcx))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st (show 8 * sl + 8 ≤ Z by have := hhs 8; omega)]) rfl)
    fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : VG.Proof.Bignum.X86_64.Outside B (8 * sl) 8 s.mem s₁.mem := by rw [hm₁]; exact VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega)
  exact ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, by rw [hm₁]; exact Hdr.store hH hsl hsl' _,
    by rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self, hcx, Nat.sub_zero],
    by rw [o₁.wv (by have := hhs o; omega) (by have := sl8 o ho; omega), Nat.pow_zero, Nat.one_mul,
      Nat.mod_eq_of_lt hO],
    o₁.wv (by have := hhs mo; omega) (by have := sl8 mo hmo; omega),
    Frm.of_outside o₁ (by simp), k₁.mono (by decide)⟩

theorem doubles_eq (mo acc tmp o sl : Nat) : doubles mo acc tmp o sl =
    .seq (.block [.store (hdr sl) .rcx]) (.loop (.seq (double mo acc tmp o) (.block (VG.Proof.Bignum.X86_64.dblCount sl))) .ne) := rfl

/-- `doubles`: `[o] := 2^c [o] mod m`, for the count `c ≥ 1` in `rcx`. -/
theorem doubles_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 31)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hO : wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w < wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) :
    WP isa (doubles mo acc tmp o sl) s fun t =>
      wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = 2 ^ c * wv s.mem B (VG.Proof.Bignum.X86_64.slot w o) w % wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w ∧
      Frm B [(VG.Proof.Bignum.X86_64.slot w acc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w tmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w o, 8 * (w + 2)), (8 * sl, 8)]
        s.mem t.mem ∧ Hdr t.mem B w minv ∧ VG.Proof.MlKem.X86_64.Keep mmRegs s t := by
  rw [VG.Proof.Bignum.X86_64.doubles_eq]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.dblStart_ok (acc := acc) (tmp := tmp) hs hdi hH hZ hmo ho hsl hsl' hcx hO)
    fun s₁ h₁ => ?_)
  exact wp_upto (a := 0) (N := c) (by omega) _ (fun j _ hj t hI => VG.Proof.Bignum.X86_64.dblIter_ok hZ hw hw' hmo hacc htmp ho
    d1 d2 d3 d6 d7 d8 hsl hsl' hc' (by omega) hj hI) (fun t hI => ⟨hI.ov, hI.frm, hI.hdr, hI.keep⟩) h₁

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Exp`. -/
section

/-!
# Multiword arithmetic on x86-64: the exponentiation of `vg_rsa_public`

`Good t B Z w minv`: the working space, its base in `rdi`, and the header.
`mm_ok` is `montMul_ok` for `vg_rsa_public`'s arrays. `expBit` squares `Y`
and multiplies it by `X` if the bit is set (`expBit_ok`); `expLoop` does it
for every bit of `e`, most significant first (`expLoop_ok`): `Y ≡ x^e R`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem bit7 (V : Nat) (hV : V < 2 ^ 64) :
    ((BitVec.ofNat 64 V >>> 7) &&& 1 == 0) = decide (V / 128 % 2 = 0) := by
  have h : ((BitVec.ofNat 64 V >>> 7) &&& 1).toNat = V / 128 % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
      Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h0 : V / 128 % 2 = 0
  · simp only [h0, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, h0]; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; rw [← h, he]; rfl

/-- What a bit of the exponentiation changes: arrays and header slots. -/
def bitRanges (w : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot w aAcc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aTmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aY, 8 * (w + 2)), (8 * VG.Impl.Bignum.X86_64.Public.sV, 8),
    (8 * VG.Impl.Bignum.X86_64.Public.sBit, 8)]

/-- What the exponentiation changes: also the byte index. -/
def expRanges (w : Nat) : List (Nat × Nat) := (8 * VG.Impl.Bignum.X86_64.Public.sI, 8) :: VG.Proof.Bignum.X86_64.bitRanges w

/-- An array that `Arrays` does not list keeps its value. -/
theorem Arrays.wv_of_not_mem {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {j : Nat} (hj : j < 8) (hn : j ∉ js) (hZ : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) :
    wv m' B (VG.Proof.Bignum.X86_64.slot w j) w = wv m B (VG.Proof.Bignum.X86_64.slot w j) w :=
  h.wv_eq (fun k hk => by
    have := slot_sep (w := w) (show j ≠ k from fun e => hn (e ▸ hk)); omega)
    (by have := slot_le (w := w) hj; omega)

theorem Arrays.word0_of_not_mem {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {j : Nat} (hj : j < 8) (hn : j ∉ js) (hZ : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    VG.Proof.Bignum.X86_64.word m' B (VG.Proof.Bignum.X86_64.slot w j) = VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w j) :=
  h.word_eq (fun k hk => by
    have := slot_sep (w := w) (show j ≠ k from fun e => hn (e ▸ hk)); omega)
    (by have := slot_le (w := w) hj; omega)

theorem Arrays.hslot {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {i : Nat}
    (hi : i < 32) : VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) :=
  h.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega)

theorem bit_step {v tb : Nat} (htb : tb < 8) :
    2 * (v / 2 ^ (8 - tb)) + v * 2 ^ tb / 128 % 2 = v / 2 ^ (7 - tb) := by
  have h1 : v * 2 ^ tb / 128 = v / 2 ^ (7 - tb) := by
    rw [show (128 : Nat) = 2 ^ tb * 2 ^ (7 - tb) by rw [← Nat.pow_add, show tb + (7 - tb) = 7 by omega],
      Nat.mul_comm v, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
  rw [h1, show 8 - tb = (7 - tb) + 1 by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- What the exponentiation keeps: the working space, the modulus `N` (and
its low word, for `-m⁻¹`), and `X ≡ x R`. -/
structure ExpCtx (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = N
  inv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aXm) w = X

theorem ExpCtx.of_arrays {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hg : Good t' B Z w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w)
    (ha : Arrays B w [aAcc, aTmp, aY] t.mem t'.mem) : VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X := by
  have hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  exact ⟨hg, by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hc.n,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn hw]; exact hc.inv,
    by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hc.x⟩

/-- One bit of `e`: `Y ≡ x^E R` becomes `x^(2E + bit) R`, for the bit at the
top of the byte `V / 128 mod 2`; `V` doubles and the bit count `b` drops. -/
theorem expBit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E Y V b : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hY : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y) (hYN : Y < N) (hYc : Y % N = x ^ E * 2 ^ (64 * w) % N)
    (hV : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62)
    (hb : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa VG.Impl.Bignum.X86_64.Public.expBit t fun t' => VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X ∧
      (∃ Y', wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y' ∧ Y' < N ∧ Y' % N = x ^ (2 * E + V / 128 % 2) * 2 ^ (64 * w) % N) ∧
      VG.Proof.Bignum.X86_64.word t'.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 (V + V) ∧ VG.Proof.Bignum.X86_64.word t'.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm B (VG.Proof.Bignum.X86_64.bitRanges w) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have eV : VG.Impl.Bignum.X86_64.Public.sV = 25 := rfl
  have eB : VG.Impl.Bignum.X86_64.Public.sBit = 24 := rfl
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot w 0 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold VG.Impl.Bignum.X86_64.Public.expBit
  -- `Y := Y²`.
  refine WP.seq (WP.mono (Mont.base.mm_ok (o := aY) (a := aY) (b := aY) hc.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hY, hc.n]; exact hYN))
    fun t₁ ⟨hg₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁
  rw [hc.n, hY] at hm₁
  have hc₁ := hc.of_arrays hg₁ hZ (by omega) ha₁
  have hY₁ : wv t₁.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = x ^ (2 * E) * 2 ^ (64 * w) % N :=
    VG.Proof.Bignum.mont_sq hR hYc hm₁
  have hV₁ : VG.Proof.Bignum.X86_64.word t₁.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V := by rw [ha₁.hslot (by decide)]; exact hV
  have hb₁ : VG.Proof.Bignum.X86_64.word t₁.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 b := by rw [ha₁.hslot (by decide)]; exact hb
  have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hg₁.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₂ => t₂.zf = some (decide (V / 128 % 2 = 0)) ∧
      t₂.mem = t₁.mem) (by
    unfold bitTest
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl VG.Impl.Bignum.X86_64.Public.sV (by decide), hV₁, VG.Proof.Bignum.X86_64.bit7 V (by omega)]) rfl)
    fun t₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good t₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, hm₂ ▸ hg₁.hdr⟩
  have hc₂ : VG.Proof.Bignum.X86_64.ExpCtx t₂ B Z w minv N X := ⟨hg₂, hm₂ ▸ hc₁.n, hm₂ ▸ hc₁.inv, hm₂ ▸ hc₁.x⟩
  -- `Y := Y X` if the bit is set; the rest as on entry to it.
  have hmul : WP isa (.ite .ne (mm aY aY aXm) (.block [])) t₂ fun t₃ => VG.Proof.Bignum.X86_64.ExpCtx t₃ B Z w minv N X ∧
      wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w < N ∧
      wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = x ^ (2 * E + V / 128 % 2) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aY] t₂.mem t₃.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t₂ t₃ := by
    by_cases hbit : V / 128 % 2 = 0
    · refine WP.ite false (by simp [VG.X86_64.eval, hz₂, hbit]) (by simp) (fun _ => WP.block_nil ⟨hc₂, ?_, ?_,
        fun _ _ => rfl, Keep.refl _ _⟩)
      · rw [hm₂]; exact hlt₁
      · rw [hm₂, hY₁, hbit, Nat.add_zero]
    · refine WP.ite true (by simp [VG.X86_64.eval, hz₂, hbit]) (fun _ => ?_) (by simp)
      refine WP.mono (Mont.base.mm_ok (o := aY) (a := aY) (b := aXm) hg₂ hZ hw hw' (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.inv
        (by rw [hc₂.x, hc₂.n]; exact hXN)) fun t₃ ⟨hg₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_
      rw [hc₂.n] at hlt₃
      rw [hc₂.n, hc₂.x] at hm₃
      refine ⟨hc₂.of_arrays hg₃ hZ (by omega) ha₃, hlt₃, ?_, ha₃, k₃⟩
      rw [show V / 128 % 2 = 1 by omega]
      have hY₂ : wv t₂.mem B (VG.Proof.Bignum.X86_64.slot w aY) w % N = x ^ (2 * E) * 2 ^ (64 * w) % N := by rw [hm₂]; exact hY₁
      exact VG.Proof.Bignum.mont_mulx hR hY₂ hXc hm₃
  refine WP.seq (WP.mono hmul fun t₃ ⟨hc₃, hlt₃, hY₃, ha₃, k₃⟩ => ?_)
  -- The next bit.
  have hV₃ : VG.Proof.Bignum.X86_64.word t₃.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V := by rw [ha₃.hslot (by decide), hm₂]; exact hV₁
  have hb₃ : VG.Proof.Bignum.X86_64.word t₃.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 b := by rw [ha₃.hslot (by decide), hm₂]; exact hb₁
  have hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₃.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₃ : ∀ i < 32, InRegions t₃.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₃.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hV₃' : (t₃.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV)) (BitVec.ofNat 64 (V + V))).readW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit)) 64 =
      BitVec.ofNat 64 b := by
    rw [← hb₃]; exact (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by unfold VG.Impl.Bignum.X86_64.Public.sV VG.Impl.Bignum.X86_64.Public.sBit sFn; omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t₃.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV))
      (BitVec.ofNat 64 (V + V))).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
      t'.zf = some (decide (b - 1 = 0))) (by
    unfold bitNext
    xrun [State.ea, hdr, hc₃.good.rdi, hdrOff, hl₃ VG.Impl.Bignum.X86_64.Public.sV (by decide), hs₃ VG.Impl.Bignum.X86_64.Public.sV (by decide), hV₃, hV₃',
      hs₃ VG.Impl.Bignum.X86_64.Public.sBit (by decide), hl₃ VG.Impl.Bignum.X86_64.Public.sBit (by decide), ← BitVec.ofNat_add,
      ofNat64_pred hb1 (by omega), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t₃.mem B (BitVec.ofNat 64 (V + V)) (d := 8 * VG.Impl.Bignum.X86_64.Public.sV) (by unfold VG.Impl.Bignum.X86_64.Public.sV sFn; omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t₃.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV)) (BitVec.ofNat 64 (V + V))) B
    (BitVec.ofNat 64 (b - 1)) (d := 8 * VG.Impl.Bignum.X86_64.Public.sBit) (by omega)
  have hfr : Frm B (VG.Proof.Bignum.X86_64.bitRanges w) t.mem t'.mem := by
    rw [hm']
    exact (((Frm.of_arrays ha₁ (by simp [VG.Proof.Bignum.X86_64.bitRanges])).trans (by rw [hm₂]; exact Frm.refl _ _ _)).trans
      (Frm.of_arrays ha₃ (by simp [VG.Proof.Bignum.X86_64.bitRanges]))).trans
      ((Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.bitRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.bitRanges])))
  have hgood : Good t' B Z w minv := ⟨hc₃.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hc₃.good.rdi,
    by rw [hm']; exact Hdr.store (Hdr.store hc₃.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  have hY' : wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w aY) w := by
    rw [hm', o2.wv (by unfold VG.Impl.Bignum.X86_64.Public.sBit sFn; have := hdr_lt_slot w aY (show VG.Impl.Bignum.X86_64.Public.sBit < 32 by decide); omega)
      (by have := slot_le (w := w) (show aY < 8 by decide); omega),
      o1.wv (by have := hdr_lt_slot w aY (show VG.Impl.Bignum.X86_64.Public.sV < 32 by decide); omega)
      (by have := slot_le (w := w) (show aY < 8 by decide); omega)]
  refine ⟨?_, ⟨_, hY', hlt₃, hY₃⟩, ?_, ?_, hz', hfr,
    (((k₁.trans k₂).trans k₃).trans k').mono (by decide)⟩
  · -- The header stores are below the arrays: the modulus and `X` are as before.
    have hkeep : ∀ j < 8, j ≠ aY → j ≠ aAcc → j ≠ aTmp →
        wv t'.mem B (VG.Proof.Bignum.X86_64.slot w j) w = wv t₃.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun j hj _ _ _ => by
      rw [hm', o2.wv (by have := hdr_lt_slot w j (show VG.Impl.Bignum.X86_64.Public.sBit < 32 by decide); omega)
        (by have := slot_le (w := w) hj; omega),
        o1.wv (by have := hdr_lt_slot w j (show VG.Impl.Bignum.X86_64.Public.sV < 32 by decide); omega)
        (by have := slot_le (w := w) hj; omega)]
    have hw0 : VG.Proof.Bignum.X86_64.word t'.mem B (VG.Proof.Bignum.X86_64.slot w aN) = VG.Proof.Bignum.X86_64.word t₃.mem B (VG.Proof.Bignum.X86_64.slot w aN) := by
      have := slot_le (w := w) (show aN < 8 by decide)
      rw [hm', o2.word (by have := hdr_lt_slot w aN (show VG.Impl.Bignum.X86_64.Public.sBit < 32 by decide); omega) (by omega),
        o1.word (by have := hdr_lt_slot w aN (show VG.Impl.Bignum.X86_64.Public.sV < 32 by decide); omega) (by omega)]
    exact ⟨hgood, by rw [hkeep aN (by decide) (by decide) (by decide) (by decide)]; exact hc₃.n,
      by rw [hw0]; exact hc₃.inv, by rw [hkeep aXm (by decide) (by decide) (by decide) (by decide)]; exact hc₃.x⟩
  · rw [hm', o2.word (by unfold VG.Impl.Bignum.X86_64.Public.sV VG.Impl.Bignum.X86_64.Public.sBit sFn; omega) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]

/-- After `j` bits of the byte `v` from `t₀`, where `Y ≡ x^E R`. -/
structure BitInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x E v : Nat) (j : Nat)
    (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X
  y : ∃ Y, wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ (E * 2 ^ j + v / 2 ^ (8 - j)) * 2 ^ (64 * w) % N
  v : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 (v * 2 ^ j)
  b : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 (8 - j)
  frm : Frm B (VG.Proof.Bignum.X86_64.bitRanges w) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

/-- Bit `j` of the byte `v`. -/
theorem bitStep_ok {t s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) {j : Nat} (hj : j < 8) (hI : VG.Proof.Bignum.X86_64.BitInv t B Z w minv N X x E v j s) :
    WP isa VG.Impl.Bignum.X86_64.Public.expBit s fun s' => s'.zf = some (decide (j + 1 = 8)) ∧ VG.Proof.Bignum.X86_64.BitInv t B Z w minv N X x E v (j + 1) s' := by
  obtain ⟨Y, hY, hYN, hYc⟩ := hI.y
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (VG.Proof.Bignum.X86_64.expBit_ok hI.ctx hZ hw hw' hR hXN hXc hY hYN hYc hI.v
    (by have := Nat.mul_le_mul_left v hp; omega) hI.b (by omega) (by omega))
    fun s' ⟨hc', ⟨Y', hY', hYN', hYc'⟩, hV', hb', hz', hfr', k'⟩ => ⟨?_, ⟨hc', ⟨Y', hY', hYN', ?_⟩, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [hYc', show 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) by
        rw [Nat.mul_add, Nat.add_assoc, VG.Proof.Bignum.X86_64.bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]]
  · rw [hV', ← Nat.two_mul, Nat.pow_succ]; congr 1; rw [Nat.mul_comm, Nat.mul_assoc]
  · rw [hb']; congr 1

/-- The eight bits of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem bits_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) (h0 : VG.Proof.Bignum.X86_64.BitInv t B Z w minv N X x E v 0 t) :
    WP isa (.loop VG.Impl.Bignum.X86_64.Public.expBit .ne) t (VG.Proof.Bignum.X86_64.BitInv t B Z w minv N X x E v 8) :=
  wp_upto (a := 0) (N := 8) (by decide) (VG.Proof.Bignum.X86_64.BitInv t B Z w minv N X x E v)
    (fun _ _ hj _ hI => VG.Proof.Bignum.X86_64.bitStep_ok hZ hw hw' hR hXN hXc hv hj hI) (fun _ h => h) h0

/-- A store to a header slot keeps the arrays. -/
theorem hdrStore_wv (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32) (hj : j < 8)
    (hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) :
    wv (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) B (VG.Proof.Bignum.X86_64.slot w j) w = wv m B (VG.Proof.Bignum.X86_64.slot w j) w :=
  (VG.Proof.Bignum.X86_64.writeW_outside m B v (by omega)).wv (by have := hdr_lt_slot w j hi; omega)
    (by have := slot_le (w := w) hj; omega)

theorem hdrStore_word (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32) (hj : j < 8)
    (hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) B (VG.Proof.Bignum.X86_64.slot w j) = VG.Proof.Bignum.X86_64.word m B (VG.Proof.Bignum.X86_64.slot w j) :=
  (VG.Proof.Bignum.X86_64.writeW_outside m B v (by omega)).word (by have := hdr_lt_slot w j hi; omega)
    (by have := slot_le (w := w) hj; omega)

/-- Another header slot. -/
theorem hdrStore_hdr (m : Mem) (B : Addr) {i k : Nat} (v : BitVec 64) (hi : i < 32) (hk : k < 32)
    (hik : i ≠ k) : VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) B (8 * k) = VG.Proof.Bignum.X86_64.word m B (8 * k) :=
  (VG.Proof.Bignum.X86_64.writeW_outside m B v (by omega)).word (by omega) (by omega)

/-- `ExpCtx` after a store to a slot of the functions' own. -/
theorem ExpCtx.store {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32)
    {v : BitVec 64} (hm : t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = B) : VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X := by
  have hn : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  exact ⟨⟨hc.good.scr.congr hwr, hdi, hm ▸ Hdr.store hc.good.hdr hi hi' v⟩,
    by rw [hm, VG.Proof.Bignum.X86_64.hdrStore_wv _ _ _ hi' (by decide) hn]; exact hc.n,
    by rw [hm, VG.Proof.Bignum.X86_64.hdrStore_word _ _ _ hi' (by decide) hn]; exact hc.inv,
    by rw [hm, VG.Proof.Bignum.X86_64.hdrStore_wv _ _ _ hi' (by decide) hn]; exact hc.x⟩

/-- After `i` bytes of `e` (`L` bytes `eb` at `ep`) from `t₀`. -/
structure ByteInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x : Nat) (ep : Addr)
    (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X
  y : ∃ Y, wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ VG.Proof.Bignum.X86_64.pre eb i * 2 ^ (64 * w) % N
  idx : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sI) = BitVec.ofNat 64 i
  e : VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = ep
  len : VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = BitVec.ofNat 64 L
  frm : Frm B (VG.Proof.Bignum.X86_64.expRanges w) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

theorem expRanges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.expRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  have h := hdr_lt_slot w 0 (i := VG.Impl.Bignum.X86_64.Public.sBit) (by decide)
  have h1 := slot_le (w := w) (show aAcc < 8 by decide)
  have h2 := slot_le (w := w) (show aTmp < 8 by decide)
  have h3 := slot_le (w := w) (show aY < 8 by decide)
  have h4 : VG.Proof.Bignum.X86_64.slot w 0 ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  simp only [VG.Proof.Bignum.X86_64.expRanges, VG.Proof.Bignum.X86_64.bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [VG.Impl.Bignum.X86_64.Public.sI, VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sFn] at * <;> omega

theorem bitRanges_sub (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.bitRanges w, r ∈ VG.Proof.Bignum.X86_64.expRanges w :=
  fun _ hr => List.mem_cons_of_mem _ hr

/-- A header slot that a bit of the exponentiation does not change. -/
theorem bitRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ VG.Impl.Bignum.X86_64.Public.sV) (h2 : k ≠ VG.Impl.Bignum.X86_64.Public.sBit) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.bitRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have h := hdr_lt_slot w aAcc hk
  have h' := hdr_lt_slot w aTmp hk
  have h'' := hdr_lt_slot w aY hk
  simp only [VG.Proof.Bignum.X86_64.bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [VG.Impl.Bignum.X86_64.Public.sV, VG.Impl.Bignum.X86_64.Public.sBit, sFn] at * <;> omega

theorem expRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ VG.Impl.Bignum.X86_64.Public.sI) (h1 : k ≠ VG.Impl.Bignum.X86_64.Public.sV) (h2 : k ≠ VG.Impl.Bignum.X86_64.Public.sBit) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [VG.Impl.Bignum.X86_64.Public.sI, sFn] at *; omega
  · exact VG.Proof.Bignum.X86_64.bitRanges_hdr w hk h1 h2 r hr

theorem byteRead (ep : Addr) (i : Nat) :
    ep + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = ep + BitVec.ofNat 64 i := by
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
    BitVec.add_zero]

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 (b.toNat * 2 ^ 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.pow_zero, Nat.mul_one,
    Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem sw8 : BitVec.setWidth 64 (8 : BitVec 32) = BitVec.ofNat 64 (8 - 0) := rfl

theorem byteHead_eq : byteHead = ([.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))] : List Instr) ++
    ([.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax, .mov32 .rax (.imm 8),
      .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax] : List Instr) := rfl

/-- `byteHead`'s loads: `e` and the byte index. -/
theorem byteHead1_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hI : VG.Proof.Bignum.X86_64.ByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ VG.Proof.Bignum.X86_64.ByteInv t₀ B Z w minv N X x ep L eb i t₁ := by
  have hc := hI.ctx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sE (by decide), hl VG.Impl.Bignum.X86_64.Public.sI (by decide), hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  exact ⟨⟨⟨hc.good.scr.congr k.2.2, (k.gpr (by decide)).trans hc.good.rdi, hm ▸ hc.good.hdr⟩, hm ▸ hc.n,
    hm ▸ hc.inv, hm ▸ hc.x⟩, hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e, hm ▸ hI.len, hm ▸ hI.frm,
    (hI.keep.trans k).mono (by decide)⟩

/-- `byteHead`'s byte of `e` into `sV`, and the bit count 8: the start of the
bits. -/
theorem byteHead2_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ VG.Proof.Bignum.X86_64.ofs B (ep + BitVec.ofNat 64 i))
    (hI : VG.Proof.Bignum.X86_64.ByteInv t₀ B Z w minv N X x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax,
      .mov32 .rax (.imm 8), .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV)) ((eb[i]'(by omega)).setWidth 64)).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit))
        (BitVec.setWidth 64 (8 : BitVec 32)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t₁ ∧
      VG.Proof.Bignum.X86_64.BitInv t₁ B Z w minv N X x (VG.Proof.Bignum.X86_64.pre eb i) (eb[i]'(by omega)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hs : ∀ i < 32, InRegions t.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := VG.Proof.Bignum.X86_64.expRanges_le w r hr; have := hout i hi; omega)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV))
      ((eb[i]'(by omega)).setWidth 64)).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit)) (BitVec.setWidth 64 (8 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hax, hcx, VG.Proof.Bignum.X86_64.byteRead, hrdi, hbi, hs VG.Impl.Bignum.X86_64.Public.sV (by decide),
      hs VG.Impl.Bignum.X86_64.Public.sBit (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have hc₁ : VG.Proof.Bignum.X86_64.ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hc.good.rdi,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_word (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_word (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aXm) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  obtain ⟨Y, hY, hYN, hYc⟩ := hI.y
  refine ⟨hc₁, ⟨Y, ?_, hYN, ?_⟩, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aY) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hY
  · rw [hYc, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 2 ^ 8 from hv), Nat.add_zero]
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sBit) (k := VG.Impl.Bignum.X86_64.Public.sV) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.word_writeW_self, VG.Proof.Bignum.X86_64.setWidth_byte]
  · rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl

/-- One byte of `e`: its eight bits, then the next byte. -/
theorem byte_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} {i : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ VG.Proof.Bignum.X86_64.ofs B (ep + BitVec.ofNat 64 i))
    (hI : VG.Proof.Bignum.X86_64.ByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.seq (.block byteHead) (.seq (.loop VG.Impl.Bignum.X86_64.Public.expBit .ne) (.block byteNext))) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ VG.Proof.Bignum.X86_64.ByteInv t₀ B Z w minv N X x ep L eb (i + 1) t' := by
  have hn := hI.ctx.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  rw [VG.Proof.Bignum.X86_64.byteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (VG.Proof.Bignum.X86_64.byteHead1_ok hZ hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (VG.Proof.Bignum.X86_64.byteHead2_ok hZ hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.bits_ok hZ hw hw' hR hXN hXc hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₂ : ∀ i < 32, InRegions t₂.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hh₂ : ∀ k < 32, k ≠ VG.Impl.Bignum.X86_64.Public.sV → k ≠ VG.Impl.Bignum.X86_64.Public.sBit → VG.Proof.Bignum.X86_64.word t₂.mem B (8 * k) = VG.Proof.Bignum.X86_64.word tₐ.mem B (8 * k) := fun k hk h1 h2 => by
    rw [h₂.frm.word_eq (VG.Proof.Bignum.X86_64.bitRanges_hdr w hk h1 h2) (by omega), hm₁,
      VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sBit) _ _ _ (by decide) hk (Ne.symm h2),
      VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ VG.Impl.Bignum.X86_64.Public.sI (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ sE (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ sElen (by decide) (by decide) (by decide)).trans hIₐ.len
  have hlen₂' : (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sI)) (BitVec.ofNat 64 (i + 1))).readW (VG.Proof.Bignum.X86_64.off B (8 * sElen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    unfold byteNext
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hl₂ VG.Impl.Bignum.X86_64.Public.sI (by decide), hs₂ VG.Impl.Bignum.X86_64.Public.sI (by decide), hidx₂,
      ofNat_add_one, hl₂ sElen (by decide), hlen₂', ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega)
      (show L < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  obtain ⟨Y₂, hY₂, hYN₂, hYc₂⟩ := h₂.y
  refine ⟨ExpCtx.store hc₂ hZ (i := VG.Impl.Bignum.X86_64.Public.sI) (by decide) (by decide) hm' k'.2.2 ((k'.gpr (by decide)).trans
    hc₂.good.rdi), ⟨Y₂, ?_, hYN₂, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm', VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sI) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hY₂
  · rw [hYc₂, VG.Proof.Bignum.X86_64.pre_succ eb (by omega), Nat.pow_zero, Nat.div_one, Nat.mul_comm (VG.Proof.Bignum.X86_64.pre eb i)]; rfl
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm', VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm B (VG.Proof.Bignum.X86_64.expRanges w) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside tₐ.mem B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sV) (by unfold VG.Impl.Bignum.X86_64.Public.sV sFn; omega)) (by simp [VG.Proof.Bignum.X86_64.expRanges, VG.Proof.Bignum.X86_64.bitRanges])).trans
        (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sBit) (by unfold VG.Impl.Bignum.X86_64.Public.sBit sFn; omega)) (by simp [VG.Proof.Bignum.X86_64.expRanges, VG.Proof.Bignum.X86_64.bitRanges]))
    have f₃ : Frm B (VG.Proof.Bignum.X86_64.expRanges w) t₂.mem t'.mem := by
      rw [hm']; exact Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sI) (by unfold VG.Impl.Bignum.X86_64.Public.sI sFn; omega)) (by simp [VG.Proof.Bignum.X86_64.expRanges])
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (VG.Proof.Bignum.X86_64.bitRanges_sub w))).trans f₃
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-- `expLoop`'s start: byte index 0. -/
theorem expInit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x Y : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z)
    (hY : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y) (hYN : Y < N) (hYc : Y % N = 2 ^ (64 * w) % N)
    (he : VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = ep) (hlen : VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (hdr VG.Impl.Bignum.X86_64.Public.sI) .rax]) t
      (VG.Proof.Bignum.X86_64.ByteInv t B Z w minv N X x ep L eb 0) := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sI))
      (BitVec.setWidth 64 (0 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff,
      hc.good.scr.st (d := 8 * VG.Impl.Bignum.X86_64.Public.sI) (by have := hdr_lt_slot w 8 (show VG.Impl.Bignum.X86_64.Public.sI < 32 by decide); omega)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  refine ⟨ExpCtx.store hc hZ (i := VG.Impl.Bignum.X86_64.Public.sI) (by decide) (by decide) hm₁ k₁.2.2
      ((k₁.gpr (by decide)).trans hc.good.rdi), ⟨Y, ?_, hYN, ?_⟩, ?_, ?_, ?_, ?_, k₁.mono (by decide)⟩
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sI) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hY
  · rw [hYc, VG.Proof.Bignum.X86_64.pre_zero, Nat.pow_zero, Nat.one_mul]
  · rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen
  · rw [hm₁]; exact Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sI) (by unfold VG.Impl.Bignum.X86_64.Public.sI sFn; omega))
      (by simp [VG.Proof.Bignum.X86_64.expRanges])

/-- The exponentiation: `Y ≡ R` becomes `Y ≡ x^e R`, for the `L` bytes `eb`
of `e` at `ep`, outside the working space. -/
theorem expLoop_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x Y : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N)
    (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hY : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y) (hYN : Y < N) (hYc : Y % N = 2 ^ (64 * w) % N)
    (he : VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = ep) (hlen : VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ VG.Proof.Bignum.X86_64.ofs B (ep + BitVec.ofNat 64 i)) :
    WP isa VG.Impl.Bignum.X86_64.Public.expLoop t fun t' => VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X ∧
      (∃ Y', wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = Y' ∧ Y' < N ∧
        Y' % N = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * w) % N) ∧
      Frm B (VG.Proof.Bignum.X86_64.expRanges w) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  unfold VG.Impl.Bignum.X86_64.Public.expLoop
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.expInit_ok (x := x) (eb := eb) hc hZ hY hYN hYc he hlen) fun t₁ h₁ => ?_)
  refine wp_upto (a := 0) (N := L) (by omega) (VG.Proof.Bignum.X86_64.ByteInv t B Z w minv N X x ep L eb)
    (fun i _ hi s hI => VG.Proof.Bignum.X86_64.byte_ok hZ hw hw' hR hXN hXc hL hL' hi hrd hbytes hout hI)
    (fun s hI => ?_) h₁
  obtain ⟨Y', h1, h2, h3⟩ := hI.y
  exact ⟨hI.ctx, ⟨Y', h1, h2, by rw [h3, ← hL, VG.Proof.Bignum.X86_64.pre_len]⟩, hI.frm, hI.keep⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.PdExp`. -/
section

/-!
# `vg_rsa_public_precomputed` on x86-64: the exponentiation

The exponentiation of `vg_rsa_public_precomputed` starts at the first set bit
of `e`: until then `Y` is not used (`YSt`); at that bit `Y := X`, and after
it each bit squares `Y` and multiplies it by `X` if set (`pExpBit_ok`, over
the bits and bytes of `e` in `pExpLoop_ok`). `finish` leaves `x^e mod N`
(`pFinish_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-- What a bit of the exponentiation changes: also whether it started. -/
def pBitRanges (w : Nat) : List (Nat × Nat) := (8 * sStarted, 8) :: VG.Proof.Bignum.X86_64.bitRanges w

/-- What `start` changes. -/
def startRanges (w : Nat) : List (Nat × Nat) := [(VG.Proof.Bignum.X86_64.slot w aY, 8 * (w + 2)), (8 * sStarted, 8)]

theorem startRanges_sub (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.startRanges w, r ∈ VG.Proof.Bignum.X86_64.pBitRanges w := by
  simp [VG.Proof.Bignum.X86_64.startRanges, VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges]

/-- `Y` after the prefix `E` of `e`: unused, and not started, while `E = 0`;
started, and `x^E R` modulo `N`, after. -/
def YSt (m : Mem) (B : Addr) (w N x E : Nat) : Prop :=
  (E = 0 ∧ VG.Proof.Bignum.X86_64.word m B (8 * sStarted) = 0) ∨
    (E ≠ 0 ∧ VG.Proof.Bignum.X86_64.word m B (8 * sStarted) = 1 ∧
      ∃ Y, wv m B (VG.Proof.Bignum.X86_64.slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ E * 2 ^ (64 * w) % N)

theorem YSt.started {m : Mem} {B : Addr} {w N x E : Nat} (h : VG.Proof.Bignum.X86_64.YSt m B w N x E) :
    VG.Proof.Bignum.X86_64.word m B (8 * sStarted) = if E = 0 then 0 else 1 := by
  rcases h with ⟨h0, hs⟩ | ⟨h0, hs, -⟩
  · rw [hs]; simp [h0]
  · rw [hs]; simp [h0]

theorem started_test (E : Nat) :
    ((if E = 0 then (0 : BitVec 64) else 1) &&& (if E = 0 then (0 : BitVec 64) else 1) == 0) =
      decide (E = 0) := by
  by_cases h : E = 0 <;> simp [h]

/-- Whether the exponentiation started, into ZF. -/
theorem startedTest_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N x E : Nat}
    (hg : Good t B Z w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hy : VG.Proof.Bignum.X86_64.YSt t.mem B w N x E) :
    WP isa (.block startedTest) t fun t' => t'.zf = some (decide (E = 0)) ∧ t'.mem = t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  have hn := hg.scr.nowrap
  have hl : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off B (8 * sStarted)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (E = 0)) ∧ t'.mem = t.mem) (by
    unfold startedTest
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hy.started, VG.Proof.Bignum.X86_64.started_test]) rfl)
    fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩

/-- `start`: `Y := X`, and the exponentiation started. -/
theorem start_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa start t fun t' => VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X ∧ wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = X ∧
      VG.Proof.Bignum.X86_64.word t'.mem B (8 * sStarted) = 1 ∧ Frm B (VG.Proof.Bignum.X86_64.startRanges w) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hs := hc.good.scr
  have hn := hs.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hX := slot_le (w := w) (show aXm < 8 by decide)
  have hY := slot_le (w := w) (show aY < 8 by decide)
  have hXY : VG.Proof.Bignum.X86_64.slot w aXm + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aY := by unfold VG.Proof.Bignum.X86_64.slot aXm aY; omega
  have hYs := hdr_lt_slot w aY (show sStarted < 32 by decide)
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold start
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 w ∧
      t₁.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aXm) ∧ t₁.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aY) ∧ t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide),
      hl (sArr aY) (by decide), hc.good.hdr.hw, hc.good.hdr.harr aXm (by decide),
      hc.good.hdr.harr aY (by decide)]) rfl)
    fun t₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega)
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact hs.ld (by omega))
    (fun j hj => by rw [k₁.2.2]; exact hs.st (by omega))
    (fun j hj b hb => Or.inl (by rw [VG.Proof.Bignum.X86_64.ofs_off B (d := VG.Proof.Bignum.X86_64.slot w aXm + 8 * j) (i := b) (by omega)]; omega)))
    fun t₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  rw [hm₁, hc.x] at hv₂
  rw [hm₁] at ho₂
  have k12 := k₁.trans k₂
  have ha₂ : Arrays B w [aAcc, aTmp, aY] t.mem t₂.mem :=
    Arrays.of_outside (j := aY) (by simp) ho₂ (Nat.le_refl _) (by omega)
  have hc₂ : VG.Proof.Bignum.X86_64.ExpCtx t₂ B Z w minv N X := hc.of_arrays ⟨hs.congr k12.2.2,
    (k12.gpr (by decide)).trans hc.good.rdi, ha₂.hdr hc.good.hdr⟩ hZ hw ha₂
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * sStarted))
      (BitVec.setWidth 64 (1 : BitVec 32))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff,
      hc₂.good.scr.st (d := 8 * sStarted) (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega)])
    rfl) fun t' ⟨hm', k'⟩ => ?_
  refine ⟨ExpCtx.store hc₂ hZ (i := sStarted) (by decide) (by decide) hm' k'.2.2
    ((k'.gpr (by decide)).trans hc₂.good.rdi), ?_, by rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]; rfl, ?_,
    (k12.trans k').mono (by decide)⟩
  · rw [hm', VG.Proof.Bignum.X86_64.hdrStore_wv (i := sStarted) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hv₂
  · rw [hm']
    exact (Frm.of_outside (ho₂.mono (o' := VG.Proof.Bignum.X86_64.slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [VG.Proof.Bignum.X86_64.startRanges])).trans
      (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sStarted) (by omega)) (by simp [VG.Proof.Bignum.X86_64.startRanges]))

/-- `YSt` in memory with the same `Y` and the same flag. -/
theorem YSt.congr {m m' : Mem} {B : Addr} {w N x E : Nat} (h : VG.Proof.Bignum.X86_64.YSt m B w N x E)
    (hs : VG.Proof.Bignum.X86_64.word m' B (8 * sStarted) = VG.Proof.Bignum.X86_64.word m B (8 * sStarted)) (hy : wv m' B (VG.Proof.Bignum.X86_64.slot w aY) w = wv m B (VG.Proof.Bignum.X86_64.slot w aY) w) :
    VG.Proof.Bignum.X86_64.YSt m' B w N x E := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1, Y, h2, h3, h4⟩
  · exact .inl ⟨h0, hs.trans h1⟩
  · exact .inr ⟨h0, hs.trans h1, Y, hy.trans h2, h3, h4⟩

theorem ExpCtx.mem {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hm : t'.mem = t.mem) {regs : List Reg} (k : VG.Proof.MlKem.X86_64.Keep regs t t')
    (hr : .rdi ∉ regs) : VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X :=
  ⟨⟨hc.good.scr.congr k.2.2, (k.gpr hr).trans hc.good.rdi, hm ▸ hc.good.hdr⟩, hm ▸ hc.n, hm ▸ hc.inv, hm ▸ hc.x⟩

theorem pBitRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ VG.Impl.Bignum.X86_64.Public.sV) (h2 : k ≠ VG.Impl.Bignum.X86_64.Public.sBit) (h3 : k ≠ sStarted) :
    ∀ r ∈ VG.Proof.Bignum.X86_64.pBitRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sStarted, sFn] at *; omega
  · exact VG.Proof.Bignum.X86_64.bitRanges_hdr w hk h1 h2 r hr

/-- `Y := Y²` once started. -/
theorem pSq_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hy : VG.Proof.Bignum.X86_64.YSt t.mem B w N x E) (hz : t.zf = some (decide (E = 0))) :
    WP isa (.ite .ne (M.mm aY aY aY) (.block [])) t fun t' => VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X ∧
      VG.Proof.Bignum.X86_64.YSt t'.mem B w N x (2 * E) ∧ Arrays B w [aAcc, aTmp, aY] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  rcases hy with ⟨h0, hs0⟩ | ⟨h0, hs1, Y, hY, hYN, hYc⟩
  · refine WP.ite false (by simp [VG.X86_64.eval, hz, h0]) (by simp) (fun _ => WP.block_nil ⟨hc, ?_,
      fun _ _ => rfl, Keep.refl _ _⟩)
    exact .inl ⟨by omega, hs0⟩
  · refine WP.ite true (by simp [VG.X86_64.eval, hz, h0]) (fun _ => ?_) (by simp)
    refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n, hY]; exact hYN)) fun t₂ ⟨hg₂, hlt₂, hmm₂, ha₂, k₂⟩ => ?_
    rw [hc.n] at hlt₂
    rw [hc.n, hY] at hmm₂
    exact ⟨hc.of_arrays hg₂ hZ (by omega) ha₂, .inr ⟨by omega, by rw [ha₂.hslot (by decide)]; exact hs1,
      _, rfl, hlt₂, VG.Proof.Bignum.mont_sq hR hYc hmm₂⟩, ha₂, k₂⟩

/-- If the bit is set, `Y := Y X` once started, or `Y := X` and started. -/
theorem pMul_ok {t₃ : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E V : Nat}
    (hc₃ : VG.Proof.Bignum.X86_64.ExpCtx t₃ B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hy₃ : VG.Proof.Bignum.X86_64.YSt t₃.mem B w N x (2 * E)) (hz₃ : t₃.zf = some (decide (V / 128 % 2 = 0))) :
    WP isa (.ite .ne (.seq (.block startedTest) (.ite .ne (M.mm aY aY aXm) start)) (.block [])) t₃
      fun t₄ => VG.Proof.Bignum.X86_64.ExpCtx t₄ B Z w minv N X ∧ VG.Proof.Bignum.X86_64.YSt t₄.mem B w N x (2 * E + V / 128 % 2) ∧
        Frm B (VG.Proof.Bignum.X86_64.pBitRanges w) t₃.mem t₄.mem ∧ (∀ k < 32, k ≠ sStarted → VG.Proof.Bignum.X86_64.word t₄.mem B (8 * k) = VG.Proof.Bignum.X86_64.word t₃.mem B (8 * k)) ∧
        VG.Proof.MlKem.X86_64.Keep mmRegs t₃ t₄ := by
  have hn := hc₃.good.scr.nowrap
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot w 0 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  by_cases hbit : V / 128 % 2 = 0
  · refine WP.ite false (by simp [VG.X86_64.eval, hz₃, hbit]) (by simp) (fun _ => WP.block_nil ⟨hc₃, ?_,
      Frm.refl _ _ _, fun _ _ _ => rfl, Keep.refl _ _⟩)
    rw [hbit, Nat.add_zero]; exact hy₃
  · refine WP.ite true (by simp [VG.X86_64.eval, hz₃, hbit]) (fun _ => ?_) (by simp)
    rw [show V / 128 % 2 = 1 by omega]
    refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.startedTest_ok hc₃.good hZ hy₃) fun t₄ ⟨hz₄, hm₄, k₄⟩ => ?_)
    have hc₄ := hc₃.mem hm₄ k₄ (by decide)
    rcases hy₃ with ⟨h0, hs0⟩ | ⟨h0, hs1, Y, hY, hYN, hYc⟩
    · refine WP.ite false (by simp [VG.X86_64.eval, hz₄, h0]) (by simp) (fun _ => ?_)
      refine WP.mono (VG.Proof.Bignum.X86_64.start_ok hc₄ hZ (by omega) hw') fun t₅ ⟨hc₅, hv₅, hs₅, hf₅, k₅⟩ => ?_
      refine ⟨hc₅, .inr ⟨by omega, hs₅, X, hv₅, hXN, by rw [show 2 * E + 1 = 1 by omega, Nat.pow_one]; exact hXc⟩,
        by rw [← hm₄]; exact hf₅.mono (VG.Proof.Bignum.X86_64.startRanges_sub w), fun k hk hk' => ?_, (k₄.trans k₅).mono (by decide)⟩
      rw [hf₅.word_eq (fun r hr => by
        simp only [VG.Proof.Bignum.X86_64.startRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hdr_lt_slot w aY hk
        rcases hr with rfl | rfl
        · omega
        · simp only [sStarted, sFn] at hk' ⊢; omega) (by omega), hm₄]
    · refine WP.ite true (by simp [VG.X86_64.eval, hz₄, h0]) (fun _ => ?_) (by simp)
      refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aXm) hc₄.good hZ hw hw' (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc₄.inv
        (by rw [hc₄.x, hc₄.n]; exact hXN)) fun t₅ ⟨hg₅, hlt₅, hmm₅, ha₅, k₅⟩ => ?_
      rw [hc₄.n] at hlt₅
      rw [hc₄.n, hc₄.x, hm₄, hY] at hmm₅
      refine ⟨hc₄.of_arrays hg₅ hZ (by omega) ha₅, .inr ⟨by omega, by rw [ha₅.hslot (by decide), hm₄]; exact hs1,
        _, rfl, hlt₅, VG.Proof.Bignum.mont_mulx hR hYc hXc hmm₅⟩,
        by rw [← hm₄]; exact Frm.of_arrays ha₅ (by simp [VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges]),
        fun k hk _ => by rw [ha₅.hslot hk, hm₄], (k₄.trans k₅).mono (by decide)⟩

/-- One bit of `e`: `YSt` for the prefix `E` becomes `YSt` for `2 E + bit`,
for the bit at the top of the byte `V / 128 mod 2`; `V` doubles and the bit
count `b` drops. -/
theorem pExpBit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E V b : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hy : VG.Proof.Bignum.X86_64.YSt t.mem B w N x E)
    (hV : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62)
    (hb : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa (Precomputed.expBit M.mm) t fun t' => VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X ∧ VG.Proof.Bignum.X86_64.YSt t'.mem B w N x (2 * E + V / 128 % 2) ∧
      VG.Proof.Bignum.X86_64.word t'.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 (V + V) ∧ VG.Proof.Bignum.X86_64.word t'.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm B (VG.Proof.Bignum.X86_64.pBitRanges w) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have eV : VG.Impl.Bignum.X86_64.Public.sV = 25 := rfl
  have eB : VG.Impl.Bignum.X86_64.Public.sBit = 24 := rfl
  have eS : sStarted = 27 := rfl
  have h8 : 256 ≤ VG.Proof.Bignum.X86_64.slot w 0 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  unfold Precomputed.expBit
  -- Whether started.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.startedTest_ok hc.good hZ hy) fun t₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have hc₁ := hc.mem hm₁ k₁ (by decide)
  -- `Y := Y²` if started.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.pSq_ok (x := x) hc₁ hZ hw hw' hR (by rw [hm₁]; exact hy) hz₁) fun t₂ ⟨hc₂, hy₂, ha₂, k₂⟩ => ?_)
  have hV₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V := by rw [ha₂.hslot (by decide), hm₁]; exact hV
  have hb₂ : VG.Proof.Bignum.X86_64.word t₂.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 b := by rw [ha₂.hslot (by decide), hm₁]; exact hb
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₃ => t₃.zf = some (decide (V / 128 % 2 = 0)) ∧
      t₃.mem = t₂.mem) (by
    unfold bitTest
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hl₂ VG.Impl.Bignum.X86_64.Public.sV (by decide), hV₂, VG.Proof.Bignum.X86_64.bit7 V (by omega)]) rfl)
    fun t₃ ⟨⟨hz₃, hm₃⟩, k₃⟩ => ?_)
  have hc₃ := hc₂.mem hm₃ k₃ (by decide)
  have hy₃ : VG.Proof.Bignum.X86_64.YSt t₃.mem B w N x (2 * E) := by rw [hm₃]; exact hy₂
  -- If the bit is set: `Y := Y X` if started, `Y := X` and started if not.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.pMul_ok hc₃ hZ hw hw' hR hXN hXc hy₃ hz₃) fun t₄ ⟨hc₄, hy₄, hf₄, hh₄, k₄⟩ => ?_)
  -- The next bit.
  have hV₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 V := by
    rw [hh₄ VG.Impl.Bignum.X86_64.Public.sV (by decide) (by decide), hm₃]; exact hV₂
  have hb₄ : VG.Proof.Bignum.X86_64.word t₄.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 b := by
    rw [hh₄ VG.Impl.Bignum.X86_64.Public.sBit (by decide) (by decide), hm₃]; exact hb₂
  have hl₄ : ∀ i < 32, InRegions (t₄.rd ++ t₄.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₄.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₄ : ∀ i < 32, InRegions t₄.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₄.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hV₄' : (t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV)) (BitVec.ofNat 64 (V + V))).readW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit)) 64 =
      BitVec.ofNat 64 b := by
    rw [← hb₄]; exact (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by unfold VG.Impl.Bignum.X86_64.Public.sV VG.Impl.Bignum.X86_64.Public.sBit sFn; omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV))
      (BitVec.ofNat 64 (V + V))).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
      t'.zf = some (decide (b - 1 = 0))) (by
    unfold bitNext
    xrun [State.ea, hdr, hc₄.good.rdi, hdrOff, hl₄ VG.Impl.Bignum.X86_64.Public.sV (by decide), hs₄ VG.Impl.Bignum.X86_64.Public.sV (by decide), hV₄, hV₄',
      hs₄ VG.Impl.Bignum.X86_64.Public.sBit (by decide), hl₄ VG.Impl.Bignum.X86_64.Public.sBit (by decide), ← BitVec.ofNat_add,
      ofNat64_pred hb1 (by omega), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside t₄.mem B (BitVec.ofNat 64 (V + V)) (d := 8 * VG.Impl.Bignum.X86_64.Public.sV) (by unfold VG.Impl.Bignum.X86_64.Public.sV sFn; omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (t₄.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV)) (BitVec.ofNat 64 (V + V))) B
    (BitVec.ofNat 64 (b - 1)) (d := 8 * VG.Impl.Bignum.X86_64.Public.sBit) (by omega)
  have hkeep : ∀ j < 8, wv t'.mem B (VG.Proof.Bignum.X86_64.slot w j) w = wv t₄.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun j hj => by
    rw [hm', o2.wv (by have := hdr_lt_slot w j (show VG.Impl.Bignum.X86_64.Public.sBit < 32 by decide); omega)
      (by have := slot_le (w := w) hj; omega),
      o1.wv (by have := hdr_lt_slot w j (show VG.Impl.Bignum.X86_64.Public.sV < 32 by decide); omega)
      (by have := slot_le (w := w) hj; omega)]
  have hw0 : VG.Proof.Bignum.X86_64.word t'.mem B (VG.Proof.Bignum.X86_64.slot w aN) = VG.Proof.Bignum.X86_64.word t₄.mem B (VG.Proof.Bignum.X86_64.slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm', o2.word (by have := hdr_lt_slot w aN (show VG.Impl.Bignum.X86_64.Public.sBit < 32 by decide); omega) (by omega),
      o1.word (by have := hdr_lt_slot w aN (show VG.Impl.Bignum.X86_64.Public.sV < 32 by decide); omega) (by omega)]
  have hst' : VG.Proof.Bignum.X86_64.word t'.mem B (8 * sStarted) = VG.Proof.Bignum.X86_64.word t₄.mem B (8 * sStarted) := by
    rw [hm', VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sBit) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sV) _ _ _ (by decide) (by decide) (by decide)]
  have hgood : Good t' B Z w minv := ⟨hc₄.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hc₄.good.rdi,
    by rw [hm']; exact Hdr.store (Hdr.store hc₄.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  refine ⟨⟨hgood, by rw [hkeep aN (by decide)]; exact hc₄.n, by rw [hw0]; exact hc₄.inv,
    by rw [hkeep aXm (by decide)]; exact hc₄.x⟩, YSt.congr hy₄ hst' (hkeep aY (by decide)), ?_, ?_, hz', ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · rw [hm', o2.word (by unfold VG.Impl.Bignum.X86_64.Public.sV VG.Impl.Bignum.X86_64.Public.sBit sFn; omega) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm']
    exact ((((by rw [hm₁]; exact Frm.refl _ _ _ : Frm B (pBitRanges w) t.mem t₁.mem).trans
      (Frm.of_arrays ha₂ (by simp [VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges]))).trans (by rw [hm₃]; exact Frm.refl _ _ _)).trans hf₄).trans
      ((Frm.of_outside o1 (by simp [VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges])).trans (Frm.of_outside o2 (by simp [VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges])))

/-! ## The bits of a byte -/

/-- After `j` bits of the byte `v` from `t₀`, after the prefix `E`. -/
structure PBitInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x E v : Nat) (j : Nat)
    (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X
  y : VG.Proof.Bignum.X86_64.YSt t.mem B w N x (E * 2 ^ j + v / 2 ^ (8 - j))
  v : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sV) = BitVec.ofNat 64 (v * 2 ^ j)
  b : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sBit) = BitVec.ofNat 64 (8 - j)
  frm : Frm B (VG.Proof.Bignum.X86_64.pBitRanges w) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

/-- Bit `j` of the byte `v`. -/
theorem pBitStep_ok {t s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) {j : Nat} (hj : j < 8) (hI : VG.Proof.Bignum.X86_64.PBitInv t B Z w minv N X x E v j s) :
    WP isa (Precomputed.expBit M.mm) s fun s' => s'.zf = some (decide (j + 1 = 8)) ∧
      VG.Proof.Bignum.X86_64.PBitInv t B Z w minv N X x E v (j + 1) s' := by
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (VG.Proof.Bignum.X86_64.pExpBit_ok hI.ctx hZ hw hw' hR hXN hXc hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega) hI.b (by omega) (by omega))
    fun s' ⟨hc', hy', hV', hb', hz', hfr', k'⟩ => ⟨?_, ⟨hc', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by decide)⟩⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · rwa [show 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) by
        rw [Nat.mul_add, Nat.add_assoc, VG.Proof.Bignum.X86_64.bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]] at hy'
  · rw [hV', ← Nat.two_mul, Nat.pow_succ]; congr 1; rw [Nat.mul_comm, Nat.mul_assoc]
  · rw [hb']; congr 1

theorem pBits_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) (h0 : VG.Proof.Bignum.X86_64.PBitInv t B Z w minv N X x E v 0 t) :
    WP isa (.loop (Precomputed.expBit M.mm) .ne) t (VG.Proof.Bignum.X86_64.PBitInv t B Z w minv N X x E v 8) :=
  wp_upto (a := 0) (N := 8) (by decide) (VG.Proof.Bignum.X86_64.PBitInv t B Z w minv N X x E v)
    (fun _ _ hj _ hI => VG.Proof.Bignum.X86_64.pBitStep_ok hZ hw hw' hR hXN hXc hv hj hI) (fun _ h => h) h0

/-! ## The bytes -/

/-- What the exponentiation changes: also the byte index. -/
def pExpRanges (w : Nat) : List (Nat × Nat) := (8 * VG.Impl.Bignum.X86_64.Public.sI, 8) :: VG.Proof.Bignum.X86_64.pBitRanges w

/-- After `i` bytes of `e` (`L` bytes `eb` at `ep`) from `t₀`. -/
structure PByteInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x : Nat) (ep : Addr)
    (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X
  y : VG.Proof.Bignum.X86_64.YSt t.mem B w N x (VG.Proof.Bignum.X86_64.pre eb i)
  idx : VG.Proof.Bignum.X86_64.word t.mem B (8 * VG.Impl.Bignum.X86_64.Public.sI) = BitVec.ofNat 64 i
  e : VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = ep
  len : VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = BitVec.ofNat 64 L
  frm : Frm B (VG.Proof.Bignum.X86_64.pExpRanges w) t₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep mmRegs t₀ t

theorem pExpRanges_le (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.pExpRanges w, r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot w 0 (i := VG.Impl.Bignum.X86_64.Public.sI) (by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot w 0 (i := sStarted) (by decide); have := slot_le (w := w) (show 0 < 8 by decide)
    omega
  · exact VG.Proof.Bignum.X86_64.expRanges_le w r (List.mem_cons_of_mem _ hr)

theorem pExpRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ VG.Impl.Bignum.X86_64.Public.sI) (h1 : k ≠ VG.Impl.Bignum.X86_64.Public.sV) (h2 : k ≠ VG.Impl.Bignum.X86_64.Public.sBit)
    (h3 : k ≠ sStarted) : ∀ r ∈ VG.Proof.Bignum.X86_64.pExpRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [VG.Impl.Bignum.X86_64.Public.sI, sFn] at *; omega
  · exact VG.Proof.Bignum.X86_64.pBitRanges_hdr w hk h1 h2 h3 r hr

theorem pBitRanges_sub (w : Nat) : ∀ r ∈ VG.Proof.Bignum.X86_64.pBitRanges w, r ∈ VG.Proof.Bignum.X86_64.pExpRanges w :=
  fun _ hr => List.mem_cons_of_mem _ hr

/-- `byteHead`'s loads: `e` and the byte index. -/
theorem pByteHead1_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hI : VG.Proof.Bignum.X86_64.PByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr VG.Impl.Bignum.X86_64.Public.sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ VG.Proof.Bignum.X86_64.PByteInv t₀ B Z w minv N X x ep L eb i t₁ := by
  have hc := hI.ctx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sE (by decide), hl VG.Impl.Bignum.X86_64.Public.sI (by decide), hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  exact ⟨hc.mem hm k (by decide), hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e, hm ▸ hI.len, hm ▸ hI.frm,
    (hI.keep.trans k).mono (by decide)⟩

/-- `byteHead`'s byte of `e` into `sV`, and the bit count 8: the start of the
bits. -/
theorem pByteHead2_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ VG.Proof.Bignum.X86_64.ofs B (ep + BitVec.ofNat 64 i))
    (hI : VG.Proof.Bignum.X86_64.PByteInv t₀ B Z w minv N X x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr VG.Impl.Bignum.X86_64.Public.sV) .rax,
      .mov32 .rax (.imm 8), .store (hdr VG.Impl.Bignum.X86_64.Public.sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV)) ((eb[i]'(by omega)).setWidth 64)).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit))
        (BitVec.setWidth 64 (8 : BitVec 32)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t₁ ∧
      VG.Proof.Bignum.X86_64.PBitInv t₁ B Z w minv N X x (VG.Proof.Bignum.X86_64.pre eb i) (eb[i]'(by omega)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hs : ∀ i < 32, InRegions t.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := VG.Proof.Bignum.X86_64.pExpRanges_le w r hr; have := hout i hi; omega)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sV))
      ((eb[i]'(by omega)).setWidth 64)).writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sBit)) (BitVec.setWidth 64 (8 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hax, hcx, VG.Proof.Bignum.X86_64.byteRead, hrdi, hbi, hs VG.Impl.Bignum.X86_64.Public.sV (by decide),
      hs VG.Impl.Bignum.X86_64.Public.sBit (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have hc₁ : VG.Proof.Bignum.X86_64.ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hc.good.rdi,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_word (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_word (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aXm) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine ⟨hc₁, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 2 ^ 8 from hv), Nat.add_zero]
    exact YSt.congr hI.y (by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sBit) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sV) _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sBit) (j := aY) _ _ _ (by decide) (by decide) hn',
        VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sV) (j := aY) _ _ _ (by decide) (by decide) hn'])
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sBit) (k := VG.Impl.Bignum.X86_64.Public.sV) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.word_writeW_self, VG.Proof.Bignum.X86_64.setWidth_byte]
  · rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl

/-- One byte of `e`: its eight bits, then the next byte. -/
theorem pByte_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} {i : Nat} (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ VG.Proof.Bignum.X86_64.ofs B (ep + BitVec.ofNat 64 i))
    (hI : VG.Proof.Bignum.X86_64.PByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.seq (.block byteHead) (.seq (.loop (Precomputed.expBit M.mm) .ne) (.block byteNext))) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ VG.Proof.Bignum.X86_64.PByteInv t₀ B Z w minv N X x ep L eb (i + 1) t' := by
  have hn := hI.ctx.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  rw [VG.Proof.Bignum.X86_64.byteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (VG.Proof.Bignum.X86_64.pByteHead1_ok hZ hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (VG.Proof.Bignum.X86_64.pByteHead2_ok hZ hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.pBits_ok hZ hw hw' hR hXN hXc hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₂ : ∀ i < 32, InRegions t₂.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hh₂ : ∀ k < 32, k ≠ VG.Impl.Bignum.X86_64.Public.sV → k ≠ VG.Impl.Bignum.X86_64.Public.sBit → k ≠ sStarted → VG.Proof.Bignum.X86_64.word t₂.mem B (8 * k) = VG.Proof.Bignum.X86_64.word tₐ.mem B (8 * k) :=
    fun k hk h1 h2 h3 => by
      rw [h₂.frm.word_eq (VG.Proof.Bignum.X86_64.pBitRanges_hdr w hk h1 h2 h3) (by omega), hm₁,
        VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sBit) _ _ _ (by decide) hk (Ne.symm h2),
        VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ VG.Impl.Bignum.X86_64.Public.sI (by decide) (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ sE (by decide) (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ sElen (by decide) (by decide) (by decide) (by decide)).trans hIₐ.len
  have hlen₂' : (t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sI)) (BitVec.ofNat 64 (i + 1))).readW (VG.Proof.Bignum.X86_64.off B (8 * sElen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    unfold byteNext
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hl₂ VG.Impl.Bignum.X86_64.Public.sI (by decide), hs₂ VG.Impl.Bignum.X86_64.Public.sI (by decide), hidx₂,
      ofNat_add_one, hl₂ sElen (by decide), hlen₂', ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega)
      (show L < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  refine ⟨ExpCtx.store hc₂ hZ (i := VG.Impl.Bignum.X86_64.Public.sI) (by decide) (by decide) hm' k'.2.2 ((k'.gpr (by decide)).trans
    hc₂.good.rdi), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hy := h₂.y
    rw [show VG.Proof.Bignum.X86_64.pre eb i * 2 ^ 8 + (eb[i]'(by omega)).toNat / 2 ^ (8 - 8) = VG.Proof.Bignum.X86_64.pre eb (i + 1) by
      rw [VG.Proof.Bignum.X86_64.pre_succ eb (by omega)]; omega] at hy
    exact YSt.congr hy (by rw [hm', VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm', VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sI) (j := aY) _ _ _ (by decide) (by decide) hn'])
  · rw [hm', VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm', VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm B (VG.Proof.Bignum.X86_64.pExpRanges w) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside tₐ.mem B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sV) (by unfold VG.Impl.Bignum.X86_64.Public.sV sFn; omega))
        (by simp [VG.Proof.Bignum.X86_64.pExpRanges, VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges])).trans
        (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sBit) (by unfold VG.Impl.Bignum.X86_64.Public.sBit sFn; omega))
          (by simp [VG.Proof.Bignum.X86_64.pExpRanges, VG.Proof.Bignum.X86_64.pBitRanges, VG.Proof.Bignum.X86_64.bitRanges]))
    have f₃ : Frm B (VG.Proof.Bignum.X86_64.pExpRanges w) t₂.mem t'.mem := by
      rw [hm']; exact Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sI) (by unfold VG.Impl.Bignum.X86_64.Public.sI sFn; omega))
        (by simp [VG.Proof.Bignum.X86_64.pExpRanges])
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (VG.Proof.Bignum.X86_64.pBitRanges_sub w))).trans f₃
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-- The loop's start: byte index 0, not started. -/
theorem pExpInit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z)
    (he : VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = ep) (hlen : VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (hdr VG.Impl.Bignum.X86_64.Public.sI) .rax, .store (hdr sStarted) .rax]) t
      (VG.Proof.Bignum.X86_64.PByteInv t B Z w minv N X x ep L eb 0) := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  have hst : ∀ i < 32, InRegions t.wr (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (8 * VG.Impl.Bignum.X86_64.Public.sI))
      (BitVec.setWidth 64 (0 : BitVec 32))).writeW (VG.Proof.Bignum.X86_64.off B (8 * sStarted)) (BitVec.setWidth 64 (0 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hst VG.Impl.Bignum.X86_64.Public.sI (by decide), hst sStarted (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have hc₁ : VG.Proof.Bignum.X86_64.ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hc.good.rdi,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := sStarted) (j := aN) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sI) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_word (i := sStarted) (j := aN) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_word (i := VG.Impl.Bignum.X86_64.Public.sI) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_wv (i := sStarted) (j := aXm) _ _ _ (by decide) (by decide) hn',
      VG.Proof.Bignum.X86_64.hdrStore_wv (i := VG.Impl.Bignum.X86_64.Public.sI) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  refine ⟨hc₁, .inl ⟨VG.Proof.Bignum.X86_64.pre_zero eb, by rw [hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl⟩, ?_, ?_, ?_, ?_, k₁.mono (by decide)⟩
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide), VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he
  · rw [hm₁, VG.Proof.Bignum.X86_64.hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.Bignum.X86_64.hdrStore_hdr (i := VG.Impl.Bignum.X86_64.Public.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen
  · rw [hm₁]
    exact (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * VG.Impl.Bignum.X86_64.Public.sI) (by unfold VG.Impl.Bignum.X86_64.Public.sI sFn; omega)) (by simp [VG.Proof.Bignum.X86_64.pExpRanges])).trans
      (Frm.of_outside (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (d := 8 * sStarted) (by unfold sStarted sFn; omega))
        (by simp [VG.Proof.Bignum.X86_64.pExpRanges, VG.Proof.Bignum.X86_64.pBitRanges]))

/-- The exponentiation: `YSt` for `e`, the `L` bytes `eb` at `ep`, outside the
working space. -/
theorem pExpLoop_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N)
    (hXc : X % N = x * 2 ^ (64 * w) % N)
    (he : VG.Proof.Bignum.X86_64.word t.mem B (8 * sE) = ep) (hlen : VG.Proof.Bignum.X86_64.word t.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ VG.Proof.Bignum.X86_64.ofs B (ep + BitVec.ofNat 64 i)) :
    WP isa (Precomputed.expLoop M.mm) t fun t' => VG.Proof.Bignum.X86_64.ExpCtx t' B Z w minv N X ∧
      VG.Proof.Bignum.X86_64.YSt t'.mem B w N x (Spec.Rsa.os2ip eb) ∧ Frm B (VG.Proof.Bignum.X86_64.pExpRanges w) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  unfold Precomputed.expLoop
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.pExpInit_ok (x := x) (eb := eb) hc hZ he hlen) fun t₁ h₁ => ?_)
  refine wp_upto (a := 0) (N := L) (by omega) (VG.Proof.Bignum.X86_64.PByteInv t B Z w minv N X x ep L eb)
    (fun i _ hi s hI => VG.Proof.Bignum.X86_64.pByte_ok hZ hw hw' hR hXN hXc hL hL' hi hrd hbytes hout hI)
    (fun s hI => ?_) h₁
  exact ⟨hI.ctx, by rw [← VG.Proof.Bignum.X86_64.pre_len, hL]; exact hI.y, hI.frm, hI.keep⟩

/-! ## The result -/

/-- What `finish` changes. -/
def finRanges (w : Nat) : List (Nat × Nat) :=
  [(VG.Proof.Bignum.X86_64.slot w aAcc, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aTmp, 8 * (w + 2)), (VG.Proof.Bignum.X86_64.slot w aY, 8 * (w + 2))]

/-- `finish`: `Y R⁻¹`, which is `x^E mod N`, or 1 if `E = 0`. -/
theorem pFinish_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E : Nat}
    (hc : VG.Proof.Bignum.X86_64.ExpCtx t B Z w minv N X) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN1 : 1 < N) (hone : wv t.mem B (VG.Proof.Bignum.X86_64.slot w aOne) w = 1)
    (hy : VG.Proof.Bignum.X86_64.YSt t.mem B w N x E) :
    WP isa (VG.Impl.Rsa.X86_64.Precomputed.finish M.mm) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (VG.Proof.Bignum.X86_64.slot w aY) w = x ^ E % N ∧
      Frm B (VG.Proof.Bignum.X86_64.finRanges w) t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + VG.Proof.Bignum.X86_64.slot w 8 ≤ 2 ^ 64 := by omega
  unfold VG.Impl.Rsa.X86_64.Precomputed.finish
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.startedTest_ok hc.good hZ hy) fun t₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have hc₁ := hc.mem hm₁ k₁ (by decide)
  rcases hy with ⟨h0, -⟩ | ⟨h0, -, Y, hY, hYN, hYc⟩
  · refine WP.ite false (by simp [VG.X86_64.eval, hz₁, h0]) (by simp) (fun _ => ?_)
    have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
      hc₁.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
    refine WP.seq (WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 w ∧
        t₂.gpr .rdx = 1 ∧ t₂.gpr .rcx = BitVec.ofNat 64 0 ∧ t₂.mem = t₁.mem) (by
      xrun [State.ea, hdr, hc₁.good.rdi, hdrOff, hl sW (by decide), hc₁.good.hdr.hw]) rfl)
      fun t₂ ⟨⟨h12, hdx, hcx, hm₂⟩, k₂⟩ => ?_)
    have hc₂ := hc₁.mem hm₂ k₂ (by decide)
    refine WP.mono (VG.Proof.Bignum.X86_64.setWord_ok hc₂.good.scr hc₂.good.rdi hc₂.good.hdr hZ h12 (by omega) hw' (o := aY) (by decide)
      (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t' ⟨hv, ho, k₃⟩ => ?_
    have ha : Arrays B w [aY] t₂.mem t'.mem := Arrays.of_outside (j := aY) (by simp) ho (Nat.le_refl _) (Nat.le_refl _)
    refine ⟨⟨hc₂.good.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hc₂.good.rdi, ha.hdr hc₂.good.hdr⟩, ?_, ?_,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [hv, hdx, h0]
      simp only [Nat.pow_zero, Nat.mul_zero, Nat.mod_eq_of_lt hN1]; rfl
    · rw [hm₂, hm₁] at ha
      exact Frm.of_arrays ha (by simp [VG.Proof.Bignum.X86_64.finRanges])
  · refine WP.ite true (by simp [VG.X86_64.eval, hz₁, h0]) (fun _ => ?_) (by simp)
    refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aOne) hc₁.good hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
      (by rw [hc₁.n, hm₁, hone]; exact hN1)) fun t' ⟨hg', hlt, hmm, ha, k₂⟩ => ?_
    rw [hc₁.n] at hlt
    rw [hc₁.n, hm₁, hY, hone, Nat.mul_one] at hmm
    refine ⟨hg', ?_, by rw [hm₁] at ha; exact Frm.of_arrays ha (by simp [VG.Proof.Bignum.X86_64.finRanges]), (k₁.trans k₂).mono (by decide)⟩
    rw [← Nat.mod_eq_of_lt hlt]
    exact VG.Proof.Bignum.mont_cancel hR (by rw [hmm, hYc])

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Valid`. -/
section

/-!
# Multiword arithmetic on x86-64: `vg_rsa_public`'s check of the modulus

`invalid` sets ZF iff the `k` bytes of `m` make a valid modulus
(`Spec.Rsa.modulusValid`), for `64 ≤ k ≤ 1024` (`invalid_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem os2ip_foldl (a : Nat) (bs : List Byte) :
    bs.foldl (fun x b => 256 * x + b.toNat) a = a * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
  induction bs generalizing a with
  | nil => simp [Spec.Rsa.os2ip]
  | cons b bs ih =>
    show bs.foldl _ (256 * a + b.toNat) = a * 256 ^ (bs.length + 1) + bs.foldl _ (256 * 0 + b.toNat)
    rw [ih, ih (256 * 0 + b.toNat), Nat.pow_succ, Nat.add_mul, Nat.mul_zero, Nat.zero_add, Nat.mul_assoc,
      Nat.mul_comm (256 ^ bs.length) 256, Nat.add_assoc, Nat.mul_left_comm]

theorem os2ip_cons (b : Byte) (bs : List Byte) :
    Spec.Rsa.os2ip (b :: bs) = b.toNat * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
  show List.foldl (fun x (b : Byte) => 256 * x + b.toNat) (256 * 0 + b.toNat) bs = _
  rw [VG.Proof.Bignum.X86_64.os2ip_foldl, Nat.mul_zero, Nat.zero_add]

theorem os2ip_lt (bs : List Byte) : Spec.Rsa.os2ip bs < 256 ^ bs.length := by
  rw [← VG.Proof.Bignum.X86_64.pre_len]; exact VG.Proof.Bignum.X86_64.pre_lt bs (Nat.le_refl _)

theorem pow256_eq (a : Nat) : (256 : Nat) ^ a = 2 ^ (8 * a) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

theorem pow256_64 : (256 : Nat) ^ 64 = 2 ^ 512 := (VG.Proof.Bignum.X86_64.pow256_eq 64).trans (congrArg (2 ^ ·) rfl)

theorem modulusValid_nat {n0 r l P k : Nat} (hn0 : n0 < 256) (hr : r < P) (hP : P = 256 ^ (k - 1))
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hodd : (n0 * P + r) % 2 = l % 2) :
    Spec.Rsa.modulusValid (n0 * P + r) k =
      !(decide (n0 < 1) || decide (l % 2 < 1) || decide ((k - 64) * 256 + n0 < 128)) := by
  unfold Spec.Rsa.modulusValid
  by_cases h0 : n0 = 0
  · subst h0
    simp only [Nat.zero_mul, Nat.zero_add, ← hP, show ¬ P ≤ r by omega, decide_false, Bool.and_false,
      show (0 < 1) = True from propext ⟨fun _ => trivial, fun _ => by decide⟩, decide_true, Bool.true_or,
      Bool.not_true]
  have hge : P ≤ n0 * P + r := Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by omega))
  have hlt : n0 * P + r < 2 ^ 8192 := by
    have h1 : n0 * P + r < 256 * P := by
      have := Nat.mul_le_mul_right P (show n0 + 1 ≤ 256 by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h2 : 256 * P = 2 ^ (8 * k) := by
      rw [hP, ← VG.Proof.Bignum.X86_64.pow256_eq, ← Nat.pow_succ']; congr 1; omega
    have h3 := (fun B (hB : 8 * k ≤ B) => Nat.pow_le_pow_right (n := 2) (by decide) hB) 8192 (by omega)
    omega
  have h511 : decide (2 ^ 511 ≤ n0 * P + r) = !decide ((k - 64) * 256 + n0 < 128) := by
    by_cases hk64 : k = 64
    · subst hk64
      have hP' : P = 2 ^ 504 := hP.trans ((VG.Proof.Bignum.X86_64.pow256_eq _).trans (congrArg (2 ^ ·) rfl))
      rw [hP'] at hr ⊢
      rw [show (64 - 64) * 256 + n0 = n0 by omega]
      by_cases h128 : 128 ≤ n0
      · simp only [show 2 ^ 511 ≤ n0 * 2 ^ 504 + r by omega, show ¬ n0 < 128 by omega, decide_true,
          decide_false, Bool.not_false]
      · simp only [show ¬ 2 ^ 511 ≤ n0 * 2 ^ 504 + r by omega, show n0 < 128 by omega, decide_true,
          decide_false, Bool.not_true]
    · have hP' : 2 ^ 512 ≤ P := by
        rw [hP, ← VG.Proof.Bignum.X86_64.pow256_64]; exact Nat.pow_le_pow_right (by decide) (by omega)
      simp only [show 2 ^ 511 ≤ n0 * P + r by omega, show ¬ (k - 64) * 256 + n0 < 128 by omega, decide_true,
        decide_false, Bool.not_false]
  rw [← hP]
  simp only [h511, show P ≤ n0 * P + r from hge, show n0 * P + r < 2 ^ 8192 from hlt, show ¬ n0 < 1 by omega,
    decide_true, decide_false, Bool.and_true, Bool.false_or, Bool.not_or]
  by_cases hl : l % 2 = 1
  · simp [hl, hodd]
  · simp [show l % 2 = 0 by omega, hodd]

/-- `m` is a valid modulus iff its first byte is not zero, its last byte is
odd, and `256 (k - 64) + m[0] ≥ 128`, for `64 ≤ k ≤ 1024`. -/
theorem modulusValid_iff {nb : List Byte} {k : Nat} (hlen : nb.length = k) (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k =
      !(decide ((nb[0]'(by omega)).toNat < 1) || decide ((nb[k - 1]'(by omega)).toNat % 2 < 1) ||
        decide ((k - 64) * 256 + (nb[0]'(by omega)).toNat < 128)) := by
  have hodd : Spec.Rsa.os2ip nb % 2 = (nb[k - 1]'(by omega)).toNat % 2 := by
    have := VG.Proof.Bignum.X86_64.pre_succ nb (i := k - 1) (by omega)
    rw [show k - 1 + 1 = nb.length by omega, VG.Proof.Bignum.X86_64.pre_len] at this
    omega
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, nb = b :: bs := by
    cases nb with
    | nil => simp at hlen; omega
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hl : bs.length = k - 1 := by simp at hlen; omega
  rw [VG.Proof.Bignum.X86_64.os2ip_cons, hl] at hodd ⊢
  have hr := VG.Proof.Bignum.X86_64.os2ip_lt bs
  rw [hl] at hr
  exact VG.Proof.Bignum.X86_64.modulusValid_nat b.isLt hr rfl hk hk' hodd

theorem ofInt_m1 : BitVec.ofInt 64 (-1) = -(1#64) := by decide

/-- The masks of borrows, or'ed. -/
theorem mask_or' (a b : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool a)) |||
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool b)) = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (a || b)) := by
  cases a <;> cases b <;> decide

theorem mask_beq (a : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool a) == 0) = !a := by
  cases a <;> decide

theorem sw_toNat (b : Byte) : (BitVec.setWidth 64 b).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem sw_and1 (b : Byte) : (BitVec.setWidth 64 b &&& 1).toNat = b.toNat % 2 := by
  rw [BitVec.toNat_and, VG.Proof.Bignum.X86_64.sw_toNat, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = 64#64 := by decide
theorem sx128 : (BitVec.signExtend 64 (128 : BitVec 32)).toNat = 128 := by decide

theorem ror_k {k : Nat} (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    ((BitVec.ofNat 64 k - 64#64).rotateRight 56).toNat = (k - 64) * 256 := by
  have e : BitVec.ofNat 64 k - 64#64 = BitVec.ofNat 64 (k - 64) := by
    rw [show (64#64) = BitVec.ofNat 64 64 from rfl, show k = (k - 64) + 64 by omega, ← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel, Nat.add_sub_cancel]
  rw [e, VG.Proof.Bignum.X86_64.ror56_toNat _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

theorem invalid_ok {s : State} {np : Addr} {k : Nat} {nb : List Byte}
    (hdx : s.gpr .rdx = np) (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 i) 1)
    (hb : ∀ i (h : i < k), s.mem (np + BitVec.ofNat 64 i) = nb[i]'(by omega)) :
    WP isa (.block invalid) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .rsi] s t := by
  refine WP.mono (WP.keep [.rax, .rbp, .rsi] (Q := fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hr0 : InRegions (s.rd ++ s.wr) np 1 := by have := hrd 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have hb0 : s.mem np = nb[0]'(by omega) := by have := hb 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have hlast : np + BitVec.ofNat 64 k * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = np + BitVec.ofNat 64 (k - 1) := by
    have e : BitVec.ofNat 64 k = BitVec.ofNat 64 (k - 1) + 1#64 := by
      rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]; congr 1; omega
    rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, e, VG.Proof.Bignum.X86_64.ofInt_m1, ← BitVec.sub_eq_add_neg,
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  unfold invalid
  xrun [State.ea, at0, hdx, hcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hr0, hb0, hlast,
    hrd (k - 1) (by omega), hb (k - 1) (by omega)]
  have hn0 := (nb[0]'(by omega)).isLt
  rw [VG.Proof.Bignum.X86_64.mask_or', VG.Proof.Bignum.X86_64.mask_or', BitVec.and_self, VG.Proof.Bignum.X86_64.mask_beq, VG.Proof.Bignum.X86_64.modulusValid_iff hlen hk hk', VG.Proof.Bignum.X86_64.sw_toNat, VG.Proof.Bignum.X86_64.sw_and1,
    show BitVec.toNat (1 : BitVec 64) = 1 from rfl, VG.Proof.Bignum.X86_64.sx64, VG.Proof.Bignum.X86_64.sx128, BitVec.toNat_add, VG.Proof.Bignum.X86_64.ror_k hk hk', VG.Proof.Bignum.X86_64.sw_toNat, Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]

end VG.Proof.Bignum.X86_64

end
