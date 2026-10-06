import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Crt

/-!
# An RSA key from its primes on x86-64: `n` and the final mask

`n = p q` (`nPart_k`), and `kOk &= ` the masks of `n`'s top bit, `p` and
`q` odd, and `e` valid (`finalMask_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `nPart`: `[aQt] := [aPa] [aQa]`, `w` words each, for `W = 2 w`. -/
theorem nPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPa = a) (hb : av I s.mem aQa = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs nPart) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aQt] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aQt) (I.W + 2) = a * b := by
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl (j := aPa) (by decide)
  have sQ := h.ws.sl (j := aQa) (by decide)
  have sL := h.ws.sl (j := aQt) (by decide)
  have p1 := slot_far (w := I.W) (i := aPa) (j := aQt) (by decide)
  have p2 := slot_far (w := I.W) (i := aQa) (j := aQt) (by decide)
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  simp only [nPart, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aQt) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  have hok : [Rc.arr aQt].all Rc.ok = true := by decide
  have va : wv s₁.mem I.B (slot I.W aPa) w = a := by
    rw [f₁.wv hok (j := aPa) (by decide) (by decide) (Nat.le_refl _) (by omega) h.hZ, ← ha]
    dsimp only [av] at ha
    exact wv_low_of_lt (by omega) (by rw [ha]; exact ha')
  have vb : wv s₁.mem I.B (slot I.W aQa) w = b := by
    rw [f₁.wv hok (j := aQa) (by decide) (by decide) (Nat.le_refl _) (by omega) h.hZ, ← hb]
    dsimp only [av] at hb
    exact wv_low_of_lt (by omega) (by rw [hb]; exact hb')
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  have hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h₁.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok aPa (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQa (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQt (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  have h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  have hax₅ : s₅.gpr .rax = off I.B (slot I.W aQa) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQa) ∧
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega)]
    refine ⟨by rw [hW]; congr 1; omega, ?_⟩
    rw [ofNat_sub' (by omega) (by omega)]; congr 1; omega) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  have k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  have hm₆ : s₆.mem = s₁.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  have hz₆ : wv s₆.mem I.B (slot I.W aQt) (w + w + 2) = 0 := by rw [hm₆, ← z₁]; congr 1; omega
  refine WP.mono (mulRows_ok (h₁.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₇⟩ => ?_
  rw [hz₆, hm₆, va, vb, Nat.zero_add] at hv
  rw [hm₆] at o
  have f := KF.arr1 (I := I) (j := aQt) o (Nat.le_refl _) (by omega)
  refine ⟨h₁.step f (all_mut_arr (by decide)) (k26.trans k₇) (by decide), (f₁.trans f).mono (by simp), ?_⟩
  rw [show I.W + 2 = w + w + 2 by omega]; exact hv


/-! ## The final mask -/

/-- The top bit of a `W`-word number: of its word `W − 1`. -/
theorem top_bit {m : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) :
    (word m B (d + 8 * (W - 1))).toNat / 2 ^ 63 = if 2 ^ (64 * W - 1) ≤ wv m B d W then 1 else 0 := by
  have e : wv m B d W = wv m B d (W - 1) + 2 ^ (64 * (W - 1)) * (word m B (d + 8 * (W - 1))).toNat := by
    rw [show W = W - 1 + 1 from by omega, wv]; simp
  have ha := wv_lt m B d (W - 1)
  have ht := (word m B (d + 8 * (W - 1))).isLt
  generalize wv m B d (W - 1) = a at e ha
  generalize (word m B (d + 8 * (W - 1))).toNat = t at e ht
  have hp : 2 ^ (64 * W - 1) = 2 ^ (64 * (W - 1)) * 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega
  generalize 2 ^ (64 * (W - 1)) = R at e ha hp
  rw [e, hp]
  by_cases h63 : 2 ^ 63 ≤ t
  · have : R * 2 ^ 63 ≤ R * t := Nat.mul_le_mul_left _ h63
    rw [ite_eq_left (show R * 2 ^ 63 ≤ a + R * t by omega)]; omega
  · have : R * t + R ≤ R * 2 ^ 63 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    rw [ite_eq_right (show ¬ R * 2 ^ 63 ≤ a + R * t by omega)]; omega


theorem shr63_mask (x : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = mask (decide (x.toNat / 2 ^ 63 = 1)) := by
  have h : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := x.isLt; omega
  rw [h]
  have := x.isLt
  rcases (show x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1 by omega) with e | e <;> rw [e] <;> decide

/-- `[rbx + 8 r12 − 8]`: word `W − 1` of the array at `rbx`. -/
theorem addr_last {b : Addr} {B : Addr} {e W : Nat} (hb : b = off B e) (hW : 1 ≤ W) :
    b + BitVec.ofNat 64 W * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = off B (e + 8 * (W - 1)) := by
  subst hb
  have h8 : BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide
  rw [ofNat_mul8, h8, off, off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  refine congrArg (B + ·) ?_
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega


/-- The mask `finalMask` leaves in `kOk`. -/
abbrev finalOk (W n P Q e : Nat) (ok : Bool) : Bool :=
  decide (2 ^ (64 * W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e

/-- `finalMask`, for `[aQt] = n`, `[aPa] = P`, `[aQa] = Q` and `kOk` the
mask of `ok`. -/
theorem finalMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {n P Q e : Nat} {ok : Bool}
    (hn : av I s.mem aQt = n) (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (.block finalMask) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (finalOk I.W n P Q e ok) := by
  have hnw := h.ws.scr.nowrap
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega
  have sN := h.ws.sl (j := aQt) (by decide)
  have hld := fun (i : Nat) (hi : i < 32) => h.ws.scr.ld (d := 8 * i) (by have := h.ws.h256; omega)
  unfold finalMask
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aQt (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
  have hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  have h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  have hmu₂ : u₂.mem = s.mem := by rw [mu₂, mu₁]
  have htop : (word s.mem I.B (slot I.W aQt + 8 * (I.W - 1))).toNat / 2 ^ 63 = 1 ↔ 2 ^ (64 * I.W - 1) ≤ n := by
    rw [top_bit hw1, show wv s.mem I.B (slot I.W aQt) I.W = n from hn]; split <;> simp_all
  -- `rcx := ` the masks of the top bit and `ok`.
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) ∧
    t.mem = s.mem) (by
      have hok₂ : word u₂.mem I.B (8 * kOk) = mask ok := by rw [hmu₂, hok]
      xrun [State.ea, ix, hdr, hdrOff, h12₂, addr_last hbx hw1, hs₂.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega),
        ((ku₁.trans ku₂).gpr (by decide)).trans h.ws.rdi, hs₂.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega),
        shr63_mask, hok₂, mask_and', hmu₂]
      have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
      have ht' : decide ((s.mem.readW (off I.B (slot I.W aQt + 8 * (I.W - 1))) 64).toNat / 2 ^ 63 = 1) =
          decide (2 ^ (64 * I.W - 1) ≤ n) := decide_eq_decide.mpr htop
      rw [hok', mask_and', ht']) rfl) fun u₃ ⟨⟨hcx₃, mu₃⟩, ku₃⟩ => WP.block_append_iff.mpr ?_
  have k13 := (ku₁.trans ku₂).trans ku₃
  have h₃ := h.step (cs := []) (by rw [mu₃]; exact KF.refl _ _ _) rfl k13 (by decide)
  -- `p` odd.
  refine WP.mono (oddMask_k h₃ (j := aPa) (by decide)) fun u₄ ⟨mu₄, hax₄, _, _, ku₄⟩ => WP.block_append_iff.mpr ?_
  rw [mu₃, hP] at hax₄
  have hcx₄ : u₄.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) := by rw [ku₄.gpr (by decide), hcx₃]
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok &&
    decide (P % 2 = 1)) ∧ t.mem = u₄.mem) (by xrun [hax₄, hcx₄, mask_and']) rfl)
    fun u₅ ⟨⟨hcx₅, mu₅⟩, ku₅⟩ => WP.block_append_iff.mpr ?_
  have h₅ := h₃.step (cs := []) (by rw [mu₅, mu₄]; exact KF.refl _ _ _) rfl (ku₄.trans ku₅) (by decide)
  -- `q` odd.
  refine WP.mono (oddMask_k h₅ (j := aQa) (by decide)) fun u₆ ⟨mu₆, hax₆, _, _, ku₆⟩ => ?_
  rw [mu₅, mu₄, mu₃, hQ] at hax₆
  have hcx₆ : u₆.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1)) := by
    rw [ku₆.gpr (by decide), hcx₅]
  have hm₆ : u₆.mem = s.mem := by rw [mu₆, mu₅, mu₄, mu₃]
  have hs₆ := h₅.ws.scr.congr ku₆.2.2
  have hdi₆ : u₆.gpr .rdi = I.B := ((ku₄.trans ku₅).trans ku₆).gpr (by decide) |>.trans h₃.ws.rdi
  have hev₆ : u₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₆]; exact hev
  -- `e` valid, and the store.
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk))
    (mask (finalOk I.W n P Q e ok))) (by
      xrun [State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega),
        hs₆.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega), hev₆, hax₆, hcx₆, mask_and', mask_low,
        sxM1, maskNot, hm₆]
      have hev' : s.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev
      have hT : ((BitVec.ofNat 64 e) >>> 33).toNat = e / 2 ^ 33 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      have hsub : ∀ c : Bool, 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = mask c := fun _ => rfl
      rw [hev', BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hT, hsub, hsub, maskNot, mask_and', mask_and',
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
      have e1 : (decide (e % 2 = 1) && !decide (e < 3) && decide (e / 2 ^ 33 < 1)) = Spec.Rsa.exponentValid e := by
        unfold Spec.Rsa.exponentValid
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
        omega
      refine congrArg (fun v => s.mem.writeW (off I.B (8 * kOk)) (mask v)) ?_
      simp only [finalOk]
      rw [← e1]
      simp only [Bool.and_assoc]) rfl) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, ft, okt⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega) mt
    ((((k13.trans ku₄).trans ku₅).trans ku₆).trans kt) (by decide)
  exact ⟨ht, ft, okt⟩

end VG.Proof.RsaKeyGen.X86_64.Key
