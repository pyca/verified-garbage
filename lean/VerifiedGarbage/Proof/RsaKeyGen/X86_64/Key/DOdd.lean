import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Minv

/-! ## DBase -/
section

/-!
# An RSA key from its primes on x86-64: the pieces of `d`

`[aE] := e` (`loadEv_k`), the masks of `L ≥ 2` (`lGe2_k`) and of a gcd of 1
(`gcdIsOne_k`) into `kOk`, and the inverse's start (`invFrom_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem two_le_pow {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {x : Nat} (hx : x < 2 ^ 64) :
    x < 2 ^ (64 * I.W) :=
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by have := h.ws.w1; omega))

/-- `loadEv`: `[aE] := e` over `W + 2` words. -/
theorem loadEv_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e : Nat} (he : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) :
    WP isa (seqs loadEv) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aE) (I.W + 2) = e := by
  have hn := h.ws.scr.nowrap
  have sE := h.ws.sl (j := aE) (by decide)
  simp only [loadEv, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aE) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  have hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [f₁.word (by decide) (by decide) (by decide), hev]
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h₁.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aE (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h₁.ws.scr.congr (k₂.trans k₃).2.2
  have hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans h₁.ws.rdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aE)) (BitVec.ofNat 64 e)) (by
    xrun [State.ea, at0, hdr, hbx, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega), hs₃.st (d := slot I.W aE) (by omega),
      m₃, m₂, hev₁]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s₁.mem I.B (BitVec.ofNat 64 e) (d := slot I.W aE) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (I := I) (j := aE) o₄ (Nat.le_refl _) (by omega)
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) ((k₂.trans k₃).trans k₄) (by decide), (f₁.trans f₄).mono (by simp), ?_⟩
  rw [hm]
  have := wv_put (m := s₁.mem) (B := I.B) (d := slot I.W aE) (N := I.W + 2) (k := 0) (BitVec.ofNat 64 e)
    ((wv_eq_zero_iff _ _ _ _).mp z₁) (by omega) (by omega) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < I.W + 2 by omega), Nat.pow_zero, Nat.one_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he]

/-- `lGe2`: `kOk := ` the mask of `L ≥ 2`. -/
theorem lGe2_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (seqs lGe2) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (!decide (av I s.mem aL < 2)) := by
  have hZ := h.hZ
  unfold lGe2
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h 2) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c2 : av I s₁.mem aC = 2 := av_of_full c₁ (two_le_pow h (by decide))
  have vL : av I s₁.mem aL = av I s.mem aL := f₁.av (by decide) (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₁ (a := aL) (b := aC) (by decide) (by decide))
    fun s₂ ⟨h₂, m₂, hbp, _, _, _, k₂⟩ => ?_)
  rw [vL, c2] at hbp
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (av I s.mem aL < 2)))) (by xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃ (by decide)
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by simp), hw⟩

/-- `gcdIsOne`: `kOk &= ` the mask of `[aV] = 1`. -/
theorem gcdIsOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (seqs gcdIsOne) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (av I s.mem aV = 1) && c) := by
  have hZ := h.hZ
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  have c1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
  have vV : av I s₁.mem aV = av I s.mem aV := f₁.av (by decide) (by decide) (by decide) hZ
  have hok₁ : word s₁.mem I.B (8 * kOk) = mask c := by rw [f₁.word (by decide) (by decide) (by decide), hok]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₁ (a := aV) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, hbp, k₂⟩ => ?_)
  rw [vV, c1] at hbp
  simp only [seqs]
  have hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hld := h₂.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega)
  have hok₂ : word s₂.mem I.B (8 * kOk) = mask c := by rw [m₂, hok₁]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (decide (av I s.mem aV = 1) && c))) (by
      xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hld, hbp, hok₂, mask_and']) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega) hm k₃ (by decide)
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by simp), hw⟩

/-- `invFrom j`: `v := [j]`, `x₁ := 1`, `x₂ := 0`. -/
theorem invFrom_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjV : j ≠ aV) :
    WP isa (seqs (invFrom j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aV, .arr aX₁, .arr aX₂] s.mem t.mem ∧
      av I t.mem aV = av I s.mem j ∧ av I t.mem aX₁ = 1 ∧ av I t.mem aX₂ = 0 := by
  have hZ := h.hZ
  have hw1 := h.ws.w1
  simp only [invFrom, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aV) (by decide)) fun s₁ ⟨h₁, f₁, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₁ (o := aV) (a := j) (by decide) hj hjV.symm) fun s₂ ⟨h₂, f₂, v₂, _, _⟩ =>
      WP.seq (WP.mono (zeroA_k h₂ (j := aX₁) (by decide)) fun s₃ ⟨h₃, f₃, z₃, _⟩ =>
        WP.seq (WP.mono (setOne_k h₃ (j := aX₁) (by decide) z₃) fun s₄ ⟨h₄, f₄, o₄, _⟩ =>
          WP.mono (zeroA_k h₄ (j := aX₂) (by decide)) fun t ⟨ht, f₅, z₅, _⟩ => ?_))))
  refine ⟨ht, ((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).mono (by simp), ?_, ?_, (wv_zero2 z₅).1⟩
  · rw [f₅.av (by decide) (by decide) (by decide) hZ, f₄.av (by decide) (by decide) (by decide) hZ,
      f₃.av (by decide) (by decide) (by decide) hZ, v₂, f₁.av (by decide) hj (by simp [hjV]) hZ]
  · rw [f₅.av (by decide) (by decide) (by decide) hZ]
    exact av_of_full o₄ (two_le_pow h (by decide))

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## DOdd -/
section

/-!
# An RSA key from its primes on x86-64: `d` for an odd `e`

`L = e Q + R`, `x = R⁻¹ mod e`, `t = e − x` and `d = Q t + c` with
`c = (1 + R t) e⁻¹ mod 2⁶⁴` (`dOdd_k`, `inverse_odd`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- What `dPart` leaves: `kOk` the mask of `e⁻¹ mod L` existing, and that
inverse in `aDd`. -/
def DRes (I : KIn) (e L : Nat) (m : Mem) : Prop :=
  ∃ ok : Bool, word m I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse e L = some d) ↔ ok = true) ∧
    ∀ d, Spec.Rsa.inverse e L = some d → av I m aDd = d

/-- The parts `dPart` changes. -/
abbrev csD : List Rc :=
  [.arr aE, .arr aQt, .arr aR, .arr aT, .arr aU, .arr aV, .arr aX₁, .arr aX₂, .arr aC, .arr aM, .arr aDd, .hdr sMo,
    .hdr kOk]

theorem dOdd_eq : dOdd = loadEv ++ ([zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] ++
    (invFrom aE ++ ([inverse aU aV aX₁ aX₂ aE aT] ++ (lGe2 ++ (gcdIsOne ++
    ([.block (([.mov .rbx (.mem (hdr kEv))] : List Instr) ++ minv),
      .block (ws ++ base aX₂ .rbx ++ base aR .r10 ++
        ([.mov .rsi (.mem (hdr kEv)), .alu .sub .rsi (.mem (at0 .rbx)), .mov .rax (.mem (at0 .r10)), .mul .rsi,
          .alu .add .rax (.imm 1), .mul .rcx, .mov .r15 (.reg .rax), .store (hdr sMo) .rsi] : List Instr)),
      zeroA aDd,
      .block (ws ++ base aDd .r8 ++ ([.store (at0 .r8) .r15] : List Instr) ++ base aQt .rax ++
        ([.mov .r9 (.reg .rax), .mov .rcx (.mem (hdr sMo))] : List Instr)),
      mulAddRow] : List (Prog isa))))))) := by
  simp only [dOdd, List.append_assoc]

/-- A number below `2⁶⁴` is its low word. -/
theorem word0_of_lt {I : KIn} {m : Mem} {j v : Nat} (hw : 1 ≤ I.W) (h : av I m j = v) (hv : v < 2 ^ 64) :
    (word m I.B (slot I.W j)).toNat = v := by
  rw [← wv_mod64 _ _ _ hw, show wv m I.B (slot I.W j) I.W = av I m j from rfl, h, Nat.mod_eq_of_lt hv]

/-- `dOdd`, for an odd `e ≥ 3`. -/
theorem dOdd_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e L : Nat} (he3 : 3 ≤ e) (he64 : e < 2 ^ 64)
    (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dOdd) s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  have hw2 := h.ws.w2
  rw [dOdd_eq]
  -- `[aE] := e`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  have vE₁ : av I s₁.mem aE = e := av_of_full e₁ (two_le_pow h he64)
  have vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  -- `L = e Q + R`.
  refine wp_seqs_append (by simp) (by simp [invFrom]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aQt) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aQt) (a := aL) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aQt) (iR := aR) (iD := aE) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aU) (by decide)) fun s₅ ⟨h₅, f₅, z₅, _⟩ =>
          WP.mono (copyA_k h₅ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, t₆, _⟩ => ?_))))
  have vE₃ : av I s₃.mem aE = e := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vE₁]
  have vQ₃ : av I s₃.mem aQt = L := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  rw [vE₃, vQ₃] at d₄
  obtain ⟨dR, dQ⟩ := d₄ (by omega_using [heo])
  have hR : L % e < e := Nat.mod_lt _ (by omega_using [heo])
  have vR₄ : av I s₄.mem aR = L % e := by
    rw [← dR]; exact wv_low_of_lt (by omega_using []) (by rw [dR]; exact Nat.lt_trans hR (two_le_pow h he64))
  have hok4 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  have vU₆ : av I s₆.mem aU = L % e := by rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  have tU₆ : atop I s₆.mem aU = 0 := by rw [t₆]; exact (wv_zero2 z₅).2
  have pres6 : ∀ j, j < 16 → j ≠ aQt → j ≠ aR → j ≠ aT → j ≠ aU → av I s₆.mem j = av I s₃.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ]
  have vE₆ : av I s₆.mem aE = e := by rw [pres6 aE (by decide) (by decide) (by decide) (by decide) (by decide), vE₃]
  have vQ₆ : av I s₆.mem aQt = L / e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, dQ]
  have vR₆ : av I s₆.mem aR = L % e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  have vL₆ : av I s₆.mem aL = L := by
    rw [pres6 aL (by decide) (by decide) (by decide) (by decide) (by decide), f₃.av (by decide) (by decide)
      (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  -- `x = R⁻¹ mod e`.
  refine wp_seqs_append (by simp [invFrom]) (by simp) (WP.mono (invFrom_k h₆ (j := aE) (by decide) (by decide))
    fun s₇ ⟨h₇, f₇, vV₇, vX₁₇, vX₂₇⟩ => ?_)
  have hok7 : [Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂].all Rc.ok = true := by decide
  have vU₇ : av I s₇.mem aU = L % e := by rw [f₇.av hok7 (by decide) (by decide) hZ, vU₆]
  have tU₇ : atop I s₇.mem aU = 0 := by rw [f₇.at hok7 (by decide) (by decide) hZ, tU₆]
  have vE₇ : av I s₇.mem aE = e := by rw [f₇.av hok7 (by decide) (by decide) hZ, vE₆]
  refine wp_seqs_append (by simp) (by simp [lGe2]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₇ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aE) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) tU₇ (by rw [vV₇, vE₆, vE₇]) vX₁₇ vX₂₇) fun s₈ ⟨h₈, f₈, hinv⟩ => ?_
  rw [vE₇, vU₇] at hinv
  obtain ⟨hg₈, hdv₈, hx₈⟩ := hinv heo (by omega_using [he3])
  generalize hx : av I s₈.mem aX₂ = x at hdv₈ hx₈
  have hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.hdr sMo].all Rc.ok = true := by decide
  have vL₈ : av I s₈.mem aL = L := by
    rw [f₈.av hokI (by decide) (by decide) hZ, f₇.av hok7 (by decide) (by decide) hZ, vL₆]
  -- `kOk := ` the masks of `L ≥ 2` and `gcd(R, e) = 1`.
  refine wp_seqs_append (by simp [lGe2, constA]) (by simp [gcdIsOne, constA]) (WP.mono (lGe2_k h₈)
    fun s₉ ⟨h₉, f₉, ok₉⟩ => ?_)
  rw [vL₈] at ok₉
  have vV₉ : av I s₉.mem aV = Nat.gcd (L % e) e := by rw [f₉.av (by decide) (by decide) (by decide) hZ, hg₈]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₉ ok₉)
    fun s₁₀ ⟨h₁₀, f₁₀, ok₁₀⟩ => ?_)
  rw [vV₉] at ok₁₀
  have hokC : [Rc.arr aC, Rc.hdr kOk].all Rc.ok = true := by decide
  have pres10 : ∀ j, j < 16 → j ≠ aC → av I s₁₀.mem j = av I s₈.mem j := fun j hj h1 => by
    rw [f₁₀.av hokC hj (by simp [h1]) hZ, f₉.av hokC hj (by simp [h1]) hZ]
  have hxe : x < e := hx₈
  have vX₁₀ : av I s₁₀.mem aX₂ = x := by rw [pres10 aX₂ (by decide) (by decide), hx]
  have vR₁₀ : av I s₁₀.mem aR = L % e := by
    rw [pres10 aR (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ,
      f₇.av hok7 (by decide) (by decide) hZ, vR₆]
  have vQ₁₀ : av I s₁₀.mem aQt = L / e := by
    rw [pres10 aQt (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ,
      f₇.av hok7 (by decide) (by decide) hZ, vQ₆]
  have hev₁₀ : word s₁₀.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by
    have hk : ∀ {cs : List Rc} {m m' : Mem}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .hdr kEv ∉ cs →
        word m' I.B (8 * kEv) = word m I.B (8 * kEv) := fun f ok hn => f.word ok (by decide) hn
    rw [hk f₁₀ hokC (by decide), hk f₉ hokC (by decide), hk f₈ hokI (by decide), hk f₇ hok7 (by decide),
      hk f₆ (by decide) (by decide), hk f₅ (by decide) (by decide), hk f₄ hok4 (by decide),
      hk f₃ (by decide) (by decide), hk f₂ (by decide) (by decide), hk f₁ (by decide) (by decide), hev]
  -- `e⁻¹ mod 2⁶⁴` into `rcx`.
  have oddE : ∀ {u : State}, u.gpr .rbx = BitVec.ofNat 64 e → (u.gpr .rbx).toNat % 2 = 1 := fun hb => by
    rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]; exact heo
  simp only [seqs]
  have hld := fun (i : Nat) (hi : i < 32) => h₁₀.ws.scr.ld (d := 8 * i) (by have := h.ws.h256; omega_using [hi, this])
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 e ∧
    t.mem = s₁₀.mem) (by xrun [State.ea, hdr, h₁₀.ws.rdi, hdrOff, hld kEv (by decide), hev₁₀]) rfl)
    fun s₁₁ ⟨⟨hbx₁₁, m₁₁⟩, k₁₁⟩ => WP.mono (minvC_ok s₁₁ (oddE hbx₁₁)) fun s₁₂ ⟨hinv₁₂, _, k₁₂, m₁₂⟩ => ?_))
  rw [hbx₁₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64] at hinv₁₂
  generalize hei : (s₁₂.gpr .rcx).toNat = einv at hinv₁₂
  have hm₁₂ : s₁₂.mem = s₁₀.mem := by rw [m₁₂, m₁₁]
  have h₁₂ := h₁₀.step (cs := []) (by rw [hm₁₂]; exact KF.refl _ _ _) rfl (k₁₁.trans k₁₂) (by decide)
  -- `c` into `r15`, `t` into `sMo`.
  have sX := h.ws.sl (j := aX₂) (by decide)
  have sR := h.ws.sl (j := aR) (by decide)
  have wX : (word s₁₂.mem I.B (slot I.W aX₂)).toNat = x := by
    rw [hm₁₂]; exact word0_of_lt hw1 vX₁₀ (Nat.lt_trans hxe he64)
  have wR : (word s₁₂.mem I.B (slot I.W aR)).toNat = L % e := by
    rw [hm₁₂]; exact word0_of_lt hw1 vR₁₀ (Nat.lt_trans hR he64)
  refine WP.seq (WP.mono (Q := fun (t : State) => (t.gpr .r15).toNat = ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧
    t.mem = s₁₂.mem.writeW (off I.B (8 * sMo)) (BitVec.ofNat 64 (e - x)) ∧
    Keep [.r12, .r9, .rbx, .r10, .rsi, .rax, .rdx, .r15] s₁₂ t) ?_ fun s₁₃ ⟨c₁₃, m₁₃, k₁₃⟩ => ?_)
  · rw [List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h₁₂.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h₁₂.ws.rdi
    refine WP.mono (base_ok aX₂ (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aR (r := .r10) (by decide) ((ku₂.gpr (by decide)).trans hdi₁)
      ((ku₂.gpr (by decide)).trans h9)) fun u₃ ⟨h10, mu₃, ku₃⟩ => ?_
    have hmu : u₃.mem = s₁₂.mem := by rw [mu₃, mu₂, mu₁]
    have hs₃ := h₁₂.ws.scr.congr ((ku₁.trans ku₂).trans ku₃).2.2
    have hdi₃ : u₃.gpr .rdi = I.B := ((ku₂.trans ku₃).gpr (by decide)).trans hdi₁
    have hcx : u₃.gpr .rcx = s₁₂.gpr .rcx := ((ku₁.trans ku₂).trans ku₃).gpr (by decide)
    have hbx₃ : u₃.gpr .rbx = off I.B (slot I.W aX₂) := (ku₃.gpr (by decide)).trans hbx
    have hev₁₂ : word s₁₂.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [hm₁₂, hev₁₀]
    refine WP.mono (WP.keep [.rsi, .rax, .rdx, .r15] (Q := fun t =>
      (t.gpr .r15).toNat = ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧
      t.mem = s₁₂.mem.writeW (off I.B (8 * sMo)) (BitVec.ofNat 64 (e - x))) (by
        xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₃.ld (d := slot I.W aX₂) (by omega_using [sX]), hs₃.ld (d := slot I.W aR) (by omega_using [sR]),
          hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
          hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_using [this]), hmu, hcx, execMul]
        have hX' : s₁₂.mem.readW (off I.B (slot I.W aX₂)) 64 = BitVec.ofNat 64 x :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wX])]; exact wX)
        have hE' : s₁₂.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev₁₂
        have hR' : (s₁₂.mem.readW (off I.B (slot I.W aR)) 64).toNat = L % e := wR
        rw [hE', hX', ofNat_sub' (by omega_using [hxe]) he64, hR', hei]
        refine ⟨?_, rfl⟩
        simp only [BitVec.toNat_ofNat, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show e - x < 2 ^ 64 by omega_using [he64])]) rfl) fun t ⟨⟨hc, hm⟩, k⟩ => ⟨hc, hm, (((ku₁.trans ku₂).trans ku₃).trans k).mono (by simp)⟩
  generalize hcv : ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 = c at c₁₃
  obtain ⟨h₁₃, f₁₃, mo₁₃⟩ := h₁₂.hdrW (i := sMo) (by unfold sMo sFn; omega_using []) m₁₃ k₁₃ (by decide)
  -- `[aDd] := c`.
  refine WP.seq (WP.mono (zeroA_k h₁₃ (j := aDd) (by decide)) fun s₁₄ ⟨h₁₄, f₁₄, z₁₄, k₁₄⟩ => ?_)
  have c₁₄ : (s₁₄.gpr .r15).toNat = c := by rw [k₁₄.gpr (by decide)]; exact c₁₃
  have mo₁₄ : word s₁₄.mem I.B (8 * sMo) = BitVec.ofNat 64 (e - x) := by
    rw [f₁₄.word (by decide) (by decide) (by decide), mo₁₃]
  have sD := h.ws.sl (j := aDd) (by decide)
  have sQ := h.ws.sl (j := aQt) (by decide)
  have spDQ := slot_far (w := I.W) (i := aDd) (j := aQt) (by decide)
  refine WP.seq (WP.mono (Q := fun (t : State) => t.mem = s₁₄.mem.writeW (off I.B (slot I.W aDd)) (s₁₄.gpr .r15) ∧
    t.gpr .r8 = off I.B (slot I.W aDd) ∧ t.gpr .r9 = off I.B (slot I.W aQt) ∧
    t.gpr .rcx = BitVec.ofNat 64 (e - x) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
    Keep [.r12, .r9, .r8, .rax, .rcx] s₁₄ t) ?_ fun s₁₅ ⟨m₁₅, h8, h9, hcx, h12, k₁₅⟩ => ?_)
  · rw [List.append_assoc, List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h₁₄.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    have hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h₁₄.ws.rdi
    refine WP.mono (base_ok aDd (r := .r8) (by decide) hdi₁ h9) fun u₂ ⟨h8, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    have hs₂ := h₁₄.ws.scr.congr (ku₁.trans ku₂).2.2
    have h15 : u₂.gpr .r15 = s₁₄.gpr .r15 := (ku₁.trans ku₂).gpr (by decide)
    refine WP.mono (WP.keep [] (c := .block [.store (at0 .r8) .r15]) (Q := fun t => t.mem = s₁₄.mem.writeW
      (off I.B (slot I.W aDd)) (s₁₄.gpr .r15)) (by
        xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₂.st (d := slot I.W aDd) (by omega_using [sD]), h15, mu₂, mu₁]) rfl) fun u₃ ⟨mu₃, ku₃⟩ => WP.block_append_iff.mpr ?_
    have hdi₃ : u₃.gpr .rdi = I.B := ((ku₂.trans ku₃).gpr (by decide)).trans hdi₁
    have h9₃ : u₃.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := ((ku₂.trans ku₃).gpr (by decide)).trans h9
    refine WP.mono (base_ok aQt (r := .rax) (by decide) hdi₃ h9₃) fun u₄ ⟨hax, mu₄, ku₄⟩ => ?_
    have hs₄ := h₁₄.ws.scr.congr (((ku₁.trans ku₂).trans ku₃).trans ku₄).2.2
    have mo₄ : word u₄.mem I.B (8 * sMo) = BitVec.ofNat 64 (e - x) := by
      rw [mu₄, mu₃, (writeW_outside s₁₄.mem I.B (s₁₄.gpr .r15) (d := slot I.W aDd) (by omega_using [hn, sD])).word
        (Or.inl (hdr_lt_slot I.W aDd (show sMo < 32 by decide))) (by unfold sMo sFn; omega_using []), mo₁₄]
    refine WP.mono (WP.keep [.r9, .rcx] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQt) ∧
      t.gpr .rcx = BitVec.ofNat 64 (e - x) ∧ t.mem = u₄.mem) (by
        xrun [State.ea, hdr, (ku₄.gpr (by decide)).trans hdi₃, hdrOff, hax,
          hs₄.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_using [this]), mo₄]) rfl) fun t ⟨⟨h9t, hcxt, mt⟩, kt⟩ =>
      ⟨by rw [mt, mu₄, mu₃], ((ku₄.trans kt).gpr (by decide)).trans ((ku₃.gpr (by decide)).trans h8), h9t, hcxt,
        (((ku₂.trans ku₃).trans ku₄).trans kt).gpr (by decide) |>.trans h12,
        ((((ku₁.trans ku₂).trans ku₃).trans ku₄).trans kt).mono (by simp)⟩
  have o₁₅ := writeW_outside s₁₄.mem I.B (s₁₄.gpr .r15) (d := slot I.W aDd) (by omega_using [hn, sD])
  rw [← m₁₅] at o₁₅
  have f₁₅ := KF.arr1 (I := I) (j := aDd) o₁₅ (Nat.le_refl _) (by omega_using [])
  have h₁₅ := h₁₄.step f₁₅ (all_mut_arr (by decide)) k₁₅ (by decide)
  have vD₁₅ : wv s₁₅.mem I.B (slot I.W aDd) (I.W + 2) = c := by
    rw [m₁₅]
    have := wv_put (m := s₁₄.mem) (B := I.B) (d := slot I.W aDd) (N := I.W + 2) (k := 0) (s₁₄.gpr .r15)
      ((wv_eq_zero_iff _ _ _ _).mp z₁₄) (by omega_using [hn, sD]) (by omega_using []) (I.W + 2) (Nat.le_refl _)
    rw [Nat.mul_zero, Nat.add_zero] at this
    rw [this, ite_eq_left (show 0 < I.W + 2 by omega_using []), Nat.pow_zero, Nat.one_mul, c₁₄]
  have hokD : [Rc.arr aDd].all Rc.ok = true := by decide
  have vQ₁₅ : av I s₁₅.mem aQt = L / e := by
    rw [f₁₅.av hokD (by decide) (by decide) hZ, f₁₄.av hokD (by decide) (by decide) hZ,
      f₁₃.av (by decide) (by decide) (by decide) hZ]
    show wv s₁₂.mem I.B (slot I.W aQt) I.W = L / e
    rw [hm₁₂]; exact vQ₁₀
  -- `[aDd] += t Q`.
  have hcl : c < 2 ^ 64 := by rw [← hcv]; exact Nat.mod_lt _ (by decide)
  have hQ : L / e < 2 ^ (64 * I.W) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLW
  have hbound : c + (e - x) * (L / e) < 2 ^ (64 * (I.W + 2)) := by
    have h1 : (e - x) * (L / e) < 2 ^ 64 * 2 ^ (64 * I.W) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega_using [he64]) (Nat.le_of_lt hQ) (by omega_using [dQ, hQ])
    have h2 : 2 ^ 64 + 2 ^ 64 * 2 ^ (64 * I.W) ≤ 2 ^ (64 * (I.W + 2)) := by
      rw [show 64 * (I.W + 2) = 64 + 64 + 64 * I.W by omega_using [], Nat.pow_add, Nat.pow_add]
      have : 1 ≤ 2 ^ (64 * I.W) := Nat.one_le_two_pow
      have : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * I.W) := Nat.le_mul_of_pos_right _ (by omega_using [this])
      have : 2 * (2 ^ 64 * 2 ^ (64 * I.W)) ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ (64 * I.W) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega_arith
    omega_using [hcl, h1, h2]
  have vQ' : wv s₁₅.mem I.B (slot I.W aQt) I.W = L / e := vQ₁₅
  have hbound' : c + (e - x) * wv s₁₅.mem I.B (slot I.W aQt) I.W < 2 ^ (64 * (I.W + 2)) := by rw [vQ']; exact hbound
  refine WP.mono (mulAddRow_ok h₁₅.ws.scr h8 h9 h12 (by omega_using [hw1]) (by omega_using [hw2]) (by omega_using [sD])
      (by omega_using [sQ]) (by omega_using [spDQ])
    (by rw [vD₁₅, hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [he64])]
        exact hbound')) fun t ⟨hv, o, kt⟩ => ?_
  rw [vD₁₅, hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show e - x < 2 ^ 64 by omega_using [he64]), vQ'] at hv
  have ft := KF.arr1 (I := I) (j := aDd) o (Nat.le_refl _) (Nat.le_refl _)
  have ht := h₁₅.step ft (all_mut_arr (by decide)) kt (by decide)
  have hok₁₃ : [Rc.hdr sMo].all Rc.ok = true := by decide
  have okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (L % e) e = 1) && !decide (L < 2)) := by
    rw [ft.word hokD (by decide) (by decide), f₁₅.word hokD (by decide) (by decide),
      f₁₄.word hokD (by decide) (by decide), f₁₃.word hok₁₃ (by decide) (by decide), hm₁₂, ok₁₀]
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · have f₁₂ : KF I.B I.W [] s₁₀.mem s₁₂.mem := by rw [hm₁₂]; exact KF.refl _ _ _
    exact ((((((((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).trans f₁₂).trans f₁₃).trans f₁₄).trans f₁₅).trans ft).mono (by simp)
  · -- The inverse exists iff both hold.
    have hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (2 ≤ L ∧ Nat.gcd (L % e) e = 1) := fun ⟨h1, h2⟩ => hc (by simp [h2]; omega_using [h1])
      rw [inverse_odd_none he3 hQR this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      have hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.1] at this; exact_mod_cast this
      exact ⟨_, inverse_odd he3 he64 (by omega_using [hc]) hQR hR hx1 hxe hinv₁₂⟩
  · intro d hd
    by_cases hc : 2 ≤ L ∧ Nat.gcd (L % e) e = 1
    · have hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
      have hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.2] at this; exact_mod_cast this
      rw [inverse_odd he3 he64 hc.1 hQR hR hx1 hxe hinv₁₂, hcv] at hd
      cases hd
      have hdL := (inverse_some (inverse_odd he3 he64 hc.1 hQR hR hx1 hxe hinv₁₂)).2 (by omega_using [hc])
      rw [hcv] at hdL
      exact av_of_full (by rw [hv, Nat.add_comm, Nat.mul_comm]) (by omega_using [hLW, hdL])
    · rw [inverse_odd_none he3 (Nat.div_add_mod L e).symm hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.X86_64.Key

end
