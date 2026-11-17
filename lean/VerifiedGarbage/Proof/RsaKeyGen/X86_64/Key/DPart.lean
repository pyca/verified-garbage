module

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Halve
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Front
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Minv
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! ### `RsaKeyGen.X86_64.Key.DOdd`, which this module and modules that import it used -/

section

/-! ## DBase -/

@[expose] public section

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
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by have := h.ws.w1; omega_using [this]))

/-- `loadEv`: `[aE] := e` over `W + 2` words. -/
theorem loadEv_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e : Nat} (he : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) :
    WP isa (seqs loadEv) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aE] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aE) (I.W + 2) = e := by
  have hn := h.ws.scr.nowrap
  obtain sE := h.ws.sl (j := aE) (by decide)
  simp only [loadEv, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aE) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  obtain hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [f₁.word (by decide) (by decide) (by decide), hev]
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h₁.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aE (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h₁.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  obtain hs₃ := h₁.ws.scr.congr (k₂.trans k₃).2.2
  obtain hdi₃ : s₃.gpr .rdi = I.B := ((k₂.trans k₃).gpr (by decide)).trans h₁.ws.rdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aE)) (BitVec.ofNat 64 e)) (by
    xrun [State.ea, at0, hdr, hbx, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]), hs₃.st (d := slot I.W aE) (by omega_using [sE]),
      m₃, m₂, hev₁]) rfl) fun t ⟨hm, k₄⟩ => ?_
  obtain o₄ := writeW_outside s₁.mem I.B (BitVec.ofNat 64 e) (d := slot I.W aE) (by omega_using [hn, sE])
  rw [← hm] at o₄
  obtain f₄ := KF.arr1 (I := I) (j := aE) o₄ (Nat.le_refl _) (by omega_using [])
  refine ⟨h₁.step f₄ (all_mut_arr (by decide)) ((k₂.trans k₃).trans k₄) (by decide), (f₁.trans f₄).mono (by decide), ?_⟩
  rw [hm]
  have := wv_put (m := s₁.mem) (B := I.B) (d := slot I.W aE) (N := I.W + 2) (k := 0) (BitVec.ofNat 64 e)
    ((wv_eq_zero_iff _ _ _ _).mp z₁) (by omega_using [hn, sE]) (by omega_using []) (I.W + 2) (Nat.le_refl _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rw [this, ite_eq_left (show 0 < I.W + 2 by omega_using []), Nat.pow_zero, Nat.one_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he]

/-- `lGe2`: `kOk := ` the mask of `L ≥ 2`. -/
theorem lGe2_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (seqs lGe2) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (!decide (av I s.mem aL < 2)) := by
  have hZ := h.hZ
  unfold lGe2
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h 2) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  obtain c2 : av I s₁.mem aC = 2 := av_of_full c₁ (two_le_pow h (by decide))
  obtain vL : av I s₁.mem aL = av I s.mem aL := f₁.av (by decide) (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₁ (a := aL) (b := aC) (by decide) (by decide))
    fun s₂ ⟨h₂, m₂, hbp, _, _, _, k₂⟩ => ?_)
  rw [vL, c2] at hbp
  simp only [seqs]
  obtain hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (av I s.mem aL < 2)))) (by xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) hm k₃ (by decide)
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by decide), hw⟩

/-- `gcdIsOne`: `kOk &= ` the mask of `[aV] = 1`. -/
theorem gcdIsOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {c : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (seqs gcdIsOne) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC, .hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (av I s.mem aV = 1) && c) := by
  have hZ := h.hZ
  unfold gcdIsOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  obtain c1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
  obtain vV : av I s₁.mem aV = av I s.mem aV := f₁.av (by decide) (by decide) (by decide) hZ
  obtain hok₁ : word s₁.mem I.B (8 * kOk) = mask c := by rw [f₁.word (by decide) (by decide) (by decide), hok]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₁ (a := aV) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, hbp, k₂⟩ => ?_)
  rw [vV, c1] at hbp
  simp only [seqs]
  obtain hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  obtain hld := h₂.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  obtain hok₂ : word s₂.mem I.B (8 * kOk) = mask c := by rw [m₂, hok₁]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (decide (av I s.mem aV = 1) && c))) (by
      xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hld, hbp, hok₂, mask_and']) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  obtain ⟨ht, f₃, hw⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) hm k₃ (by decide)
  exact ⟨ht, (f₁.trans (by rw [← m₂]; exact f₃)).mono (by decide), hw⟩

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
    .hdr kOk, .priv]

theorem dOdd_eq : dOdd = loadEv ++ ([zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] ++
    ([inverseK kOne aU aV aX₂ aE] ++ (lGe2 ++ (gcdIsOne ++
    ([.block (([.mov .rbx (.mem (hdr kEv))] : List Instr) ++ minv),
      .block (ws ++ base aX₂ .rbx ++ base aR .r10 ++
        ([.mov .rsi (.mem (hdr kEv)), .alu .sub .rsi (.mem (at0 .rbx)), .mov .rax (.mem (at0 .r10)), .mul .rsi,
          .alu .add .rax (.imm 1), .mul .rcx, .mov .r15 (.reg .rax), .store (hdr sMo) .rsi] : List Instr)),
      zeroA aDd,
      .block (ws ++ base aDd .r8 ++ ([.store (at0 .r8) .r15] : List Instr) ++ base aQt .rax ++
        ([.mov .r9 (.reg .rax), .mov .rcx (.mem (hdr sMo))] : List Instr)),
      mulAddRow] : List (Prog isa)))))) := by
  simp only [dOdd, List.append_assoc]

/-- A number below `2⁶⁴` is its low word. -/
theorem word0_of_lt {I : KIn} {m : Mem} {j v : Nat} (hw : 1 ≤ I.W) (h : av I m j = v) (hv : v < 2 ^ 64) :
    (word m I.B (slot I.W j)).toNat = v := by
  rw [← wv_mod64 _ _ _ hw, show wv m I.B (slot I.W j) I.W = av I m j from rfl, h, Nat.mod_eq_of_lt hv]

/-- `dOdd`, for an odd `e ≥ 3`. -/
theorem dOdd_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e L : Nat} (he3 : 3 ≤ e) (he64 : e < 2 ^ 64)
    (heo : e % 2 = 1) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dOdd) s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  have hw2 := h.ws.w2
  rw [dOdd_eq]
  -- `[aE] := e`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  obtain vE₁ : av I s₁.mem aE = e := av_of_full e₁ (two_le_pow h he64)
  obtain vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  -- `L = e Q + R`.
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aQt) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aQt) (a := aL) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aQt) (iR := aR) (iD := aE) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aU) (by decide)) fun s₅ ⟨h₅, f₅, z₅, _⟩ =>
          WP.mono (copyA_k h₅ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, t₆, _⟩ => ?_))))
  obtain vE₃ : av I s₃.mem aE = e := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vE₁]
  obtain vQ₃ : av I s₃.mem aQt = L := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  rw [vE₃, vQ₃] at d₄
  obtain ⟨dR, dQ⟩ := d₄ (by omega_using [heo])
  obtain hR : L % e < e := Nat.mod_lt _ (by omega_using [heo])
  obtain vR₄ : av I s₄.mem aR = L % e := by
    rw [← dR]; exact wv_low_of_lt (by omega_using []) (by rw [dR]; exact Nat.lt_trans hR (two_le_pow h he64))
  obtain hok4 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  obtain vU₆ : av I s₆.mem aU = L % e := by rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  obtain tU₆ : atop I s₆.mem aU = 0 := by rw [t₆]; exact (wv_zero2 z₅).2
  obtain pres6 : ∀ j, j < 16 → j ≠ aQt → j ≠ aR → j ≠ aT → j ≠ aU → av I s₆.mem j = av I s₃.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ]
  obtain vE₆ : av I s₆.mem aE = e := by rw [pres6 aE (by decide) (by decide) (by decide) (by decide) (by decide), vE₃]
  obtain vQ₆ : av I s₆.mem aQt = L / e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, dQ]
  obtain vR₆ : av I s₆.mem aR = L % e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, f₅.av (by decide) (by decide) (by decide) hZ, vR₄]
  obtain vL₆ : av I s₆.mem aL = L := by
    rw [pres6 aL (by decide) (by decide) (by decide) (by decide) (by decide), f₃.av (by decide) (by decide)
      (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  -- `x = R⁻¹ mod e`.
  refine wp_seqs_append (by simp) (by simp [lGe2]) ?_
  simp only [seqs]
  refine WP.mono (inverseK_k h₆ (k := kOne) (n := 1) (fun _ _ _ => kOne_ok) (Nat.le_refl _) hw1
    (iU := aU) (iV := aV) (iX₂ := aX₂) (iM := aE) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₈ ⟨h₈, f₈, _, hinv⟩ => ?_
  rw [vE₆, vU₆] at hinv
  obtain ⟨hg₈, hdv₈, hx₈⟩ := hinv (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_arith)) (by omega_arith)) he64 heo
  generalize hx : av I s₈.mem aX₂ = x at hdv₈ hx₈
  obtain hokI : [Rc.arr aV, Rc.arr aX₂, Rc.priv].all Rc.ok = true := by decide
  obtain vL₈ : av I s₈.mem aL = L := by
    rw [f₈.av hokI (by decide) (by decide) hZ, vL₆]
  -- `kOk := ` the masks of `L ≥ 2` and `gcd(R, e) = 1`.
  refine wp_seqs_append (by simp [lGe2, constA]) (by simp [gcdIsOne, constA]) (WP.mono (lGe2_k h₈)
    fun s₉ ⟨h₉, f₉, ok₉⟩ => ?_)
  rw [vL₈] at ok₉
  obtain vV₉ : av I s₉.mem aV = Nat.gcd (L % e) e := by rw [f₉.av (by decide) (by decide) (by decide) hZ, hg₈]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₉ ok₉)
    fun s₁₀ ⟨h₁₀, f₁₀, ok₁₀⟩ => ?_)
  rw [vV₉] at ok₁₀
  obtain hokC : [Rc.arr aC, Rc.hdr kOk].all Rc.ok = true := by decide
  obtain pres10 : ∀ j, j < 16 → j ≠ aC → av I s₁₀.mem j = av I s₈.mem j := fun j hj h1 => by
    rw [f₁₀.av hokC hj (by simp [h1]) hZ, f₉.av hokC hj (by simp [h1]) hZ]
  have hxe : x < e := hx₈
  obtain vX₁₀ : av I s₁₀.mem aX₂ = x := by rw [pres10 aX₂ (by decide) (by decide), hx]
  obtain vR₁₀ : av I s₁₀.mem aR = L % e := by
    rw [pres10 aR (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ, vR₆]
  obtain vQ₁₀ : av I s₁₀.mem aQt = L / e := by
    rw [pres10 aQt (by decide) (by decide), f₈.av hokI (by decide) (by decide) hZ, vQ₆]
  obtain hev₁₀ : word s₁₀.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by
    obtain hk : ∀ {cs : List Rc} {m m' : Mem}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .hdr kEv ∉ cs →
        word m' I.B (8 * kEv) = word m I.B (8 * kEv) := fun f ok hn => f.word ok (by decide) hn
    rw [hk f₁₀ hokC (by decide), hk f₉ hokC (by decide), hk f₈ hokI (by decide),
      hk f₆ (by decide) (by decide), hk f₅ (by decide) (by decide), hk f₄ hok4 (by decide),
      hk f₃ (by decide) (by decide), hk f₂ (by decide) (by decide), hk f₁ (by decide) (by decide), hev]
  -- `e⁻¹ mod 2⁶⁴` into `rcx`.
  obtain oddE : ∀ {u : State}, u.gpr .rbx = BitVec.ofNat 64 e → (u.gpr .rbx).toNat % 2 = 1 := fun hb => by
    rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]; exact heo
  simp only [seqs]
  obtain hld := fun (i : Nat) (hi : i < 32) => h₁₀.ws.scr.ld (d := 8 * i) (by have := h.ws.h256; omega_using [hi, this])
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 e ∧
    t.mem = s₁₀.mem) (by xrun [State.ea, hdr, h₁₀.ws.rdi, hdrOff, hld kEv (by decide), hev₁₀]) rfl)
    fun s₁₁ ⟨⟨hbx₁₁, m₁₁⟩, k₁₁⟩ => WP.mono (minvC_ok s₁₁ (oddE hbx₁₁)) fun s₁₂ ⟨hinv₁₂, _, k₁₂, m₁₂⟩ => ?_))
  rw [hbx₁₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64] at hinv₁₂
  generalize hei : (s₁₂.gpr .rcx).toNat = einv at hinv₁₂
  obtain hm₁₂ : s₁₂.mem = s₁₀.mem := by rw [m₁₂, m₁₁]
  obtain h₁₂ := h₁₀.step (cs := []) (by rw [hm₁₂]; exact KF.refl _ _ _) rfl (k₁₁.trans k₁₂) (by decide)
  -- `c` into `r15`, `t` into `sMo`.
  obtain sX := h.ws.sl (j := aX₂) (by decide)
  obtain sR := h.ws.sl (j := aR) (by decide)
  obtain wX : (word s₁₂.mem I.B (slot I.W aX₂)).toNat = x := by
    rw [hm₁₂]; exact word0_of_lt hw1 vX₁₀ (Nat.lt_trans hxe he64)
  obtain wR : (word s₁₂.mem I.B (slot I.W aR)).toNat = L % e := by
    rw [hm₁₂]; exact word0_of_lt hw1 vR₁₀ (Nat.lt_trans hR he64)
  refine WP.seq (WP.mono (Q := fun (t : State) => (t.gpr .r15).toNat = ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧
    t.mem = s₁₂.mem.writeW (off I.B (8 * sMo)) (BitVec.ofNat 64 (e - x)) ∧
    Keep [.r12, .r9, .rbx, .r10, .rsi, .rax, .rdx, .r15] s₁₂ t) ?_ fun s₁₃ ⟨c₁₃, m₁₃, k₁₃⟩ => ?_)
  · rw [List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h₁₂.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    obtain hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h₁₂.ws.rdi
    refine WP.mono (base_ok aX₂ (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aR (r := .r10) (by decide) ((ku₂.gpr (by decide)).trans hdi₁)
      ((ku₂.gpr (by decide)).trans h9)) fun u₃ ⟨h10, mu₃, ku₃⟩ => ?_
    obtain hmu : u₃.mem = s₁₂.mem := by rw [mu₃, mu₂, mu₁]
    obtain hs₃ := h₁₂.ws.scr.congr ((ku₁.trans ku₂).trans ku₃).2.2
    obtain hdi₃ : u₃.gpr .rdi = I.B := ((ku₂.trans ku₃).gpr (by decide)).trans hdi₁
    obtain hcx : u₃.gpr .rcx = s₁₂.gpr .rcx := ((ku₁.trans ku₂).trans ku₃).gpr (by decide)
    obtain hbx₃ : u₃.gpr .rbx = off I.B (slot I.W aX₂) := (ku₃.gpr (by decide)).trans hbx
    obtain hev₁₂ : word s₁₂.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [hm₁₂, hev₁₀]
    refine WP.mono (WP.keep [.rsi, .rax, .rdx, .r15] (Q := fun t =>
      (t.gpr .r15).toNat = ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 ∧
      t.mem = s₁₂.mem.writeW (off I.B (8 * sMo)) (BitVec.ofNat 64 (e - x))) (by
        xrun [State.ea, at0, hdr, hbx₃, h10, hdi₃, hdrOff, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₃.ld (d := slot I.W aX₂) (by omega_using [sX]), hs₃.ld (d := slot I.W aR) (by omega_using [sR]),
          hs₃.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
          hs₃.st (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_using [this]), hmu, hcx, execMul]
        obtain hX' : s₁₂.mem.readW (off I.B (slot I.W aX₂)) 64 = BitVec.ofNat 64 x :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wX])]; exact wX)
        have hE' : s₁₂.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev₁₂
        have hR' : (s₁₂.mem.readW (off I.B (slot I.W aR)) 64).toNat = L % e := wR
        rw [hE', hX', ofNat_sub' (by omega_using [hxe]) he64, hR', hei]
        refine ⟨?_, rfl⟩
        simp only [BitVec.toNat_ofNat, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (show e - x < 2 ^ 64 by omega_using [he64])]) rfl) fun t ⟨⟨hc, hm⟩, k⟩ => ⟨hc, hm, (((ku₁.trans ku₂).trans ku₃).trans k).mono (by decide)⟩
  generalize hcv : ((L % e * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 = c at c₁₃
  obtain ⟨h₁₃, f₁₃, mo₁₃⟩ := h₁₂.hdrW (i := sMo) (by unfold sMo sFn; omega_using []) m₁₃ k₁₃ (by decide)
  -- `[aDd] := c`.
  refine WP.seq (WP.mono (zeroA_k h₁₃ (j := aDd) (by decide)) fun s₁₄ ⟨h₁₄, f₁₄, z₁₄, k₁₄⟩ => ?_)
  obtain c₁₄ : (s₁₄.gpr .r15).toNat = c := by rw [k₁₄.gpr (by decide)]; exact c₁₃
  obtain mo₁₄ : word s₁₄.mem I.B (8 * sMo) = BitVec.ofNat 64 (e - x) := by
    rw [f₁₄.word (by decide) (by decide) (by decide), mo₁₃]
  obtain sD := h.ws.sl (j := aDd) (by decide)
  obtain sQ := h.ws.sl (j := aQt) (by decide)
  obtain spDQ := slot_far (w := I.W) (i := aDd) (j := aQt) (by decide)
  refine WP.seq (WP.mono (Q := fun (t : State) => t.mem = s₁₄.mem.writeW (off I.B (slot I.W aDd)) (s₁₄.gpr .r15) ∧
    t.gpr .r8 = off I.B (slot I.W aDd) ∧ t.gpr .r9 = off I.B (slot I.W aQt) ∧
    t.gpr .rcx = BitVec.ofNat 64 (e - x) ∧ t.gpr .r12 = BitVec.ofNat 64 I.W ∧
    Keep [.r12, .r9, .r8, .rax, .rcx] s₁₄ t) ?_ fun s₁₅ ⟨m₁₅, h8, h9, hcx, h12, k₁₅⟩ => ?_)
  · rw [List.append_assoc, List.append_assoc, List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h₁₄.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    obtain hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h₁₄.ws.rdi
    refine WP.mono (base_ok aDd (r := .r8) (by decide) hdi₁ h9) fun u₂ ⟨h8, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    obtain hs₂ := h₁₄.ws.scr.congr (ku₁.trans ku₂).2.2
    obtain h15 : u₂.gpr .r15 = s₁₄.gpr .r15 := (ku₁.trans ku₂).gpr (by decide)
    refine WP.mono (WP.keep [] (c := .block [.store (at0 .r8) .r15]) (Q := fun t => t.mem = s₁₄.mem.writeW
      (off I.B (slot I.W aDd)) (s₁₄.gpr .r15)) (by
        xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₂.st (d := slot I.W aDd) (by omega_using [sD]), h15, mu₂, mu₁]) rfl) fun u₃ ⟨mu₃, ku₃⟩ => WP.block_append_iff.mpr ?_
    obtain hdi₃ : u₃.gpr .rdi = I.B := ((ku₂.trans ku₃).gpr (by decide)).trans hdi₁
    obtain h9₃ : u₃.gpr .r9 = BitVec.ofNat 64 (8 * (I.W + 2)) := ((ku₂.trans ku₃).gpr (by decide)).trans h9
    refine WP.mono (base_ok aQt (r := .rax) (by decide) hdi₃ h9₃) fun u₄ ⟨hax, mu₄, ku₄⟩ => ?_
    obtain hs₄ := h₁₄.ws.scr.congr (((ku₁.trans ku₂).trans ku₃).trans ku₄).2.2
    obtain mo₄ : word u₄.mem I.B (8 * sMo) = BitVec.ofNat 64 (e - x) := by
      rw [mu₄, mu₃, (writeW_outside s₁₄.mem I.B (s₁₄.gpr .r15) (d := slot I.W aDd) (by omega_using [hn, sD])).word
        (Or.inl (hdr_lt_slot I.W aDd (show sMo < 32 by decide))) (by unfold sMo sFn; omega_using []), mo₁₄]
    refine WP.mono (WP.keep [.r9, .rcx] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQt) ∧
      t.gpr .rcx = BitVec.ofNat 64 (e - x) ∧ t.mem = u₄.mem) (by
        xrun [State.ea, hdr, (ku₄.gpr (by decide)).trans hdi₃, hdrOff, hax,
          hs₄.ld (d := 8 * sMo) (by have := h.ws.h256; unfold sMo sFn; omega_using [this]), mo₄]) rfl) fun t ⟨⟨h9t, hcxt, mt⟩, kt⟩ =>
      ⟨by rw [mt, mu₄, mu₃], ((ku₄.trans kt).gpr (by decide)).trans ((ku₃.gpr (by decide)).trans h8), h9t, hcxt,
        (((ku₂.trans ku₃).trans ku₄).trans kt).gpr (by decide) |>.trans h12,
        ((((ku₁.trans ku₂).trans ku₃).trans ku₄).trans kt).mono (by decide)⟩
  obtain o₁₅ := writeW_outside s₁₄.mem I.B (s₁₄.gpr .r15) (d := slot I.W aDd) (by omega_using [hn, sD])
  rw [← m₁₅] at o₁₅
  obtain f₁₅ := KF.arr1 (I := I) (j := aDd) o₁₅ (Nat.le_refl _) (by omega_using [])
  obtain h₁₅ := h₁₄.step f₁₅ (all_mut_arr (by decide)) k₁₅ (by decide)
  obtain vD₁₅ : wv s₁₅.mem I.B (slot I.W aDd) (I.W + 2) = c := by
    rw [m₁₅]
    have := wv_put (m := s₁₄.mem) (B := I.B) (d := slot I.W aDd) (N := I.W + 2) (k := 0) (s₁₄.gpr .r15)
      ((wv_eq_zero_iff _ _ _ _).mp z₁₄) (by omega_using [hn, sD]) (by omega_using []) (I.W + 2) (Nat.le_refl _)
    rw [Nat.mul_zero, Nat.add_zero] at this
    rw [this, ite_eq_left (show 0 < I.W + 2 by omega_using []), Nat.pow_zero, Nat.one_mul, c₁₄]
  obtain hokD : [Rc.arr aDd].all Rc.ok = true := by decide
  obtain vQ₁₅ : av I s₁₅.mem aQt = L / e := by
    rw [f₁₅.av hokD (by decide) (by decide) hZ, f₁₄.av hokD (by decide) (by decide) hZ,
      f₁₃.av (by decide) (by decide) (by decide) hZ]
    show wv s₁₂.mem I.B (slot I.W aQt) I.W = L / e
    rw [hm₁₂]; exact vQ₁₀
  -- `[aDd] += t Q`.
  obtain hcl : c < 2 ^ 64 := by rw [← hcv]; exact Nat.mod_lt _ (by decide)
  obtain hQ : L / e < 2 ^ (64 * I.W) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLW
  obtain hbound : c + (e - x) * (L / e) < 2 ^ (64 * (I.W + 2)) := by
    obtain h1 : (e - x) * (L / e) < 2 ^ 64 * 2 ^ (64 * I.W) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega_using [he64]) (Nat.le_of_lt hQ) (by omega_using [dQ, hQ])
    obtain h2 : 2 ^ 64 + 2 ^ 64 * 2 ^ (64 * I.W) ≤ 2 ^ (64 * (I.W + 2)) := by
      rw [show 64 * (I.W + 2) = 64 + 64 + 64 * I.W by omega_using [], Nat.pow_add, Nat.pow_add]
      have : 1 ≤ 2 ^ (64 * I.W) := Nat.one_le_two_pow
      have : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * I.W) := Nat.le_mul_of_pos_right _ (by omega_using [this])
      have : 2 * (2 ^ 64 * 2 ^ (64 * I.W)) ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ (64 * I.W) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega_arith
    omega_using [hcl, h1, h2]
  have vQ' : wv s₁₅.mem I.B (slot I.W aQt) I.W = L / e := vQ₁₅
  obtain hbound' : c + (e - x) * wv s₁₅.mem I.B (slot I.W aQt) I.W < 2 ^ (64 * (I.W + 2)) := by rw [vQ']; exact hbound
  refine WP.mono (mulAddRow_ok h₁₅.ws.scr h8 h9 h12 (by omega_using [hw1]) (by omega_using [hw2]) (by omega_using [sD])
      (by omega_using [sQ]) (by omega_using [spDQ])
    (by rw [vD₁₅, hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [he64])]
        exact hbound')) fun t ⟨hv, o, kt⟩ => ?_
  rw [vD₁₅, hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show e - x < 2 ^ 64 by omega_using [he64]), vQ'] at hv
  obtain ft := KF.arr1 (I := I) (j := aDd) o (Nat.le_refl _) (Nat.le_refl _)
  obtain ht := h₁₅.step ft (all_mut_arr (by decide)) kt (by decide)
  obtain hok₁₃ : [Rc.hdr sMo].all Rc.ok = true := by decide
  obtain okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (L % e) e = 1) && !decide (L < 2)) := by
    rw [ft.word hokD (by decide) (by decide), f₁₅.word hokD (by decide) (by decide),
      f₁₄.word hokD (by decide) (by decide), f₁₃.word hok₁₃ (by decide) (by decide), hm₁₂, ok₁₀]
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · have f₁₂ : KF I.B I.W [] s₁₀.mem s₁₂.mem := by rw [hm₁₂]; exact KF.refl _ _ _
    exact (((((((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₈).trans f₉).trans
      f₁₀).trans f₁₂).trans f₁₃).trans f₁₄).trans f₁₅).trans ft).mono (by decide)
  · -- The inverse exists iff both hold.
    obtain hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (2 ≤ L ∧ Nat.gcd (L % e) e = 1) := fun ⟨h1, h2⟩ => hc (by simp [h2]; omega_using [h1])
      rw [inverse_odd_none he3 hQR this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      obtain hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.1] at this; exact_mod_cast this
      exact ⟨_, inverse_odd he3 he64 (by omega_using [hc]) hQR hR hx1 hxe hinv₁₂⟩
  · intro d hd
    by_cases hc : 2 ≤ L ∧ Nat.gcd (L % e) e = 1
    · have hQR : L = e * (L / e) + L % e := (Nat.div_add_mod L e).symm
      obtain hx1 : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1 := by
        have := hdv₈; rw [hg₈, hc.2] at this; exact_mod_cast this
      rw [inverse_odd he3 he64 hc.1 hQR hR hx1 hxe hinv₁₂, hcv] at hd
      cases hd
      obtain hdL := (inverse_some (inverse_odd he3 he64 hc.1 hQR hR hx1 hxe hinv₁₂)).2 (by omega_using [hc])
      rw [hcv] at hdL
      exact av_of_full (by rw [hv, Nat.add_comm, Nat.mul_comm]) (by omega_using [hLW, hdL])
    · rw [inverse_odd_none he3 (Nat.div_add_mod L e).symm hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

end

/-! ## DEven -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: `d` for an even `e`

`d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`, by `inverse` modulo `L` (or
3 otherwise) (`dEven_k`, `inverse_even`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem dEven_eq : dEven = loadEv ++ ([zeroA aM, copyA aM aL] ++ (constA 0 ++ (eqMask aL aC ++
    (([.block [.mov .r15 (.reg .rbp)]] : List (Prog isa)) ++ (constA 1 ++
    (([.block (ws ++ base aM .rbx ++ base aC .r10 ++ ([.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .r15),
        .alu .and .rdx (.imm 1), .alu .or .rax (.reg .rdx), .store (at0 .rbx) .rax] : List Instr)),
      zeroA aQt, copyA aQt aE, divmod aQt aR aM aT, zeroA aU, copyA aU aR] : List (Prog isa)) ++ (constA 3 ++ (ltA aL aC ++
    (([.block (([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ oddMask aL ++
        ([.alu .and .rax (.reg .rcx), .store (hdr kOk) .rax, .mov .rbp (.reg .rax)] : List Instr)),
      zeroA aM, copyA aM aL] : List (Prog isa)) ++ (selC aM ++ ([inverse aU aV aX₂ aM] ++ (gcdIsOne ++
    [zeroA aDd, copyA aDd aX₂])))))))))))) := by
  simp only [dEven, List.append_assoc]

theorem or_and1_mask (x : BitVec 64) (c : Bool) :
    x ||| (mask c &&& 1) = if c then x ||| 1 else x := by
  cases c
  · simp [mask]
  · simp [mask]

/-- `[j] := [j] | 1` for `[j] = 0` if `c`, else `[j]` unchanged. -/
theorem av_or1 {I : KIn} {m : Mem} {j : Nat} (hw : 1 ≤ I.W) (hj : slot I.W j + 8 * I.W ≤ 2 ^ 64) {c : Bool}
    (hc : c = true → av I m j = 0) :
    av I (m.writeW (off I.B (slot I.W j)) (if c then word m I.B (slot I.W j) ||| 1 else word m I.B (slot I.W j))) j =
      (if c then 1 else av I m j) := by
  obtain o := writeW_outside m I.B (if c then word m I.B (slot I.W j) ||| 1 else word m I.B (slot I.W j))
    (d := slot I.W j) (by omega_arith)
  dsimp only [av] at hc ⊢
  rw [VG.Proof.Rsa.X86_64.wv_low hw, VG.Proof.Rsa.X86_64.wv_low (m := m) hw, word_writeW_self,
    o.wv (Or.inr (Nat.le_refl _)) (by omega_arith)]
  cases c
  · simp
  · have hz := hc rfl
    rw [VG.Proof.Rsa.X86_64.wv_low (m := m) hw] at hz
    obtain h0 : (word m I.B (slot I.W j)).toNat = 0 := by omega_arith
    obtain h1 : wv m I.B (slot I.W j + 8) (I.W - 1) = 0 := by
      rcases Nat.eq_zero_or_pos (wv m I.B (slot I.W j + 8) (I.W - 1)) with h | h
      · exact h
      · have := Nat.le_mul_of_pos_right (2 ^ 64) h; omega_arith
    have : word m I.B (slot I.W j) = 0 := BitVec.eq_of_toNat_eq h0
    simp only [ite_true]
    rw [this, h1]; decide

/-- `dEven`, for an even `e`. -/
theorem dEven_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hee : e % 2 = 0) (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L)
    (hLW : L < 2 ^ (64 * I.W)) :
    WP isa (seqs dEven) s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  rw [dEven_eq]
  -- `[aE] := e`, `[aM] := L`.
  refine wp_seqs_append (by simp [loadEv]) (by simp) (WP.mono (loadEv_k h he64 hev) fun s₁ ⟨h₁, f₁, e₁⟩ => ?_)
  obtain vE₁ : av I s₁.mem aE = e := av_of_full e₁ (two_le_pow h he64)
  obtain vL₁ : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h₁ (o := aM) (a := aL) (by decide) (by decide)
    (by decide)) fun s₂ ⟨h₂, f₂, v₂, _⟩ => ?_)
  rw [vL₁] at v₂
  -- `r15 := ` the mask of `L = 0`.
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₂ 0) fun s₃ ⟨h₃, f₃, c₃, _⟩ => ?_)
  obtain c0 : av I s₃.mem aC = 0 := av_of_full c₃ (Nat.two_pow_pos _)
  obtain vL₃ : av I s₃.mem aL = L := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, vL₁]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₃ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₄ ⟨h₄, m₄, hbp₄, k₄⟩ => ?_)
  rw [vL₃, c0] at hbp₄
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (decide (L = 0)) ∧ t.mem = s₄.mem)
    (by xrun [hbp₄]) rfl) fun s₅ ⟨⟨h15₅, m₅⟩, k₅⟩ => ?_
  obtain h₅ := h₄.step (cs := []) (by rw [m₅]; exact KF.refl _ _ _) rfl k₅ (by decide)
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₅ 1) fun s₆ ⟨h₆, f₆, _, k₆⟩ => ?_)
  obtain h15₆ : s₆.gpr .r15 = mask (decide (L = 0)) := by rw [k₆.gpr (by decide), h15₅]
  obtain vM₆ : av I s₆.mem aM = L := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, m₅, m₄, f₃.av (by decide) (by decide) (by decide) hZ, v₂]
  obtain vE₆ : av I s₆.mem aE = e := by
    rw [f₆.av (by decide) (by decide) (by decide) hZ, m₅, m₄, f₃.av (by decide) (by decide) (by decide) hZ,
      f₂.av (by decide) (by decide) (by decide) hZ, vE₁]
  obtain vL₆ : av I s₆.mem aL = L := by rw [f₆.av (by decide) (by decide) (by decide) hZ, m₅, m₄, vL₃]
  -- `[aM] := L`, or 1 for `L = 0`.
  obtain sM := h.ws.sl (j := aM) (by decide)
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.mem = s₆.mem.writeW (off I.B (slot I.W aM))
      (if decide (L = 0) then word s₆.mem I.B (slot I.W aM) ||| 1 else word s₆.mem I.B (slot I.W aM)) ∧
      Keep [.r12, .r9, .rbx, .r10, .rax, .rdx] s₆ t) ?_ fun s₇ ⟨m₇, k₇⟩ => ?_)
  · simp only [List.append_assoc]
    refine WP.block_append_iff.mpr (WP.mono h₆.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
    obtain hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h₆.ws.rdi
    refine WP.mono (base_ok aM (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .r10) (by decide) ((ku₂.gpr (by decide)).trans hdi₁)
      ((ku₂.gpr (by decide)).trans h9)) fun u₃ ⟨_, mu₃, ku₃⟩ => ?_
    obtain hs₃ := h₆.ws.scr.congr ((ku₁.trans ku₂).trans ku₃).2.2
    obtain h15 : u₃.gpr .r15 = mask (decide (L = 0)) := by rw [((ku₁.trans ku₂).trans ku₃).gpr (by decide), h15₆]
    obtain hmu : u₃.mem = s₆.mem := by rw [mu₃, mu₂, mu₁]
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₆.mem.writeW (off I.B (slot I.W aM))
      (if decide (L = 0) then word s₆.mem I.B (slot I.W aM) ||| 1 else word s₆.mem I.B (slot I.W aM))) (by
        xrun [State.ea, at0, (ku₃.gpr (by decide)).trans hbx, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero, hs₃.ld (d := slot I.W aM) (by omega_arith), hs₃.st (d := slot I.W aM) (by omega_arith), h15, hmu]
        rw [or_and1_mask]) rfl)
      fun t ⟨hm, k⟩ => ⟨hm, (((ku₁.trans ku₂).trans ku₃).trans k).mono (by decide)⟩
  obtain o₇ := writeW_outside s₆.mem I.B (if decide (L = 0) then word s₆.mem I.B (slot I.W aM) ||| 1 else
    word s₆.mem I.B (slot I.W aM)) (d := slot I.W aM) (by omega_arith)
  rw [← m₇] at o₇
  obtain f₇ := KF.arr1 (I := I) (j := aM) o₇ (Nat.le_refl _) (by omega_arith)
  obtain h₇ := h₆.step f₇ (all_mut_arr (by decide)) k₇ (by decide)
  obtain vM₇ : av I s₇.mem aM = (if decide (L = 0) then 1 else L) := by
    rw [m₇, av_or1 hw1 (by omega_arith) (fun hc => by rw [vM₆]; simpa using hc), vM₆]
  generalize hM₁ : (if decide (L = 0) then 1 else L) = M₁ at vM₇
  obtain hM₁0 : 0 < M₁ := by
    rw [← hM₁]
    by_cases hL0 : L = 0
    · simp only [hL0, decide_true, ite_true]; decide
    · simp only [hL0, decide_false, Bool.false_eq_true, ite_false]; omega_arith
  -- `[aR] := e mod M₁`, `[aU] := [aR]`.
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aQt) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aQt) (a := aE) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₉ (iQ := aQt) (iR := aR) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₁₀ ⟨h₁₀, f₁₀, d₁₀⟩ =>
        WP.seq (WP.mono (zeroA_k h₁₀ (j := aU) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, z₁₁, _⟩ =>
          WP.mono (copyA_k h₁₁ (o := aU) (a := aR) (by decide) (by decide) (by decide))
            fun s₁₂ ⟨h₁₂, f₁₂, v₁₂, t₁₂, _⟩ => ?_))))
  obtain vM₉ : av I s₉.mem aM = M₁ := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, vM₇]
  obtain vQ₉ : av I s₉.mem aQt = e := by
    rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, vE₆]
  rw [vM₉, vQ₉] at d₁₀
  obtain hRlt : e % M₁ < M₁ := Nat.mod_lt _ hM₁0
  obtain hM₁W : M₁ < 2 ^ (64 * I.W) := by
    rw [← hM₁]
    by_cases hL0 : L = 0
    · simp only [hL0, decide_true, ite_true]; exact Nat.one_lt_two_pow (by omega_arith)
    · simp only [hL0, decide_false, Bool.false_eq_true, ite_false]; exact hLW
  obtain vR₁₀ : av I s₁₀.mem aR = e % M₁ := by
    rw [← (d₁₀ hM₁0).1]; exact wv_low_of_lt (by omega_arith) (by rw [(d₁₀ hM₁0).1]; omega_arith)
  obtain hok10 : [Rc.arr aQt, Rc.arr aR, Rc.arr aT].all Rc.ok = true := by decide
  obtain vU₁₂ : av I s₁₂.mem aU = e % M₁ := by rw [v₁₂, f₁₁.av (by decide) (by decide) (by decide) hZ, vR₁₀]
  obtain tU₁₂ : atop I s₁₂.mem aU = 0 := by rw [t₁₂]; exact (wv_zero2 z₁₁).2
  obtain vL₁₂ : av I s₁₂.mem aL = L := by
    rw [f₁₂.av (by decide) (by decide) (by decide) hZ, f₁₁.av (by decide) (by decide) (by decide) hZ,
      f₁₀.av hok10 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, vL₆]
  -- `kOk := ` the mask of `L` odd and at least 3.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₁₂ 3) fun s₁₃ ⟨h₁₃, f₁₃, c₁₃, _⟩ => ?_)
  obtain c3 : av I s₁₃.mem aC = 3 := av_of_full c₁₃ (two_le_pow h (by decide))
  obtain vL₁₃ : av I s₁₃.mem aL = L := by rw [f₁₃.av (by decide) (by decide) (by decide) hZ, vL₁₂]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₁₃ (a := aL) (b := aC) (by decide) (by decide))
    fun s₁₄ ⟨h₁₄, m₁₄, hbp₁₄, _, _, _, k₁₄⟩ => ?_)
  rw [vL₁₃, c3] at hbp₁₄
  generalize hok0 : (decide (L % 2 = 1) && !decide (L < 3)) = ok0
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  obtain hst := h₁₄.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (WP.keep [.rcx]
    (Q := fun t => t.gpr .rcx = mask (!decide (L < 3)) ∧ t.mem = s₁₄.mem) (by xrun [hbp₁₄, sxM1, maskNot]) rfl)
    fun s₁₅ ⟨⟨hcx₁₅, m₁₅⟩, k₁₅⟩ => ?_)))
  obtain h₁₅ := h₁₄.step (cs := []) (by rw [m₁₅]; exact KF.refl _ _ _) rfl k₁₅ (by decide)
  refine WP.mono (oddMask_k h₁₅ (j := aL) (by decide)) fun s₁₆ ⟨m₁₆, hax, _, _, k₁₆⟩ => ?_
  rw [m₁₅, m₁₄, vL₁₃] at hax
  obtain hcx₁₆ : s₁₆.gpr .rcx = mask (!decide (L < 3)) := by rw [k₁₆.gpr (by decide), hcx₁₅]
  obtain hdi₁₆ : s₁₆.gpr .rdi = I.B := ((k₁₅.trans k₁₆).gpr (by decide)).trans h₁₄.ws.rdi
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₁₆.mem.writeW (off I.B (8 * kOk)) (mask ok0) ∧
    t.gpr .rbp = mask ok0) (by
      obtain hst₁₆ := (h₁₄.ws.scr.congr (k₁₅.trans k₁₆).2.2).st (d := 8 * kOk)
        (by have := h.ws.h256; unfold kOk sFn; omega_arith)
      xrun [State.ea, hdr, hdi₁₆, hdrOff, hax, hcx₁₆, mask_and', hst₁₆]
      rw [hok0]; exact ⟨rfl, rfl⟩) rfl) fun s₁₇ ⟨⟨m₁₇, hbp₁₇⟩, k₁₇⟩ => ?_
  obtain h₁₆ := h₁₅.step (cs := []) (by rw [m₁₆]; exact KF.refl _ _ _) rfl k₁₆ (by decide)
  obtain ⟨h₁₇, f₁₇, ok₁₇⟩ := h₁₆.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) m₁₇ k₁₇ (by decide)
  obtain hm₁₆ : s₁₆.mem = s₁₃.mem := by rw [m₁₆, m₁₅, m₁₄]
  -- `[aM] := L`, then 3 unless `L` is odd and at least 3.
  refine WP.seq (WP.mono (zeroA_k h₁₇ (j := aM) (by decide)) fun s₁₈ ⟨h₁₈, f₁₈, _, k₁₈⟩ =>
    WP.mono (copyA_k h₁₈ (o := aM) (a := aL) (by decide) (by decide) (by decide)) fun s₁₉ ⟨h₁₉, f₁₉, v₁₉, _, k₁₉⟩ => ?_)
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  obtain vL₁₇ : av I s₁₇.mem aL = L := by rw [f₁₇.av hokO (by decide) (by decide) hZ, hm₁₆, vL₁₃]
  obtain vC₁₉ : av I s₁₉.mem aC = 3 := by
    rw [f₁₉.av (by decide) (by decide) (by decide) hZ, f₁₈.av (by decide) (by decide) (by decide) hZ,
      f₁₇.av hokO (by decide) (by decide) hZ, hm₁₆, c3]
  rw [f₁₈.av (by decide) (by decide) (by decide) hZ, vL₁₇] at v₁₉
  refine wp_seqs_append (by simp [selC]) (by simp) (WP.mono (selC_k h₁₉ (j := aM) (by decide) (by decide)
    (c := ok0) (by rw [k₁₉.gpr (by decide), k₁₈.gpr (by decide), hbp₁₇])) fun s₂₀ ⟨h₂₀, f₂₀, v₂₀, _, _⟩ => ?_)
  rw [v₁₉, vC₁₉] at v₂₀
  generalize hM : (if ok0 = true then L else 3) = M at v₂₀
  obtain hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]; cases ok0
    · simp
    · simp only [ite_true]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hok0
      omega_using [hok0]
  -- The inverse modulo `M`.
  obtain hokM : [Rc.arr aM].all Rc.ok = true := by decide
  obtain presU : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
      av I m' aU = av I m aU ∧ atop I m' aU = atop I m aU := fun f ok hn =>
    ⟨f.av ok (by decide) hn hZ, f.at ok (by decide) hn hZ⟩
  obtain pU : av I s₂₀.mem aU = e % M₁ := by
    obtain ⟨a2, _⟩ := presU f₂₀ hokM (by decide)
    obtain ⟨a3, _⟩ := presU f₁₉ (by decide) (by decide)
    obtain ⟨a4, _⟩ := presU f₁₈ (by decide) (by decide)
    obtain ⟨a5, _⟩ := presU f₁₇ hokO (by decide)
    obtain ⟨a6, _⟩ := presU f₁₃ (by decide) (by decide)
    rw [hm₁₆] at a5
    rw [a2, a3, a4, a5, a6, vU₁₂]
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  refine WP.mono (inverse_k h₂₀ (iU := aU) (iV := aV) (iX₂ := aX₂) (iM := aM) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₂₂ ⟨h₂₂, f₂₂, _, hinv⟩ => ?_
  rw [v₂₀, pU] at hinv
  obtain ⟨hg₂₂, hdv₂₂, hx₂₂⟩ := hinv hMo.1
  generalize hx : av I s₂₂.mem aX₂ = x at hdv₂₂ hx₂₂
  -- `kOk &= ` the mask of the gcd being 1.
  obtain hokI : [Rc.arr aV, Rc.arr aX₂, Rc.priv].all Rc.ok = true := by decide
  obtain ok₂₂ : word s₂₂.mem I.B (8 * kOk) = mask ok0 := by
    rw [f₂₂.word hokI (by decide) (by decide),
      f₂₀.word hokM (by decide) (by decide), f₁₉.word (by decide) (by decide) (by decide),
      f₁₈.word (by decide) (by decide) (by decide), ok₁₇]
  refine wp_seqs_append (by simp [gcdIsOne, constA]) (by simp) (WP.mono (gcdIsOne_k h₂₂ ok₂₂)
    fun s₂₃ ⟨h₂₃, f₂₃, ok₂₃⟩ => ?_)
  rw [hg₂₂] at ok₂₃
  -- `[aDd] := x`.
  refine WP.mono (zc_k h₂₃ (o := aDd) (a := aX₂) (by decide) (by decide) (by decide)) fun t ⟨ht, f₂₄, vD, _⟩ => ?_
  obtain okt : word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd (e % M₁) M = 1) && ok0) := by
    rw [f₂₄.word (by decide) (by decide) (by decide), ok₂₃]
  obtain vDt : av I t.mem aDd = x := by
    rw [vD, f₂₃.av (by decide) (by decide) (by decide) hZ, hx]
  obtain f₁₄₁₆ : KF I.B I.W [] s₁₃.mem s₁₆.mem := by rw [hm₁₆]; exact KF.refl _ _ _
  refine ⟨ht, ?_, ⟨_, okt, ?_, ?_⟩⟩
  · have f₆' : KF I.B I.W [.arr aC] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
    exact ((((((((((((((((((f₁.trans f₂).trans f₃).trans f₆').trans f₇).trans f₈).trans
      f₉).trans f₁₀).trans f₁₁).trans f₁₂).trans f₁₃).trans f₁₄₁₆).trans f₁₇).trans f₁₈).trans f₁₉).trans f₂₀).trans
      f₂₂).trans f₂₃).trans f₂₄).mono (by decide)
  · -- The inverse exists iff `L` is odd, at least 3, and the gcd is 1.
    constructor
    · rintro ⟨d, hd⟩
      by_contra hc
      have : ¬ (L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1) := fun ⟨h1, h2, h3⟩ => by
        obtain hok : ok0 = true := by rw [← hok0]; simp [h1]; omega_using [h2]
        obtain hMe : M = L := by rw [← hM, hok]; rfl
        obtain hM₁e : M₁ = L := by rw [← hM₁]; simp; omega_using [h2]
        exact hc (by rw [hok, hMe, hM₁e]; simp [h3])
      rw [inverse_even_none hee this] at hd
      cases hd
    · intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain hMe : M = L := by rw [← hM, hc.2]; rfl
      obtain hL3 : 3 ≤ L ∧ L % 2 = 1 := by
        have := hc.2; rw [← hok0] at this
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
        omega_using [this]
      obtain hM₁e : M₁ = L := by rw [← hM₁]; simp; omega_using [hL3]
      have hg1 := hc.1
      rw [hMe, hM₁e] at hg1
      rw [hg₂₂, hMe, hM₁e, hg1] at hdv₂₂
      rw [hMe] at hx₂₂
      exact ⟨x, inverse_even hL3.1 (by exact_mod_cast hdv₂₂) hx₂₂⟩
  · intro d hd
    by_cases hc : L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1
    · have hok : ok0 = true := by rw [← hok0]; simp [hc.1]; omega_using [hc.2.1]
      obtain hMe : M = L := by rw [← hM, hok]; rfl
      obtain hM₁e : M₁ = L := by rw [← hM₁]; simp; omega_using [hc.2.1]
      rw [hg₂₂, hMe, hM₁e, hc.2.2] at hdv₂₂
      rw [hMe] at hx₂₂
      rw [inverse_even hc.2.1 (by exact_mod_cast hdv₂₂) hx₂₂] at hd
      cases hd
      exact vDt
    · rw [inverse_even_none hee hc] at hd
      cases hd

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## DPart -/
section

/-!
# An RSA key from its primes on x86-64: `d = e⁻¹ mod L`

`dPart`, by `e`: none for 0, 1 for 1 but `L = 1`, `dOdd` for an odd `e`
and `dEven` for an even one (`dPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `e = 1`: `d = 1`, `kOk` the mask of `L ≠ 1`. -/
theorem dOne_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {L : Nat} (hL : av I s.mem aL = L) :
    WP isa (seqs dOne) s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I 1 L t.mem := by
  have hZ := h.hZ
  unfold dOne
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  obtain c1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
  obtain vL : av I s₁.mem aL = L := by rw [f₁.av (by decide) (by decide) (by decide) hZ, hL]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₁ (a := aL) (b := aC) (by decide)
    (by decide)) fun s₂ ⟨h₂, m₂, hbp, _⟩ => ?_)
  rw [vL, c1] at hbp
  simp only [seqs]
  obtain hst := h₂.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.mem = s₂.mem.writeW (off I.B (8 * kOk))
    (mask (!decide (L = 1)))) (by xrun [State.ea, hdr, h₂.ws.rdi, hdrOff, hst, hbp, sxM1, maskNot]) rfl)
    fun s₃ ⟨m₃, k₃⟩ => ?_)
  obtain ⟨h₃, f₃, ok₃⟩ := h₂.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) m₃ k₃ (by decide)
  refine WP.seq (WP.mono (zeroA_k h₃ (j := aDd) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _⟩ =>
    WP.mono (setOne_k h₄ (j := aDd) (by decide) z₄) fun t ⟨ht, f₅, o₅, _⟩ => ?_)
  refine ⟨ht, (((f₁.trans (by rw [← m₂]; exact f₃)).trans f₄).trans f₅).mono (by simp),
    ⟨!decide (L = 1), ?_, ?_, ?_⟩⟩
  · rw [f₅.word (by decide) (by decide) (by decide), f₄.word (by decide) (by decide) (by decide), ok₃]
  · rw [VG.Proof.RsaKeyGen.inverse_one]
    by_cases h1 : L = 1 <;> simp [h1]
  · intro d hd
    rw [VG.Proof.RsaKeyGen.inverse_one] at hd
    by_cases h1 : L = 1
    · simp [h1] at hd
    · simp only [h1, ite_false, Option.some.injEq] at hd
      subst hd
      exact av_of_full o₅ (two_le_pow h (by decide))

/-- `dPart`, for `e < 2⁶⁴`. -/
theorem dPart_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {e L : Nat} (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hL : av I s.mem aL = L) (hLW : L < 2 ^ (64 * I.W)) :
    WP isa dPart s fun t => KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := by
  obtain hld := h.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith)
  unfold dPart
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (e < 1)) ∧ t.zf = some (decide (e = 1)) ∧
    t.mem = s.mem) (by
      xrun [State.ea, hdr, h.ws.rdi, hdrOff, hld, hev, sx1]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        ofNat_sub_beq he64 (by decide)]
      exact ⟨rfl, rfl⟩) rfl) fun s₁ ⟨⟨hcf, hzf, m₁⟩, k₁⟩ => ?_)
  obtain h₁ := h.step (cs := []) (by rw [m₁]; exact KF.refl _ _ _) rfl k₁ (by decide)
  obtain hev₁ : word s₁.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₁, hev]
  obtain hL₁ : av I s₁.mem aL = L := by rw [show av I s₁.mem aL = av I s.mem aL by rw [m₁], hL]
  obtain post : ∀ t, KS I m₀ t ∧ KF I.B I.W csD s₁.mem t.mem ∧ DRes I e L t.mem →
      KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := fun t ⟨a, b, c⟩ => ⟨a, by rw [← m₁]; exact b, c⟩
  refine WP.ite (decide (e < 1)) (by simp [eval, hcf]) (fun he0 => ?_) (fun he0 => ?_)
  · -- `e = 0`: no inverse.
    simp only [decide_eq_true_eq] at he0
    obtain hst := h₁.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (8 * kOk)) (mask false)) (by
      unfold dZero
      xrun [State.ea, hdr, h₁.ws.rdi, hdrOff, hst]
      rfl) rfl) fun t ⟨m, k⟩ => post t ?_
    obtain ⟨ht, ft, okt⟩ := h₁.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) m k (by decide)
    refine ⟨ht, ft.mono (by simp), false, okt, ?_, fun d hd => ?_⟩
    · rw [show e = 0 by omega_arith, VG.Proof.RsaKeyGen.inverse_zero]; simp
    · rw [show e = 0 by omega_arith, VG.Proof.RsaKeyGen.inverse_zero] at hd; cases hd
  simp only [decide_eq_false_iff_not] at he0
  refine WP.ite (decide (e = 1)) (by simp [eval, hzf]) (fun he1 => ?_) (fun he1 => ?_)
  · simp only [decide_eq_true_eq] at he1
    subst he1
    exact WP.mono (dOne_k h₁ hL₁) post
  simp only [decide_eq_false_iff_not] at he1
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (e % 2 = 0)) ∧ t.mem = s₁.mem) (by
      obtain hld₁ := h₁.ws.scr.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_arith)
      xrun [State.ea, hdr, h₁.ws.rdi, hdrOff, hld₁, hev₁, sx1]
      rw [and1_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      rcases Nat.mod_two_eq_zero_or_one e with h2 | h2 <;> rw [h2] <;> decide) rfl) fun s₂ ⟨⟨hzf₂, m₂⟩, k₂⟩ => ?_)
  obtain h₂ := h₁.step (cs := []) (by rw [m₂]; exact KF.refl _ _ _) rfl k₂ (by decide)
  obtain post₂ : ∀ t, KS I m₀ t ∧ KF I.B I.W csD s₂.mem t.mem ∧ DRes I e L t.mem →
      KS I m₀ t ∧ KF I.B I.W csD s.mem t.mem ∧ DRes I e L t.mem := fun t ⟨a, b, c⟩ =>
    ⟨a, by rw [← m₁, ← m₂]; exact b, c⟩
  obtain hev₂ : word s₂.mem I.B (8 * kEv) = BitVec.ofNat 64 e := by rw [m₂, hev₁]
  obtain hL₂ : av I s₂.mem aL = L := by rw [show av I s₂.mem aL = av I s₁.mem aL by rw [m₂], hL₁]
  refine WP.ite (decide (e % 2 = 1)) (by
    simp only [eval, hzf₂, Option.map_some, Option.some.injEq]
    rcases Nat.mod_two_eq_zero_or_one e with h2 | h2 <;> simp [h2]) (fun ho => ?_) (fun ho => ?_)
  · simp only [decide_eq_true_eq] at ho
    exact WP.mono (dOdd_k h₂ (by omega_arith) he64 ho hev₂ hL₂ hLW) post₂
  · simp only [decide_eq_false_iff_not] at ho
    exact WP.mono (dEven_k h₂ he64 (by omega_arith) hev₂ hL₂ hLW) post₂

end VG.Proof.RsaKeyGen.X86_64.Key

end
