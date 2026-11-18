module

public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Front
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Halve
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Minv

/-! ### `RsaKeyGen.X86_64.Key.Crt`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Key.DPart`, which this module and modules that import it used -/

section

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

end

end

/-! ## Small -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: `d` too small

`smallMask`: ZF clear exactly when `d` exists and `d ≤ 2^(64 w)`
(`smallMask_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- Word `k` of a number written, from zero. -/
theorem wv_set {m : Mem} {B : Addr} {d N k : Nat} (v : BitVec 64) (hz : word m B (d + 8 * k) = 0)
    (hd : d + 8 * N ≤ 2 ^ 64) (hk : k < N) : ∀ n ≤ N,
    wv (m.writeW (off B (d + 8 * k)) v) B d n = wv m B d n + (if k < n then 2 ^ (64 * k) * v.toNat else 0)
  | 0, _ => by simp [wv]
  | n + 1, hn => by
    rw [wv, wv, wv_set v hz hd hk n (by omega_arith)]
    by_cases hkn : n = k
    · subst hkn; rw [word_writeW_self, hz]; simp
    · rw [(writeW_outside m B v (d := d + 8 * k) (by omega_arith)).word (by omega_arith) (by omega_arith)]
      by_cases hk' : k < n
      · simp [hk', show k < n + 1 by omega_arith]; omega_arith
      · simp [hk', show ¬ k < n + 1 by omega_arith]

/-- `smallMask`: ZF clear iff `kOk` and `[aDd] ≤ 2^(64 w)`, for `W = 2 w`. -/
theorem smallMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (seqs smallMask) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧
      t.zf = some (!(decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  obtain hw1 : 1 ≤ w := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  obtain sC := h.ws.sl (j := aC) (by decide)
  unfold smallMask
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h 1) fun s₁ ⟨h₁, f₁, c₁, _⟩ => ?_)
  -- Word `w` of `[aC]` set: `[aC] = 2^(64 w) + 1`.
  refine wp_seqs_append (by simp) (by simp [ltA]) ?_
  simp only [seqs]
  refine WP.mono (Q := fun (t : State) => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w)) (1 : BitVec 64) ∧
    Keep [.r12, .r9, .rbx, .rax, .rdx] s₁ t) ?_ fun (s₂ : State) ⟨m₂, k₂⟩ => ?_
  · rw [WP.block_append_iff]
    refine WP.mono h₁.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aC (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h₁.ws.rdi) h9)
      fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
    obtain hs₂ := h₁.ws.scr.congr (ku₁.trans ku₂).2.2
    obtain h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s₁.mem.writeW (off I.B (slot I.W aC + 8 * w)) (1 : BitVec 64)) (by
      obtain ew : BitVec.ofNat 64 I.W >>> 1 = BitVec.ofNat 64 w := by
        rw [ofNat_shr1 (by omega_arith)]; congr 1; omega_arith
      xrun [State.ea, ix, h12₂, ew, addr0 hbx rfl, hs₂.st (d := slot I.W aC + 8 * w) (by omega_arith), mu₂, mu₁]
      rfl) rfl) fun t ⟨hm, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by decide)⟩
  obtain o₂ := writeW_outside s₁.mem I.B (1 : BitVec 64) (d := slot I.W aC + 8 * w) (by omega_arith)
  rw [← m₂] at o₂
  obtain f₂ := KF.arr1 (I := I) (j := aC) o₂ (by omega_arith) (by omega_arith)
  obtain h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂ (by decide)
  obtain c₂ : av I s₂.mem aC = 2 ^ (64 * w) + 1 := by
    obtain hz : word s₁.mem I.B (slot I.W aC + 8 * w) = 0 := by
      obtain e := VG.Proof.Rsa.X86_64.wv_low (m := s₁.mem) (B := I.B) (e := slot I.W aC) (w := I.W + 2) (by omega_arith)
      rw [c₁] at e
      obtain h0 : wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (wv s₁.mem I.B (slot I.W aC + 8) (I.W + 2 - 1)) with h0 | h0
        · exact h0
        · have := Nat.le_mul_of_pos_right (2 ^ 64) h0
          simp only [show (1 : BitVec 32).toNat = 1 from rfl] at e; omega_arith
      have := (wv_eq_zero_iff _ _ _ _).mp h0 (w - 1) (by omega_arith)
      rwa [show slot I.W aC + 8 + 8 * (w - 1) = slot I.W aC + 8 * w by omega_arith] at this
    obtain hv1 : av I s₁.mem aC = 1 := av_of_full c₁ (two_le_pow h (by decide))
    dsimp only [av] at hv1 ⊢
    rw [m₂, wv_set (1 : BitVec 64) hz (by omega_arith) (by omega_arith) I.W (Nat.le_refl _), hv1, ite_eq_left (by omega_arith)]
    simp; omega_arith
  obtain vD : av I s₂.mem aDd = av I s.mem aDd := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₂ (a := aDd) (b := aC) (by decide) (by decide))
    fun s₃ ⟨h₃, m₃, hbp, _, _, _, k₃⟩ => ?_)
  rw [vD, c₂] at hbp
  simp only [seqs]
  obtain hok₃ : word s₃.mem I.B (8 * kOk) = mask ok := by
    rw [m₃, f₂.word (by decide) (by decide) (by decide), f₁.word (by decide) (by decide) (by decide), hok]
  obtain hld := h₃.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.zf = some (!(decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok)) ∧
    t.mem = s₃.mem) (by
      xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hld, hbp, hok₃, mask_and']
      obtain hd : decide (av I s.mem aDd < 2 ^ (64 * w) + 1) = decide (av I s.mem aDd ≤ 2 ^ (64 * w)) :=
        decide_eq_decide.mpr Nat.lt_succ_iff
      rw [Bool.and_self, hd]
      cases (decide (av I s.mem aDd ≤ 2 ^ (64 * w)) && ok) <;> decide) rfl) fun t ⟨⟨hz, m⟩, k⟩ => by
    obtain f₂' : KF I.B I.W [.arr aC] s₁.mem t.mem := by rw [m, m₃]; exact f₂
    exact ⟨h₃.step (cs := []) (by rw [m]; exact KF.refl _ _ _) rfl k (by decide), (f₁.trans f₂').mono (by decide), hz⟩

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Qinv -/
section

/-!
# An RSA key from its primes on x86-64: `qInv`

`qinvPart`: the inverse of `q` modulo `M = p` (3 unless `p` is odd and at
least 3) into `aX₂`, and `kOk &= ` the mask of `gcd(q, M) = 1`
(`qinvPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem qinvPart_eq : qinvPart = [zeroA aU, copyA aU aQa] ++ (constA 3 ++ (ltA aPa aC ++
    (([.block (([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] : List Instr) ++ oddMask aPa ++
        ([.alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)] : List Instr)), zeroA aM, copyA aM aPa] : List (Prog isa)) ++
    (selC aM ++ ([inverseK kHalf aU aV aX₂ aM] ++ gcdIsOne))))) := by
  simp only [qinvPart, gcdIsOne, List.append_assoc]

/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
abbrev qMod (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

/-- The parts `qinvPart` changes. -/
abbrev csQ : List Rc :=
  [.arr aU, .arr aC, .arr aM, .arr aV, .arr aX₁, .arr aX₂, .arr aT, .hdr sMo, .hdr kOk, .priv]

/-- `qinvPart`, for `[aPa] = P` and `[aQa] = Q`. -/
theorem qinvPart_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {P Q : Nat} {ok : Bool}
    (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (hok : word s.mem I.B (8 * kOk) = mask ok)
    (hw : 1 ≤ I.W / 2) (hPb : P < 2 ^ (64 * (I.W / 2))) (hQb : Q < 2 ^ (64 * (I.W / 2))) :
    WP isa (seqs qinvPart) s fun t => KS I m₀ t ∧ KF I.B I.W csQ s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (decide (Nat.gcd Q (qMod P) = 1) && ok) ∧
      ((qMod P : Nat) : Int) ∣ (av I t.mem aX₂ : Int) * Q - Nat.gcd Q (qMod P) ∧ av I t.mem aX₂ < qMod P := by
  have hZ := h.hZ
  rw [qinvPart_eq]
  -- `[aU] := q`.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aU) (a := aQa) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  rw [hQ] at v₁
  refine wp_seqs_append (by simp [constA]) (by simp [ltA]) (WP.mono (constA_k h₁ 3) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  obtain c3 : av I s₂.mem aC = 3 := av_of_full c₂ (two_le_pow h (by decide))
  obtain vP₂ : av I s₂.mem aPa = P := by
    rw [f₂.av (by decide) (by decide) (by decide) hZ, f₁.av (by decide) (by decide) (by decide) hZ, hP]
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h₂ (a := aPa) (b := aC) (by decide) (by decide))
    fun s₃ ⟨h₃, m₃, hbp₃, _, _, _, k₃⟩ => ?_)
  rw [vP₂, c3] at hbp₃
  generalize hpv : (decide (P % 2 = 1) && !decide (P < 3)) = pv
  -- `rbp := ` the mask of `p` odd and at least 3; `[aM] := p`.
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (WP.keep [.rcx]
    (Q := fun t => t.gpr .rcx = mask (!decide (P < 3)) ∧ t.mem = s₃.mem) (by xrun [hbp₃, sxM1, maskNot]) rfl)
    fun s₄ ⟨⟨hcx₄, m₄⟩, k₄⟩ => ?_)))
  obtain h₄ := h₃.step (cs := []) (by rw [m₄]; exact KF.refl _ _ _) rfl k₄ (by decide)
  refine WP.mono (oddMask_k h₄ (j := aPa) (by decide)) fun s₅ ⟨m₅, hax, _, _, k₅⟩ => ?_
  rw [m₄, m₃, vP₂] at hax
  obtain hcx₅ : s₅.gpr .rcx = mask (!decide (P < 3)) := by rw [k₅.gpr (by decide), hcx₄]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rbp = mask pv ∧ t.mem = s₅.mem) (by
    xrun [hax, hcx₅, mask_and']; rw [hpv]) rfl) fun s₆ ⟨⟨hbp₆, m₆⟩, k₆⟩ => ?_
  obtain h₆ := h₄.step (cs := []) (by rw [m₆, m₅]; exact KF.refl _ _ _) rfl (k₅.trans k₆) (by decide)
  obtain hm₆ : s₆.mem = s₂.mem := by rw [m₆, m₅, m₄, m₃]
  refine WP.seq (WP.mono (zeroA_k h₆ (j := aM) (by decide)) fun s₇ ⟨h₇, f₇, _, k₇⟩ =>
    WP.mono (copyA_k h₇ (o := aM) (a := aPa) (by decide) (by decide) (by decide)) fun s₈ ⟨h₈, f₈, v₈, _, k₈⟩ => ?_)
  obtain vP₆ : av I s₆.mem aPa = P := by rw [hm₆, vP₂]
  rw [f₇.av (by decide) (by decide) (by decide) hZ, vP₆] at v₈
  obtain vC₈ : av I s₈.mem aC = 3 := by
    rw [f₈.av (by decide) (by decide) (by decide) hZ, f₇.av (by decide) (by decide) (by decide) hZ, hm₆, c3]
  -- `[aM] := M`.
  refine wp_seqs_append (by simp [selC]) (by simp) (WP.mono (selC_k h₈ (j := aM) (by decide) (by decide)
    (c := pv) (by rw [k₈.gpr (by decide), k₇.gpr (by decide), hbp₆])) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ => ?_)
  rw [v₈, vC₈] at v₉
  obtain hM : (if pv = true then P else 3) = qMod P := by rw [← hpv]
  rw [hM] at v₉
  obtain hMo : qMod P % 2 = 1 ∧ 1 < qMod P := by
    unfold qMod
    by_cases hc : (decide (P % 2 = 1) && !decide (P < 3)) = true
    · rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hc
      omega_arith
    · rw [ite_eq_right hc]; decide
  -- The inverse.
  obtain pU : av I s₉.mem aU = Q := by
    obtain hK : ∀ {m m' : Mem} {cs : List Rc}, KF I.B I.W cs m m' → cs.all Rc.ok = true → .arr aU ∉ cs →
        av I m' aU = av I m aU := fun f ok hn => f.av ok (by decide) hn hZ
    rw [hK f₉ (by decide) (by decide), hK f₈ (by decide) (by decide), hK f₇ (by decide) (by decide), hm₆,
      hK f₂ (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp) (by simp [gcdIsOne, constA]) ?_
  simp only [seqs]
  obtain hMb : qMod P < 2 ^ (64 * (I.W / 2)) := by
    unfold qMod; split
    · exact hPb
    · exact Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 64) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine WP.mono (inverseK_k h₉ (k := kHalf) (n := I.W / 2) (fun _ h12 _ => kHalf_ok h12 (by omega_arith)) hw
    (by omega_arith) (iU := aU) (iV := aV) (iX₂ := aX₂) (iM := aM) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, _, hinv⟩ => ?_
  rw [v₉, pU] at hinv
  obtain ⟨hg₁₁, hdv₁₁, hx₁₁⟩ := hinv hQb hMb hMo.1
  obtain hokI : [Rc.arr aV, Rc.arr aX₂, Rc.priv].all Rc.ok = true := by decide
  obtain ok₁₁ : word s₁₁.mem I.B (8 * kOk) = mask ok := by
    rw [f₁₁.word hokI (by decide) (by decide),
      f₉.word (by decide) (by decide) (by decide), f₈.word (by decide) (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), hm₆, f₂.word (by decide) (by decide) (by decide),
      f₁.word (by decide) (by decide) (by decide), hok]
  refine WP.mono (gcdIsOne_k h₁₁ ok₁₁) fun t ⟨ht, f₁₂, ok₁₂⟩ => ?_
  rw [hg₁₁] at ok₁₂ hdv₁₁
  obtain vX : av I t.mem aX₂ = av I s₁₁.mem aX₂ := f₁₂.av (by decide) (by decide) (by decide) hZ
  obtain f₂₆ : KF I.B I.W [.arr aC] s₁.mem s₆.mem := by rw [hm₆]; exact f₂
  refine ⟨ht, ?_, ok₁₂, by rw [vX]; exact hdv₁₁, by rw [vX]; exact hx₁₁⟩
  exact (((((((f₁.trans f₂₆).trans f₇).trans f₈).trans f₉).trans f₁₁).trans f₁₂)).mono (by decide)

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Crt -/
section

/-!
# An RSA key from its primes on x86-64: `dP` and `dQ`

`divisorOf j`: `[aM] := [j]`, or 1 for 0 (`divisorOf_k`); `crtPart`:
`dP = d mod (p − 1)` into `aX₁` and `dQ = d mod (q − 1)` into `aV`
(`crtPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A divisor: `x`, or 1 for 0. -/
abbrev dv (x : Nat) : Nat := if x = 0 then 1 else x

theorem divisorOf_eq (j : Nat) : divisorOf j = [zeroA aM, copyA aM j] ++ (constA 0 ++ (eqMask j aC ++
    ([.block (ws ++ base aM .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rbp (.imm 1), .alu .or .rax (.reg .rbp),
      .store (at0 .rbx) .rax] : List Instr))] : List (Prog isa)))) := by
  simp only [divisorOf, List.append_assoc]

/-- `divisorOf j`. -/
theorem divisorOf_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j : Nat} (hj : j < 16) (hjM : j ≠ aM)
    (hjC : j ≠ aC) :
    WP isa (seqs (divisorOf j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aM, .arr aC] s.mem t.mem ∧
      av I t.mem aM = dv (av I s.mem j) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  obtain sM := h.ws.sl (j := aM) (by decide)
  rw [divisorOf_eq]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h (o := aM) (a := j) (by decide) hj hjM.symm)
    fun s₁ ⟨h₁, f₁, v₁, _⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₁ 0) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  obtain c0 : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  obtain vj : av I s₂.mem j = av I s.mem j := by
    rw [f₂.av (by decide) hj (by simp [hjC]) hZ, f₁.av (by decide) hj (by simp [hjM]) hZ]
  obtain vM₂ : av I s₂.mem aM = av I s.mem j := by rw [f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₂ (a := j) (b := aC) hj (by decide))
    fun s₃ ⟨h₃, m₃, hbp₃, _⟩ => ?_)
  rw [vj, c0] at hbp₃
  simp only [seqs]
  refine WP.mono (Q := fun (t : State) => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM)) ∧
      Keep [.r12, .r9, .rbx, .rax, .rbp] s₃ t) ?_ fun (t : State) ⟨m₄, k₄⟩ => ?_
  · rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono h₃.ws.ws_ok fun u₁ ⟨_, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aM (r := .rbx) (by decide) ((ku₁.gpr (by decide)).trans h₃.ws.rdi) h9)
      fun u₂ ⟨hbx, mu₂, ku₂⟩ => ?_
    obtain hs₂ := h₃.ws.scr.congr (ku₁.trans ku₂).2.2
    obtain hbp : u₂.gpr .rbp = mask (decide (av I s.mem j = 0)) := by rw [(ku₁.trans ku₂).gpr (by decide), hbp₃]
    obtain hmu : u₂.mem = s₃.mem := by rw [mu₂, mu₁]
    refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (slot I.W aM))
      (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else word s₃.mem I.B (slot I.W aM))) (by
        xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs₂.ld (d := slot I.W aM) (by omega_arith), hs₂.st (d := slot I.W aM) (by omega_arith), hbp, hmu]
        rw [or_and1_mask]) rfl) fun t ⟨hm, k⟩ => ⟨hm, ((ku₁.trans ku₂).trans k).mono (by decide)⟩
  obtain o₄ := writeW_outside s₃.mem I.B (if decide (av I s.mem j = 0) then word s₃.mem I.B (slot I.W aM) ||| 1 else
    word s₃.mem I.B (slot I.W aM)) (d := slot I.W aM) (by omega_arith)
  rw [← m₄] at o₄
  obtain f₄ := KF.arr1 (I := I) (j := aM) o₄ (Nat.le_refl _) (by omega_arith)
  refine ⟨h₃.step f₄ (all_mut_arr (by decide)) k₄ (by decide), ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono
    (by simp), ?_⟩
  obtain vM₃ : av I s₃.mem aM = av I s.mem j := by rw [m₃, vM₂]
  rw [m₄, av_or1 hw1 (by omega_arith) (fun hc => by rw [vM₃]; simpa using hc), vM₃]
  by_cases hz : av I s.mem j = 0 <;> simp [hz, dv]

/-- The parts `crtPart` changes. -/
abbrev csC : List Rc := [.arr aM, .arr aC, .arr aU, .arr aV, .arr aT, .arr aX₁]

/-- `crtPart`: `[aX₁] := d mod dv(P − 1)`, `[aV] := d mod dv(Q − 1)`, for `[aDd] = d`,
`[aPm] = P − 1` and `[aQm] = Q − 1`. -/
theorem crtPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {d a b : Nat} (hd : av I s.mem aDd = d)
    (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) :
    WP isa (seqs crtPart) s fun t => KS I m₀ t ∧ KF I.B I.W csC s.mem t.mem ∧
      av I t.mem aX₁ = d % dv a ∧ av I t.mem aV = d % dv b := by
  have hZ := h.hZ
  obtain hdv : ∀ x, 0 < dv x := fun x => by unfold dv; split <;> omega_arith
  obtain hdW : ∀ {x}, x < 2 ^ (64 * I.W) → dv x < 2 ^ (64 * I.W) := fun hx => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := h.ws.w1; omega_arith)
    · exact hx
  unfold crtPart
  simp only [List.append_assoc]
  -- `dP`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h (j := aPm) (by decide) (by decide)
    (by decide)) fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  rw [ha] at v₁
  obtain hok1 : [Rc.arr aM, Rc.arr aC].all Rc.ok = true := by decide
  obtain vD₁ : av I s₁.mem aDd = d := by rw [f₁.av hok1 (by decide) (by decide) hZ, hd]
  refine wp_seqs_append (by simp) (by simp [divisorOf]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, _, _⟩ =>
      WP.seq (WP.mono (divmod_k h₃ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, d₄⟩ =>
        WP.seq (WP.mono (zeroA_k h₄ (j := aX₁) (by decide)) fun s₅ ⟨h₅, f₅, _, _⟩ =>
          WP.mono (copyA_k h₅ (o := aX₁) (a := aV) (by decide) (by decide) (by decide))
            fun s₆ ⟨h₆, f₆, v₆, _, _⟩ => ?_))))
  obtain vM₃ : av I s₃.mem aM = dv a := by
    rw [f₃.av (by decide) (by decide) (by decide) hZ, f₂.av (by decide) (by decide) (by decide) hZ, v₁]
  obtain vU₃ : av I s₃.mem aU = d := by rw [v₃, f₂.av (by decide) (by decide) (by decide) hZ, vD₁]
  rw [vM₃, vU₃] at d₄
  obtain hR := (d₄ (hdv a)).1
  obtain hlt : d % dv a < dv a := Nat.mod_lt _ (hdv a)
  obtain vM₁W : dv a < 2 ^ (64 * I.W) := by rw [← v₁]; exact wv_lt _ _ _ _
  obtain vX₆ : av I s₆.mem aX₁ = d % dv a := by
    rw [v₆, f₅.av (by decide) (by decide) (by decide) hZ, ← hR]
    exact wv_low_of_lt (by omega_arith) (by rw [hR]; omega_arith)
  obtain hok4 : [Rc.arr aU, Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  obtain pres6 : ∀ j, j < 16 → j ≠ aU → j ≠ aV → j ≠ aT → j ≠ aX₁ → av I s₆.mem j = av I s₁.mem j :=
    fun j hj h1 h2 h3 h4 => by
      rw [f₆.av (by decide) hj (by simp [h4]) hZ, f₅.av (by decide) hj (by simp [h4]) hZ,
        f₄.av hok4 hj (by simp [h1, h2, h3]) hZ, f₃.av (by decide) hj (by simp [h1]) hZ,
        f₂.av (by decide) hj (by simp [h1]) hZ]
  obtain vQm₆ : av I s₆.mem aQm = b := by
    rw [pres6 aQm (by decide) (by decide) (by decide) (by decide) (by decide), f₁.av hok1 (by decide) (by decide) hZ, hb]
  obtain vD₆ : av I s₆.mem aDd = d := by
    rw [pres6 aDd (by decide) (by decide) (by decide) (by decide) (by decide), vD₁]
  -- `dQ`.
  refine wp_seqs_append (by simp [divisorOf]) (by simp) (WP.mono (divisorOf_k h₆ (j := aQm) (by decide) (by decide)
    (by decide)) fun s₇ ⟨h₇, f₇, v₇⟩ => ?_)
  rw [vQm₆] at v₇
  obtain vD₇ : av I s₇.mem aDd = d := by rw [f₇.av hok1 (by decide) (by decide) hZ, vD₆]
  obtain vX₇ : av I s₇.mem aX₁ = d % dv a := by rw [f₇.av hok1 (by decide) (by decide) hZ, vX₆]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aU) (by decide)) fun s₈ ⟨h₈, f₈, _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₈ (o := aU) (a := aDd) (by decide) (by decide) (by decide)) fun s₉ ⟨h₉, f₉, v₉, _, _⟩ =>
      WP.mono (divmod_k h₉ (iQ := aU) (iR := aV) (iD := aM) (iT := aT) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, f₁₀, d₁₀⟩ => ?_))
  obtain vM₉ : av I s₉.mem aM = dv b := by
    rw [f₉.av (by decide) (by decide) (by decide) hZ, f₈.av (by decide) (by decide) (by decide) hZ, v₇]
  obtain vU₉ : av I s₉.mem aU = d := by rw [v₉, f₈.av (by decide) (by decide) (by decide) hZ, vD₇]
  rw [vM₉, vU₉] at d₁₀
  obtain hR' := (d₁₀ (hdv b)).1
  obtain vMb : dv b < 2 ^ (64 * I.W) := by rw [← v₇]; exact wv_lt _ _ _ _
  refine ⟨ht, ?_, ?_, ?_⟩
  · exact (((((((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇).trans f₈).trans f₉).trans
      f₁₀).mono (by decide)
  · rw [f₁₀.av hok4 (by decide) (by decide) hZ, f₉.av (by decide) (by decide) (by decide) hZ,
      f₈.av (by decide) (by decide) (by decide) hZ, vX₇]
  · rw [← hR']
    exact wv_low_of_lt (by omega_arith) (by rw [hR']; exact Nat.lt_trans (Nat.mod_lt _ (hdv b)) vMb)

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

end

/-! ### `RsaKeyGen.X86_64.Key.Tail`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Key.Main`, which only this module used -/

section

/-! ## Out -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: the outputs

The arrays, masked by `kOk`, to their outputs (`stores_ok`, for any list of
stores to outputs apart from each other), and `kOk`'s low bit returned with
the saved registers restored (`keyExit_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- `storeA` under `kOk`, which keeps the working space and the header. -/
theorem storeK_ws {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = out) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : word s.mem B (8 * kOk) = mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen kOk)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Ws t B Z w ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14] s t :=
  WP.mono (storeA_ok h hj hP hL (by decide) hp hl hm hl1 hlw hout hsep) fun t ⟨hb, hx, hwr, hrd, k⟩ =>
    have hf := frm_scr hsep hx
    ⟨hb, hx, h.congr hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h.h256; omega_arith)) k (by decide), hf, k⟩

/-- A store: the array, the header slots of its output's pointer and length,
the output and its length. -/
structure St where
  j : Nat
  p : Nat
  l : Nat
  out : Addr
  len : Nat

/-- The stores of `L`, in order. -/
def storesK : List St → List (Prog isa)
  | [] => []
  | e :: L => storeA e.j e.p e.l kOk ++ storesK L

/-- A store's hypotheses. -/
structure St.Ok (e : St) (s : State) (B : Addr) (Z w : Nat) : Prop where
  j : e.j < 16
  p : e.p < 32
  l : e.l < 32
  hp : word s.mem B (8 * e.p) = e.out
  hl : word s.mem B (8 * e.l) = BitVec.ofNat 64 e.len
  l1 : 1 ≤ e.len
  lw : e.len ≤ 8 * w
  wr : ∀ i < e.len, InRegions s.wr (e.out + BitVec.ofNat 64 i) 1
  sep : ∀ i < e.len, Z ≤ ofs B (e.out + BitVec.ofNat 64 i)

theorem frm_word {m m' : Mem} {B : Addr} {Z : Nat} (hf : Frm B [(Z, 2 ^ 64)] m m') (hZ : 8 * 32 ≤ Z) {i : Nat}
    (hi : i < 32) : word m' B (8 * i) = word m B (8 * i) :=
  hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith)) (by omega_arith)

/-- The registers the stores change. -/
abbrev stRegs : List Reg := [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14]

/-- The stores of `L`, each output apart from the others. -/
theorem stores_ok {B : Addr} {Z w : Nat} {c : Bool} {Q : State → Prop} :
    ∀ (L : List St) (rest : List (Prog isa)) (s : State), rest ≠ [] → Ws s B Z w →
    word s.mem B (8 * kOk) = mask c → (∀ e ∈ L, e.Ok s B Z w) →
    L.Pairwise (fun a b => Apart a.out a.len b.out b.len) →
    (∀ t, Ws t B Z w → Frm B [(Z, 2 ^ 64)] s.mem t.mem →
      (∀ e ∈ L, (List.range e.len).map (fun i => t.mem (e.out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w e.j) ((e.len + 7) / 8) else 0) e.len) →
      (∀ x, (∀ e ∈ L, ∀ i < e.len, x ≠ e.out + BitVec.ofNat 64 i) → t.mem x = s.mem x) →
      Keep stRegs s t → WP isa (seqs rest) t Q) →
    WP isa (seqs (storesK L ++ rest)) s Q
  | [], rest, s, _, h, _, _, _, k => k s h (Frm.refl _ _ _) (by simp) (fun _ _ => rfl) (Keep.refl _ _)
  | e :: L, rest, s, hr, h, hm, ho, hpw, k => by
    have h256 := h.h256
    obtain ⟨hj, hp, hl, hpv, hlv, hl1, hlw, hwr, hsep⟩ := ho e List.mem_cons_self
    rw [storesK, List.append_assoc]
    refine wp_seqs_append (by simp [storeA]) (by cases L <;> simp [storesK, storeA, hr])
      (WP.mono (storeK_ws h hj hp hl hpv hlv hm hl1 hlw hwr hsep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
    obtain hpw' := List.pairwise_cons.mp hpw
    refine stores_ok L rest s₁ hr h₁ (by rw [frm_word f₁ h256 (by decide)]; exact hm) (fun e' he' => ?_) hpw'.2
      (fun t ht ft bt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by decide)))
    · obtain ⟨hj', hp', hl', hpv', hlv', hl1', hlw', hwr', hsep'⟩ := ho e' (List.mem_cons_of_mem _ he')
      exact ⟨hj', hp', hl', by rw [frm_word f₁ h256 hp']; exact hpv', by rw [frm_word f₁ h256 hl']; exact hlv',
        hl1', hlw', fun i hi => by rw [k₁.2.2]; exact hwr' i hi, hsep'⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he''
      · rw [← b₁]
        exact List.map_congr_left fun i hi => xt _ fun e'' he''' i' hi' heq =>
          hpw'.1 e'' he''' i (List.mem_range.mp hi) i' hi' heq
      · rw [bt e' he'']
        obtain hj' := (ho e' he').j
        have := (ho e' he').lw
        have := h.sl hj'
        have := h.scr.nowrap
        rw [f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith)) (by omega_arith)]
    · intro x hx
      rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]
termination_by structural L => L

/-- `kOk`'s low bit returned and the saved registers restored. -/
theorem keyExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Bool}
    (hm : word s.mem B (8 * kOk) = mask c) :
    WP isa (.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
        t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, h.rdi, hdrOff, hl kOk (by decide), hm, mask_and1,
      hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide),
      hl 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm'⟩, k⟩ => ⟨hax, ?_, hm', k⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- Zeros to each output of `L`. -/
def zerosK (L : List St) : List (Prog isa) := L.map fun e => zeroOut e.p e.l

/-- Zeros to the outputs of `L`, each apart from the others. -/
theorem zeros_ok {B : Addr} {Z w : Nat} {Q : State → Prop} :
    ∀ (L : List St) (rest : List (Prog isa)) (s : State), rest ≠ [] → Ws s B Z w → (∀ e ∈ L, e.Ok s B Z w) →
    L.Pairwise (fun a b => Apart a.out a.len b.out b.len) →
    (∀ t, Ws t B Z w → Frm B [(Z, 2 ^ 64)] s.mem t.mem →
      (∀ e ∈ L, ∀ i < e.len, t.mem (e.out + BitVec.ofNat 64 i) = 0) →
      (∀ x, (∀ e ∈ L, ∀ i < e.len, x ≠ e.out + BitVec.ofNat 64 i) → t.mem x = s.mem x) →
      Keep [.rsi, .rcx, .rax] s t → WP isa (seqs rest) t Q) →
    WP isa (seqs (zerosK L ++ rest)) s Q
  | [], rest, s, _, h, _, _, k => k s h (Frm.refl _ _ _) (by simp) (fun _ _ => rfl) (Keep.refl _ _)
  | e :: L, rest, s, hr, h, ho, hpw, k => by
    have h256 := h.h256
    obtain ⟨_, hp, hl, hpv, hlv, hl1, hlw, hwr, hsep⟩ := ho e List.mem_cons_self
    obtain hpw' := List.pairwise_cons.mp hpw
    obtain hz := zeroOut_ok h.scr h.rdi h256 hp hl hpv hlv hl1 (by have := h.w2; omega_arith) ⟨hwr, hsep⟩
    obtain step : ∀ s₁, ((∀ i < e.len, s₁.mem (e.out + BitVec.ofNat 64 i) = 0) ∧
        (∀ x, (∀ j < e.len, x ≠ e.out + BitVec.ofNat 64 j) → s₁.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s s₁) →
        WP isa (seqs (zerosK L ++ rest)) s₁ Q := by
      intro s₁ ⟨z₁, x₁, k₁⟩
      obtain f₁ := frm_scr hsep x₁
      obtain h₁ : Ws s₁ B Z w := h.congr f₁ (fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Or.inl (by omega_arith)) k₁ (by decide)
      refine zeros_ok L rest s₁ hr h₁ (fun e' he' => ?_) hpw'.2
        (fun t ht ft zt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by decide)))
      · obtain ⟨hj', hp', hl', hpv', hlv', hl1', hlw', hwr', hsep'⟩ := ho e' (List.mem_cons_of_mem _ he')
        exact ⟨hj', hp', hl', by rw [frm_word f₁ h256 hp']; exact hpv', by rw [frm_word f₁ h256 hl']; exact hlv',
          hl1', hlw', fun i hi => by rw [k₁.2.2]; exact hwr' i hi, hsep'⟩
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he₂
        · intro i hi
          rw [xt _ fun e₃ he₃ i' hi' heq => hpw'.1 e₃ he₃ i hi i' hi' heq]
          exact z₁ i hi
        · exact zt e' he₂
      · intro x hx
        rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]
    rw [zerosK, List.map_cons, List.cons_append]
    obtain hne : zerosK L ++ rest ≠ [] := by simp [hr]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [show List.map (fun e => zeroOut e.p e.l) L ++ rest = zerosK L ++ rest from rfl, hcs]
    exact WP.seq (WP.mono hz fun s₁ h₁ => by rw [← hcs]; exact step s₁ h₁)

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Main -/
section

/-!
# An RSA key from its primes on x86-64: from the loads to `smallMask`

`front_k`: after the head, the loads, the order, `p − 1` and `q − 1`,
`L = lcm(p − 1, q − 1)`, `d` and ZF (`Front`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)

/-- The inputs as numbers: `p`, `q`, `e`, ordered, and `L`. -/
abbrev KIn.P₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev KIn.Q₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev KIn.E (I : KIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev KIn.P (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.Q₀ else I.P₀
abbrev KIn.Q (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.P₀ else I.Q₀
abbrev KIn.L (I : KIn) : Nat := Nat.lcm (I.P - 1) (I.Q - 1)

/-- The lengths. -/
structure KLens (I : KIn) : Prop where
  pl1 : 32 ≤ I.pl
  pl2 : I.pl ≤ 512
  pl8 : I.pl % 8 = 0
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.pl
  ebl : I.eb.length = I.el
  el1 : 1 ≤ I.el
  el8 : I.el ≤ 8

/-- What holds after `smallMask`. -/
structure Front (I : KIn) (m₀ : Mem) (t : State) : Prop where
  ks : KS I m₀ t
  vP : av I t.mem aPa = I.P
  vQ : av I t.mem aQa = I.Q
  vPm : av I t.mem aPm = I.P - 1
  vQm : av I t.mem aQm = I.Q - 1
  ev : word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E
  d : DRes I I.E I.L t.mem
  zf : ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.zf = some (!(decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok))

theorem KLens.W {I : KIn} (L : KLens I) : I.W = 2 * (I.pl / 8) := by
  have := L.pl8; simp only [KIn.W]; omega_arith

theorem lt_of_os2ip_len {bs : List Byte} {n : Nat} (h : bs.length = n) : Spec.Rsa.os2ip bs < 2 ^ (8 * n) := by
  have := VG.Proof.Rsa.lt_of_os2ip bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

/-- From the loads to `smallMask`. -/
theorem front_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) :
    WP isa (seqs ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask))))))) s
      fun t => Front I m₀ t ∧ InScr I.B I.Z s.mem t.mem := by
  have hZ := h.hZ
  have hW := L.W
  obtain hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_arith
  obtain hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  obtain hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  obtain hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_arith))
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp [order, ltA]) (WP.mono (loads_k h L.pbl L.qbl L.ebl
    (by have := L.pl1; omega_arith) (by rw [hW]; have := L.pl8; omega_arith) L.el1 L.el8) fun s₁ ⟨h₁, f₁, vP₁, vQ₁, ev₁⟩ => ?_)
  -- The order.
  refine wp_seqs_append (by simp [order, ltA]) (by simp [decTo]) (WP.mono (order_k h₁) fun s₂ ⟨h₂, f₂, vP₂, vQ₂⟩ => ?_)
  rw [vP₁, vQ₁] at vP₂ vQ₂
  -- `p − 1`, `q − 1`.
  refine wp_seqs_append (by simp [decTo]) (by simp [decTo]) (WP.mono (decTo_k h₂ (o := aPm) (j := aPa) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, vPm₃, _⟩ => ?_)
  refine wp_seqs_append (by simp [decTo]) (by simp [lcmPart, phi]) (WP.mono (decTo_k h₃ (o := aQm) (j := aQa)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, vQm₄, _⟩ => ?_)
  obtain hok3 : [Rc.arr aPm, Rc.arr aC].all Rc.ok = true := by decide
  obtain hok4 : [Rc.arr aQm, Rc.arr aC].all Rc.ok = true := by decide
  obtain vP₄ : av I s₄.mem aPa = I.P := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vP₂]
  obtain vQ₄ : av I s₄.mem aQa = I.Q := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  rw [vP₂] at vPm₃
  rw [f₃.av hok3 (by decide) (by decide) hZ, vQ₂] at vQm₄
  obtain vPm₄ : av I s₄.mem aPm = I.P - 1 := by rw [f₄.av hok4 (by decide) (by decide) hZ, vPm₃]
  obtain hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.P, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega_arith
  obtain hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.Q, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega_arith
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi]) (by simp) (WP.mono (lcm_k h₄ hW vPm₄ vQm₄ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hPw)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQw))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  obtain hokL : [Rc.arr aL, Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR,
    Rc.hdr sMo, Rc.hdr kOk, Rc.priv].all Rc.ok = true := by decide
  obtain hokE : [Rc.arr aPa, Rc.arr aQa, Rc.hdr kEv].all Rc.ok = true := by decide
  obtain ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), f₄.word hok4 (by decide) (by decide),
      f₃.word hok3 (by decide) (by decide), f₂.word (by decide) (by decide) (by decide), ev₁]
  obtain hLW : I.L < 2 ^ (64 * I.W) := by
    obtain h1 : I.L ≤ (I.P - 1) * (I.Q - 1) ∨ I.L = 0 := by
      rcases Nat.eq_zero_or_pos ((I.P - 1) * (I.Q - 1)) with h0 | h0
      · right; simp only [KIn.L]
        rcases Nat.mul_eq_zero.mp h0 with h' | h' <;> simp [h']
      · left; exact Nat.le_of_dvd h0 (Nat.lcm_dvd_mul _ _)
    obtain h2 : (I.P - 1) * (I.Q - 1) < 2 ^ (64 * I.W) := by
      rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_arith, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega_arith) (by omega_arith) (Nat.two_pow_pos _)
    rcases h1 with h1 | h1
    · omega_arith
    · rw [h1]; exact Nat.two_pow_pos _
  -- `d`.
  refine wp_seqs_append (by simp) (by simp [smallMask, constA]) ?_
  simp only [seqs]
  refine WP.mono (dPart_k h₅ hE ev₅ vL₅ hLW) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- ZF.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, zf₇⟩ => ?_
  obtain hokD : csD.all Rc.ok = true := by decide
  obtain hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  obtain pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ [Rc.arr aL, Rc.arr aU, Rc.arr aV,
      Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR, Rc.hdr sMo, Rc.hdr kOk, Rc.priv] →
      av I t.mem j = av I s₄.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  obtain okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  obtain hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  obtain hi : InScr I.B I.Z s.mem t.mem := fun x hx => (ht.inScr x hx).trans (h.inScr x hx).symm
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [zf₇, ← hD, show 64 * (I.pl / 8) = 8 * I.pl by omega_arith]⟩⟩, hi⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), vP₄]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), vQ₄]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), vPm₄]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), vQm₄]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

end

/-! ### `RsaKeyGen.X86_64.Key.NFin`, which only this module used -/

section

/-!
# An RSA key from its primes on x86-64: `n` and the final mask

`n = p q` (`nPart_k`), and `kOk &= ` the masks of `n`'s top bit, `p` and
`q` odd, and `e` valid (`finalMask_k`).
-/

@[expose] public section

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
  obtain sP := h.ws.sl (j := aPa) (by decide)
  obtain sQ := h.ws.sl (j := aQa) (by decide)
  obtain sL := h.ws.sl (j := aQt) (by decide)
  obtain p1 := slot_far (w := I.W) (i := aPa) (j := aQt) (by decide)
  obtain p2 := slot_far (w := I.W) (i := aQa) (j := aQt) (by decide)
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  simp only [nPart, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aQt) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  obtain hok : [Rc.arr aQt].all Rc.ok = true := by decide
  obtain va : wv s₁.mem I.B (slot I.W aPa) w = a := by
    rw [f₁.wv hok (j := aPa) (by decide) (by decide) (Nat.le_refl _) (by omega_using [hW]) h.hZ, ← ha]
    dsimp only [av] at ha
    exact wv_low_of_lt (by omega_using [hW]) (by rw [ha]; exact ha')
  obtain vb : wv s₁.mem I.B (slot I.W aQa) w = b := by
    rw [f₁.wv hok (j := aQa) (by decide) (by decide) (Nat.le_refl _) (by omega_using [hW]) h.hZ, ← hb]
    dsimp only [av] at hb
    exact wv_low_of_lt (by omega_using [hW]) (by rw [hb]; exact hb')
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  obtain hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h₁.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok aPa (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQa (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQt (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  obtain h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  obtain hax₅ : s₅.gpr .rax = off I.B (slot I.W aQa) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQa) ∧
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega_using [hw2])]
    refine ⟨by rw [hW]; congr 1; omega_using [], ?_⟩
    rw [ofNat_sub' (by omega_using []) (by omega_using [hw2])]; congr 1; omega_using [hW]) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  obtain k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  obtain hm₆ : s₆.mem = s₁.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  obtain hz₆ : wv s₆.mem I.B (slot I.W aQt) (w + w + 2) = 0 := by rw [hm₆, ← z₁]; congr 1; omega_using [hW]
  refine WP.mono (mulRows_ok (h₁.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega_using [hW, hw1]) (by omega_using [hW, hw1]) (by omega_using [hW, hw2]) (by omega_using [hW, sL]) (by omega_using [hW, sP])
    (by omega_using [hW, sQ]) (by omega_using [hW, p1]) (by omega_using [hW, p2]) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₇⟩ => ?_
  rw [hz₆, hm₆, va, vb, Nat.zero_add] at hv
  rw [hm₆] at o
  obtain f := KF.arr1 (I := I) (j := aQt) o (Nat.le_refl _) (by omega_using [hW])
  refine ⟨h₁.step f (all_mut_arr (by decide)) (k26.trans k₇) (by decide), (f₁.trans f).mono (by simp), ?_⟩
  rw [show I.W + 2 = w + w + 2 by omega_using [hW]]; exact hv


/-! ## The final mask -/

/-- The top bit of a `W`-word number: of its word `W − 1`. -/
theorem top_bit {m : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) :
    (word m B (d + 8 * (W - 1))).toNat / 2 ^ 63 = if 2 ^ (64 * W - 1) ≤ wv m B d W then 1 else 0 := by
  obtain e : wv m B d W = wv m B d (W - 1) + 2 ^ (64 * (W - 1)) * (word m B (d + 8 * (W - 1))).toNat := by
    rw [show W = W - 1 + 1 from by omega_using [hW], wv]; simp
  obtain ha := wv_lt m B d (W - 1)
  obtain ht := (word m B (d + 8 * (W - 1))).isLt
  generalize wv m B d (W - 1) = a at e ha
  generalize (word m B (d + 8 * (W - 1))).toNat = t at e ht
  obtain hp : 2 ^ (64 * W - 1) = 2 ^ (64 * (W - 1)) * 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega_using [hW]
  generalize 2 ^ (64 * (W - 1)) = R at e ha hp
  rw [e, hp]
  by_cases h63 : 2 ^ 63 ≤ t
  · have : R * 2 ^ 63 ≤ R * t := Nat.mul_le_mul_left _ h63
    rw [ite_eq_left (show R * 2 ^ 63 ≤ a + R * t by omega_using [this])]; omega_using [ht, h63]
  · have : R * t + R ≤ R * 2 ^ 63 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [h63])
    rw [ite_eq_right (show ¬ R * 2 ^ 63 ≤ a + R * t by omega_using [ha, this])]; omega_using [h63]


theorem shr63_mask (x : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = mask (decide (x.toNat / 2 ^ 63 = 1)) := by
  obtain h : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := x.isLt; omega_using []
  rw [h]
  have := x.isLt
  rcases (show x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1 by omega_using []) with e | e <;> rw [e] <;> decide

/-- `[rbx + 8 r12 − 8]`: word `W − 1` of the array at `rbx`. -/
theorem addr_last {b : Addr} {B : Addr} {e W : Nat} (hb : b = off B e) (hW : 1 ≤ W) :
    b + BitVec.ofNat 64 W * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = off B (e + 8 * (W - 1)) := by
  subst hb
  obtain h8 : BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide
  rw [ofNat_mul8, h8, off, off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  refine congrArg (B + ·) ?_
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega_using [hW]


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
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  obtain sN := h.ws.sl (j := aQt) (by decide)
  obtain hld := fun (i : Nat) (hi : i < 32) => h.ws.scr.ld (d := 8 * i) (by have := h.ws.h256; omega_using [hi, this])
  unfold finalMask
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  obtain hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aQt (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
  obtain hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  obtain h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  obtain hmu₂ : u₂.mem = s.mem := by rw [mu₂, mu₁]
  obtain htop : (word s.mem I.B (slot I.W aQt + 8 * (I.W - 1))).toNat / 2 ^ 63 = 1 ↔ 2 ^ (64 * I.W - 1) ≤ n := by
    rw [top_bit hw1, show wv s.mem I.B (slot I.W aQt) I.W = n from hn]; split <;> simp_all
  -- `rcx := ` the masks of the top bit and `ok`.
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) ∧
    t.mem = s.mem) (by
      obtain hok₂ : word u₂.mem I.B (8 * kOk) = mask ok := by rw [hmu₂, hok]
      xrun [State.ea, ix, hdr, hdrOff, h12₂, addr_last hbx hw1, hs₂.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega_using [sN]),
        ((ku₁.trans ku₂).gpr (by decide)).trans h.ws.rdi, hs₂.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this]),
        shr63_mask, hok₂, mask_and', hmu₂]
      have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
      obtain ht' : decide ((s.mem.readW (off I.B (slot I.W aQt + 8 * (I.W - 1))) 64).toNat / 2 ^ 63 = 1) =
          decide (2 ^ (64 * I.W - 1) ≤ n) := decide_eq_decide.mpr htop
      rw [hok', mask_and', ht']) rfl) fun u₃ ⟨⟨hcx₃, mu₃⟩, ku₃⟩ => WP.block_append_iff.mpr ?_
  obtain k13 := (ku₁.trans ku₂).trans ku₃
  obtain h₃ := h.step (cs := []) (by rw [mu₃]; exact KF.refl _ _ _) rfl k13 (by decide)
  -- `p` odd.
  refine WP.mono (oddMask_k h₃ (j := aPa) (by decide)) fun u₄ ⟨mu₄, hax₄, _, _, ku₄⟩ => WP.block_append_iff.mpr ?_
  rw [mu₃, hP] at hax₄
  obtain hcx₄ : u₄.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) := by rw [ku₄.gpr (by decide), hcx₃]
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok &&
    decide (P % 2 = 1)) ∧ t.mem = u₄.mem) (by xrun [hax₄, hcx₄, mask_and']) rfl)
    fun u₅ ⟨⟨hcx₅, mu₅⟩, ku₅⟩ => WP.block_append_iff.mpr ?_
  obtain h₅ := h₃.step (cs := []) (by rw [mu₅, mu₄]; exact KF.refl _ _ _) rfl (ku₄.trans ku₅) (by decide)
  -- `q` odd.
  refine WP.mono (oddMask_k h₅ (j := aQa) (by decide)) fun u₆ ⟨mu₆, hax₆, _, _, ku₆⟩ => ?_
  rw [mu₅, mu₄, mu₃, hQ] at hax₆
  obtain hcx₆ : u₆.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1)) := by
    rw [ku₆.gpr (by decide), hcx₅]
  obtain hm₆ : u₆.mem = s.mem := by rw [mu₆, mu₅, mu₄, mu₃]
  obtain hs₆ := h₅.ws.scr.congr ku₆.2.2
  obtain hdi₆ : u₆.gpr .rdi = I.B := ((ku₄.trans ku₅).trans ku₆).gpr (by decide) |>.trans h₃.ws.rdi
  obtain hev₆ : u₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₆]; exact hev
  -- `e` valid, and the store.
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk))
    (mask (finalOk I.W n P Q e ok))) (by
      xrun [State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
        hs₆.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this]), hev₆, hax₆, hcx₆, mask_and', mask_low,
        sxM1, maskNot, hm₆]
      have hev' : s.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev
      obtain hT : ((BitVec.ofNat 64 e) >>> 33).toNat = e / 2 ^ 33 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      obtain hsub : ∀ c : Bool, 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = mask c := fun _ => rfl
      rw [hev', BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hT, hsub, hsub, maskNot, mask_and', mask_and',
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
      obtain e1 : (decide (e % 2 = 1) && !decide (e < 3) && decide (e / 2 ^ 33 < 1)) = Spec.Rsa.exponentValid e := by
        unfold Spec.Rsa.exponentValid
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
        omega_using []
      refine congrArg (fun v => s.mem.writeW (off I.B (8 * kOk)) (mask v)) ?_
      simp only [finalOk]
      rw [← e1]
      simp only [Bool.and_assoc]) rfl) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, ft, okt⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) mt
    ((((k13.trans ku₄).trans ku₅).trans ku₆).trans kt) (by decide)
  exact ⟨ht, ft, okt⟩

end VG.Proof.RsaKeyGen.X86_64.Key

end

end


/-!
# An RSA key from its primes on x86-64: the key

`keyPart`, once `d` is not too small or does not exist: `qInv`, `dP`, `dQ`,
`n`, the final mask, the stores and the exit (`keyPart_k`); and the zeros
and the status 2 otherwise (`zerosPart_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- The outputs, in the order of the stores. -/
def outsL (I : KIn) : List (Addr × Nat) :=
  [(I.pN, 2 * I.pl), (I.pD, 2 * I.pl), (I.pP, I.pl), (I.pQ, I.pl), (I.pDp, I.pl), (I.pDq, I.pl), (I.pQi, I.pl)]

/-- The stores. -/
def storeL (I : KIn) : List St :=
  [⟨aQt, kNo, kNl, I.pN, 2 * I.pl⟩, ⟨aDd, kDo, kNl, I.pD, 2 * I.pl⟩, ⟨aPa, kPp, kPl, I.pP, I.pl⟩,
    ⟨aQa, kQp, kPl, I.pQ, I.pl⟩, ⟨aX₁, kDp, kPl, I.pDp, I.pl⟩, ⟨aV, kDq, kPl, I.pDq, I.pl⟩,
    ⟨aX₂, kQi, kPl, I.pQi, I.pl⟩]

/-- The outputs: writable, outside the working space, apart. -/
structure KOuts (I : KIn) : Prop where
  wr : ∀ o ∈ outsL I, ∀ i < o.2, InRegions I.Wr (o.1 + BitVec.ofNat 64 i) 1
  sep : ∀ o ∈ outsL I, ∀ i < o.2, I.Z ≤ ofs I.B (o.1 + BitVec.ofNat 64 i)
  apart : (outsL I).Pairwise fun a b => Apart a.1 a.2 b.1 b.2

theorem storeL_outs (I : KIn) : (storeL I).map (fun e => (e.out, e.len)) = outsL I := rfl

theorem storeL_pairwise {I : KIn} (O : KOuts I) :
    (storeL I).Pairwise fun a b => Apart a.out a.len b.out b.len := by
  have := O.apart
  rw [← storeL_outs, List.pairwise_map] at this
  exact this

theorem st_ok {I : KIn} {m₀ : Mem} {t : State} (h : KS I m₀ t) (O : KOuts I) {j p l : Nat} {out : Addr}
    {len : Nat} (hj : j < 16) (hp : p < 32) (hl : l < 32) (hpv : word t.mem I.B (8 * p) = out)
    (hlv : word t.mem I.B (8 * l) = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W)
    (ho : (out, len) ∈ outsL I) : (⟨j, p, l, out, len⟩ : St).Ok t I.B I.Z I.W :=
  ⟨hj, hp, hl, hpv, hlv, hl1, hlw, fun i hi => by rw [h.wr]; exact O.wr _ ho i hi, O.sep _ ho⟩

theorem storeL_ok {I : KIn} {m₀ : Mem} {t : State} (h : KS I m₀ t) (L : KLens I) (O : KOuts I) :
    ∀ e ∈ storeL I, e.Ok t I.B I.Z I.W := by
  have hW := L.W
  have hpl := L.pl1
  have h8 := L.pl8
  intro e he
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.no h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dd h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.pp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dq h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qi h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])

theorem outputs_eq (I : KIn) : outputs = storesK (storeL I) ++
    ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa)) := rfl

theorem zeros_eq (I : KIn) (st : Nat) : zeros st = seqs (zerosK (storeL I) ++
    ([.block (([.mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++ exit)] : List (Prog isa))) := rfl

theorem keyPart_eq (I : KIn) : keyPart = seqs (qinvPart ++ (crtPart ++ (nPart ++ (([.block finalMask] : List (Prog isa)) ++
    (storesK (storeL I) ++ ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa))))))) := by
  rw [keyPart, ← outputs_eq I]; simp only [List.append_assoc]

/-- A number below `2^(64 v)` read from `v ≤ W` words. -/
theorem wv_of_av {I : KIn} {m : Mem} {j v x : Nat} (hv : v ≤ I.W) (h : av I m j = x) (hx : x < 2 ^ (64 * v)) :
    wv m I.B (slot I.W j) v = x := by
  rw [← h]; exact wv_low_of_lt hv (by rw [show wv m I.B (slot I.W j) I.W = av I m j from rfl, h]; exact hx)

/-- What `keyPart` leaves, from `Front` and `kOk` the mask of `ok`. -/
def TailPost (I : KIn) (s t : State) (ok : Bool) : Prop :=
  ∃ x : Nat, ((qMod I.P : Nat) : Int) ∣ (x : Int) * I.Q - Nat.gcd I.Q (qMod I.P) ∧ x < qMod I.P ∧
    (let c := finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok)
     t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
     Spec.Rsa.bytesAt t.mem I.pN (2 * I.pl) = Spec.Rsa.i2osp (if c then I.P * I.Q else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pD (2 * I.pl) = Spec.Rsa.i2osp (if c then av I s.mem aDd else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pP I.pl = Spec.Rsa.i2osp (if c then I.P else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQ I.pl = Spec.Rsa.i2osp (if c then I.Q else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDp I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.P - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDq I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.Q - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQi I.pl = Spec.Rsa.i2osp (if c then x else 0) I.pl) ∧
    (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    t.gpr .rsp = I.sp

/-- `keyPart`. -/
theorem keyPart_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : Front I m₀ s) (L : KLens I) (O : KOuts I) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa keyPart s (fun t => TailPost I s t ok) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  obtain hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_using [this]
  obtain hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    have := lt_of_os2ip_len L.pbl; have := lt_of_os2ip_len L.qbl
    simp only [KIn.P, KIn.P₀, KIn.Q₀]; rw [← hw8]; split <;> omega_arith
  obtain hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    have := lt_of_os2ip_len L.pbl; have := lt_of_os2ip_len L.qbl
    simp only [KIn.Q, KIn.P₀, KIn.Q₀]; rw [← hw8]; split <;> omega_arith
  rw [keyPart_eq I]
  -- `qInv`.
  refine wp_seqs_append (by simp [qinvPart]) (by simp [crtPart, divisorOf]) (WP.mono (qinvPart_k hk h.vP h.vQ hok
    (by have := L.pl1; omega_using [hW, this]) (by rw [show I.W / 2 = I.pl / 8 by omega_using [hW]]; exact hPw)
    (by rw [show I.W / 2 = I.pl / 8 by omega_using [hW]]; exact hQw))
    fun s₁ ⟨h₁, f₁, ok₁, hdv₁, hx₁⟩ => ?_)
  generalize hx : av I s₁.mem aX₂ = x at hdv₁ hx₁
  obtain hokQ : csQ.all Rc.ok = true := by decide
  -- `dP`, `dQ`.
  refine wp_seqs_append (by simp [crtPart, divisorOf]) (by simp [nPart]) (WP.mono (crtPart_k h₁
    (d := av I s.mem aDd) (a := I.P - 1) (b := I.Q - 1) (by rw [f₁.av hokQ (by decide) (by decide) hZ])
    (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vPm]) (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vQm]))
    fun s₂ ⟨h₂, f₂, dP₂, dQ₂⟩ => ?_)
  obtain hokC : csC.all Rc.ok = true := by decide
  -- `n`.
  refine wp_seqs_append (by simp [nPart]) (by simp) (WP.mono (nPart_k h₂ hW
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vP)
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vQ) hPw hQw)
    fun s₃ ⟨h₃, f₃, n₃⟩ => ?_)
  obtain hn : I.P * I.Q < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_using [], Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega_using [hQw]) (Nat.two_pow_pos _)
  obtain hokN : [Rc.arr aQt].all Rc.ok = true := by decide
  obtain vN₃ : av I s₃.mem aQt = I.P * I.Q := av_of_full n₃ hn
  obtain vP₃ : av I s₃.mem aPa = I.P := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vP]
  obtain vQ₃ : av I s₃.mem aQa = I.Q := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vQ]
  obtain ev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide),
      f₁.word hokQ (by decide) (by decide), h.ev]
  obtain ok₃ : word s₃.mem I.B (8 * kOk) = mask (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide), ok₁]
  obtain hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_arith))
  -- The final mask.
  refine wp_seqs_append (by simp) (by simp [storesK, storeL, storeA]) ?_
  simp only [seqs]
  refine WP.mono (finalMask_k h₃ vN₃ vP₃ vQ₃ hE ev₃ ok₃) fun s₄ ⟨h₄, f₄, ok₄⟩ => ?_
  generalize hc : finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) = cv at ok₄
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  obtain v4 : ∀ j, j < 16 → Rc.arr j ∉ [Rc.arr aQt] → Rc.arr j ∉ csC → Rc.arr j ∉ csQ →
      av I s₄.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₄.av hokO hj (by simp) hZ, f₃.av hokN hj h1 hZ, f₂.av hokC hj h2 hZ, f₁.av hokQ hj h3 hZ]
  -- The stores and the exit.
  refine stores_ok (Q := fun t => TailPost I s t ok) (storeL I) _ s₄ (by simp) h₄.ws ok₄ (storeL_ok h₄ L O)
    (storeL_pairwise O) fun t ht ft bt xt kt => ?_
  simp only [seqs]
  refine WP.mono (keyExit_ok ht (c := cv) (by rw [frm_word ft ht.h256 (by decide)]; exact ok₄))
    fun u ⟨hax, hsv, hmu, ku⟩ => ?_
  obtain b := fun e he => (bt e he)
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b
  obtain ⟨bN, bD, bP, bQ, bDp, bDq, bQi⟩ := b
  obtain hlen : (I.pl + 7) / 8 = I.pl / 8 := by have := L.pl8; omega_using [this]
  obtain hlen2 : (2 * I.pl + 7) / 8 = I.W := by have := L.pl8; simp only [KIn.W]; omega_using [this]
  obtain hv : I.pl / 8 ≤ I.W := by omega_using [hlen2]
  obtain hdvw : ∀ a, a ≤ I.P → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hPw, ha]
  obtain hdvwq : ∀ a, a ≤ I.Q → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hQw, ha]
  obtain hdv0 : ∀ a, 0 < dv a := fun a => by unfold dv; split <;> omega_arith
  obtain hqm : qMod I.P < 2 ^ (64 * (I.pl / 8)) := by
    unfold qMod; split
    · exact hPw
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ 64 * (I.pl / 8) by
        have := L.pl1; omega_using [this]))
  obtain iv : ∀ {len v : Nat} {o : Addr} {w' : Nat},
      (List.range len).map (fun i => t.mem (o + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if cv then w' else 0) len → w' = v →
      Spec.Rsa.bytesAt u.mem o len = Spec.Rsa.i2osp (if cv = true then v else 0) len := fun hb hw => by
    simp only [Spec.Rsa.bytesAt]; rw [hmu, hb, hw]
  refine ⟨x, hdv₁, hx₁, ?_, fun i hi => ?_, fun y hy hny => ?_, ?_⟩
  · dsimp only
    rw [hc]
    refine ⟨hax, iv bN ?_, iv bD ?_, iv bP ?_, iv bQ ?_, iv bDp ?_, iv bDq ?_, iv bQi ?_⟩
    · rw [hlen2]; show av I s₄.mem aQt = _; rw [f₄.av hokO (by decide) (by decide) hZ, vN₃]
    · rw [hlen2]; exact v4 aDd (by decide) (by decide) (by decide) (by decide)
    · rw [hlen]; exact wv_of_av hv (v4 aPa (by decide) (by decide) (by decide) (by decide) |>.trans h.vP) hPw
    · rw [hlen]; exact wv_of_av hv (v4 aQa (by decide) (by decide) (by decide) (by decide) |>.trans h.vQ) hQw
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dP₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvw _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dQ₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvwq _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ,
        f₂.av hokC (by decide) (by decide) hZ, hx]) (by omega_using [hx₁, hqm])
  · rw [hsv i hi, frm_word ft ht.h256 (by omega_using [hi])]; exact h₄.args.saved i hi
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy', h₄.inScr y hy, hk.inScr y hy]
  · rw [ku.gpr (by decide), kt.gpr (by decide), h₄.rsp]

/-- The status `st` returned and the saved registers restored. -/
theorem stExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (st : Nat) :
    WP isa (.block (([.mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = (BitVec.ofNat 32 st).setWidth 64 ∧
        (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
        t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = (BitVec.ofNat 32 st).setWidth 64 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, h.rdi, hdrOff, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
      hl 4 (by decide), hl 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm'⟩, k⟩ => ⟨hax, ?_, hm', k⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- What `zeros 2` leaves. -/
def ZerosPost (I : KIn) (s t : State) : Prop :=
  t.gpr .rax = (BitVec.ofNat 32 2).setWidth 64 ∧
    (∀ o ∈ outsL I, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0) ∧
    (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    t.gpr .rsp = I.sp

/-- `zeros 2`: zeros to the outputs, and the status 2. -/
theorem zerosPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) (O : KOuts I) :
    WP isa (zeros 2) s (ZerosPost I s) := by
  rw [zeros_eq I]
  refine zeros_ok (storeL I) _ s (by simp) h.ws (storeL_ok h L O) (storeL_pairwise O)
    fun t ht ft zt xt kt => ?_
  simp only [seqs]
  refine WP.mono (stExit_ok ht 2) fun u ⟨hax, hsv, hmu, ku⟩ => ⟨hax, fun o ho => ?_, fun i hi => ?_,
    fun y hy hny => ?_, ?_⟩
  · rw [← storeL_outs] at ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [hmu]; exact zt e he i (List.mem_range.mp hi)
  · rw [hsv i hi, frm_word ft ht.h256 (by omega_using [hi])]; exact h.args.saved i hi
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy']
  · rw [ku.gpr (by decide), kt.gpr (by decide), h.rsp]

end VG.Proof.RsaKeyGen.X86_64.Key

end

end


/-! ## Ctx -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: the precondition, as the code uses it

`keyIn s`: the inputs, from the state on entry; `KCtx s`: what the code
uses of `keyPre` (`keyCtx_of`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)

/-- The inputs, from the state on entry. -/
def keyIn (s : State) : KIn where
  B := arg s 10
  Z := (arg s 11).toNat * 8
  pl := (s.gpr .r9).toNat
  pN := s.gpr .rdi
  pD := s.gpr .rdx
  pP := s.gpr .r8
  pQ := arg s 0
  pDp := arg s 2
  pDq := arg s 4
  pQi := arg s 6
  pE := arg s 8
  el := (arg s 9).toNat
  sv i := s.gpr (saved.getD i .rax)
  pb := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  qb := bytesAt s.mem (arg s 0) (s.gpr .r9).toNat
  eb := bytesAt s.mem (arg s 8) (arg s 9).toNat
  Wr := s.wr
  sp := s.gpr .rsp

/-- What the code uses of `keyPre`. -/
structure KCtx (s : State) : Prop where
  L : KLens (keyIn s)
  rsi : (s.gpr .rsi).toNat = 2 * (s.gpr .r9).toNat
  hs : Scr s (arg s 10) ((arg s 11).toNat * 8)
  hZ : slot (keyIn s).W 26 ≤ (arg s 11).toNat * 8
  ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 11, ∀ m', Outside (arg s 10) 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j
  p : Src s (arg s 10) ((arg s 11).toNat * 8) (s.gpr .r8) (keyIn s).pb
  q : Src s (arg s 10) ((arg s 11).toNat * 8) (arg s 0) (keyIn s).qb
  e : Src s (arg s 10) ((arg s 11).toNat * 8) (arg s 8) (keyIn s).eb
  O : KOuts (keyIn s)
  hret : ∀ b < 8, (arg s 11).toNat * 8 ≤ ofs (arg s 10) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ o ∈ outsL (keyIn s), ∀ i < o.2, s.gpr .rsp + BitVec.ofNat 64 b ≠ o.1 + BitVec.ofNat 64 i

theorem kStk_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega_using []]

theorem kStk_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [kStk_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem kApart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

theorem keyCtx_of {s : State} (h : keyPre s) : KCtx s := by
  simp only [keyPre] at h
  sig_split h
  rename_i hsp hrd hwr dnd dnp dnq dndp dndq dnqi dne dns dna ddp ddq dddp dddq ddqi dde dds dda dpq
    dpdp dpdq dpqi dpe dps dpa dqdp dqdq dqqi dqe dqs dqa dpdq' dpqi' dpe' dps' dpa' dqqi' dqe' dqs'
    dqa' dqie dqis dqia des dsa dRn dRd dRp dRq dRdp dRdq dRqi dRe dRs dRa wn wd wp wq wdp wdq wqi
    we ws hpl hsi hcx hql hdpl hdql hqil hel1 hel8
  have hsl := h
  obtain ⟨hpl1, hpl2, hpl8⟩ := hpl
  unfold Spec.Rsa.scratchWords at hsl
  obtain hs : Scr s (arg s 10) ((arg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) ws
  have hn := hs.nowrap
  obtain hargs : (⟨stackArgAddr s 0, 96⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  simp only [hcx, hsi] at dnd ddp ddq dddp dddq ddqi dde dds dda dRd wd
  simp only [hsi] at dnp dnq dndp dndq dnqi dne dns dna dRn wn
  simp only [hql] at dnq ddq dpq dqdp dqdq dqqi dqe dqs dqa dRq wq
  simp only [hdpl] at dndp dddp dpdp dqdp dpdq' dpqi' dpe' dps' dpa' dRdp wdp
  simp only [hdql] at dndq dddq dpdq dqdq dpdq' dqqi' dqe' dqs' dqa' dRdq wdq
  simp only [hqil] at dnqi ddqi dpqi dqqi dpqi' dqqi' dqie dqis dqia dRqi wqi
  obtain hwr' : ∀ (o : Addr) (l : Nat), (⟨o, l⟩ : Region) ∈ s.wr → l ≤ 2 ^ 64 → ∀ i < l,
      InRegions s.wr (o + BitVec.ofNat 64 i) 1 := fun o l hm hl i hi => ⟨_, hm, contains_byte o hi hl⟩
  obtain hpw : (s.gpr .r9).toNat ≤ 2 ^ 64 := by omega_using []
  refine ⟨⟨hpl1, hpl2, hpl8, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, hel1, hel8⟩, hsi, hs,
    by simp only [keyIn, KIn.W, slot, hdrBytes]; omega_using [hsi, hsl, hpl1],
    fun j hj => ⟨_, hargs, by rw [kStk_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 96) (by omega_using [hj, hb]) (by omega_using []))
      rw [← kStk_add s j b] at this; omega_using [hsl, this])),
    src_of_region (by rw [hwr]; simp) (by omega_using []) dps,
    src_of_region (by rw [hwr]; simp [hql]) (by omega_using []) dqs,
    src_of_region (by rw [hrd]; simp) (by omega_using []) des,
    ⟨fun o ho => ?_, fun o ho => ?_, ?_⟩, fun b hb => ?_⟩
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact hwr' _ _ (by rw [hwr, hsi]; simp) (by omega_using [wn])
    · exact hwr' _ _ (by rw [hwr, hcx, hsi]; simp) (by omega_using [wn])
    · exact hwr' _ _ (by rw [hwr]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hql]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hdpl]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hdql]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hqil]; simp) (by omega_using [])
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> intro i hi
    · exact out_scr dns (contains_byte _ hi (by omega_using [wn]))
    · exact out_scr dds (contains_byte _ hi (by omega_using [wn]))
    · exact out_scr dps (contains_byte _ hi (by omega_using []))
    · exact out_scr dqs (contains_byte _ hi (by omega_using []))
    · exact out_scr dps' (contains_byte _ hi (by omega_using []))
    · exact out_scr dqs' (contains_byte _ hi (by omega_using []))
    · exact out_scr dqis (contains_byte _ hi (by omega_using []))
  · simp only [outsL, keyIn, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    exact ⟨⟨kApart_of dnd (by omega_using [wn]) (by omega_using [wn]), kApart_of dnp (by omega_using [wn]) (by omega_using []),
        kApart_of dnq (by omega_using [wn]) (by omega_using []), kApart_of dndp (by omega_using [wn]) (by omega_using []),
        kApart_of dndq (by omega_using [wn]) (by omega_using []), kApart_of dnqi (by omega_using [wn]) (by omega_using [])⟩,
      ⟨kApart_of ddp (by omega_using [wn]) (by omega_using []), kApart_of ddq (by omega_using [wn]) (by omega_using []),
        kApart_of dddp (by omega_using [wn]) (by omega_using []), kApart_of dddq (by omega_using [wn]) (by omega_using []),
        kApart_of ddqi (by omega_using [wn]) (by omega_using [])⟩,
      ⟨kApart_of dpq (by omega_using []) (by omega_using []), kApart_of dpdp (by omega_using []) (by omega_using []),
        kApart_of dpdq (by omega_using []) (by omega_using []), kApart_of dpqi (by omega_using []) (by omega_using [])⟩,
      ⟨kApart_of dqdp (by omega_using []) (by omega_using []), kApart_of dqdq (by omega_using []) (by omega_using []),
        kApart_of dqqi (by omega_using []) (by omega_using [])⟩,
      ⟨kApart_of dpdq' (by omega_using []) (by omega_using []), kApart_of dpqi' (by omega_using []) (by omega_using [])⟩,
      kApart_of dqqi' (by omega_using []) (by omega_using [])⟩
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega_using [hb]) (by omega_using [])
    refine ⟨out_scr dRs hc, fun o ho i hi he => ?_⟩
    simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hi he
    · exact dRn _ hc (by rw [he]; exact contains_byte _ hi (by omega_using [wn]))
    · exact dRd _ hc (by rw [he]; exact contains_byte _ hi (by omega_using [wn]))
    · exact dRp _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRq _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRdp _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRdq _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRqi _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Res -/
section

/-!
# An RSA key from its primes on x86-64: the results, against `keyOp`

What the zeros (`outsRes_zeros`) and `keyPart` (`outsRes_tail`) leave is
`keyOp`'s status and outputs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)
open VG.Spec.RsaKeyGen (keyFromPrimes)
open VG.Proof.RsaKeyGen (keyOp keyStatus)

/-- The status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (rax : BitVec 64) : Prop :=
  (rax.setWidth 32).toNat = keyStatus (keyOp I.pl I.eb I.pb I.qb) ∧
    match keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, bytesAt m o.1 o.2 = List.replicate o.2 0

theorem keyOp_inr {pl : Nat} {eB pB qB : List Byte}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) = .inr ()) :
    keyOp pl eB pB qB = .inr () := by
  unfold keyOp; rw [h]

theorem keyOp_error {pl : Nat} {eB pB qB : List Byte} {f : Spec.RsaKeyGen.Failure}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.error f)) :
    keyOp pl eB pB qB = .inl (.error f) := by
  unfold keyOp; rw [h]

theorem keyOp_ok {pl : Nat} {eB pB qB : List Byte} {k : Spec.RsaKeyGen.Key}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.ok k)) :
    keyOp pl eB pB qB = .inl (.ok [Spec.Rsa.i2osp k.n (2 * pl), Spec.Rsa.i2osp k.d (2 * pl),
      Spec.Rsa.i2osp k.p pl, Spec.Rsa.i2osp k.q pl, Spec.Rsa.i2osp k.dP pl,
      Spec.Rsa.i2osp k.dQ pl, Spec.Rsa.i2osp k.qInv pl]) := by
  unfold keyOp; rw [h]

theorem setWidth32 (n : Nat) (h : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-- The zeros and the status 2, for `d ≤ 2^(8 pl)`. -/
theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .rax) := by
  obtain hr : keyFromPrimes (16 * I.pl) I.E I.P₀ I.Q₀ = .inr () := by
    unfold keyFromPrimes
    obtain hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
      by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
    rw [hswap]
    dsimp only
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, show 16 * I.pl / 2 = 8 * I.pl by omega_using []]
    dsimp only
    rw [ite_eq_left hsm]
  rw [OutsRes, keyOp_inr hr, Z.1]
  exact ⟨by decide, Z.2.1⟩

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  simp [Spec.Rsa.i2osp, List.map_const']

/-- The outputs and the status of `keyPart`, for `d > 2^(8 pl)` or no `d`. -/
theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .rax) := by
  obtain ⟨x, hx, hxl, ⟨hax, hN, hD, hP, hQ, hDp, hDq, hQi⟩, -⟩ := T
  obtain he : I.E < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_using [this]))
  obtain hk := keyFromPrimes_code (x := x) L.pl1 L.pl2 (lt_of_os2ip_len L.pbl) (lt_of_os2ip_len L.qbl) he hx hxl
  obtain hW : 64 * I.W - 1 = 16 * I.pl - 1 := by rw [L.W]; have := L.pl8; omega_using [this]
  simp only [finalOk, hW] at hax hN hD hP hQ hDp hDq hQi
  obtain hstat : ∀ c : Bool, ((BitVec.ofNat 64 c.toNat).setWidth 32).toNat = c.toNat := fun c =>
    setWidth32 _ (by cases c <;> decide)
  rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
  · have hok' : ok = false := by
      cases ok
      · rfl
      · obtain ⟨d, hd⟩ := hok.mpr rfl; rw [hi] at hd; cases hd
    subst hok'
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    rw [OutsRes, keyOp_error hk, hax, hstat]
    refine ⟨rfl, ?_⟩
    simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
  · have hok' : ok = true := hok.mp ⟨d, hi⟩
    subst hok'
    obtain hd := hdd d hi
    rw [hd, Bool.and_true, decide_eq_false_iff_not] at hb
    obtain hd2 : 2 ≤ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 8 * I.pl by have := L.pl1; omega_using [this])
      omega_using [hb, this]
    obtain hqp : I.Q ≤ I.P := by simp only [KIn.P, KIn.Q]; split <;> omega_arith
    obtain ⟨hP3, hQ2, -⟩ := primes_of_inverse hqp hi hd2
    obtain hdvP : dv (I.P - 1) = I.P - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hP3]
    obtain hdvQ : dv (I.Q - 1) = I.Q - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hQ2]
    simp only [Bool.and_true, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hb)] at hk
    simp only [hd, hdvP, hdvQ] at hD hDp hDq
    generalize hc : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qMod I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c
      at hax hN hD hP hQ hDp hDq hQi
    have hc' : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qModP I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c := hc
    rw [hc'] at hk
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [OutsRes, keyOp_error hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, i2osp_zero] at hN hD hP hQ hDp hDq hQi
      exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
    · simp only [↓reduceIte] at hk hN hD hP hQ hDp hDq hQi
      rw [OutsRes, keyOp_ok hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.map_cons, List.map_nil, hN, hD, hP, hQ, hDp, hDq, hQi]

end VG.Proof.RsaKeyGen.X86_64.Key

end
