import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma

/-!
# RSA with AVX512_IFMA on x86-64: the bases in the primes' workspaces

`pre` computes `G` once in `n`'s workspace and, for each prime `X`, enters
its workspace and reduces (`enterRedc_ok`): `R_X` into `aY` (from `G`)
and `x R_X` into `aXc` (from `x G`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Into a prime's workspace (`rdi := [sl]`), and `aXc := [j] R^-K mod X`. -/
theorem enterRedc_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X : Nat}
    {sl o wx j : Nat} (hj : j < 8) (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X)
    (hX1 : 1 < X) :
    WP isa (seqs (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ redc M.mm j)) s fun t =>
      SubCtx t B Z o w wx mx ∧ XVals t B o wx mx X ∧ wv t.mem (off B o) (slot wx aXc) wx < X ∧
      wv t.mem (off B o) (slot wx aXc) wx * 2 ^ (64 * wx * nChunks w wx) % X =
        wv s.mem B (slot w j) w % X ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Frm (off B o) (redcRanges wx) s.mem t.mem ∧
      Keep (mmRegs ++ ([.rdi] : List Reg)) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  refine wp_seqs_append (by simp) (by simp [redc]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun s₂ ⟨⟨hdi₂, hm₂⟩, k₂⟩ => ?_
  have hc₂ : SubCtx s₂ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₂.2.2) (by rw [hm₂]; exact hg.hdr) (by rw [hm₂]; exact hws) hdi₂ hlo hhi
  have hX₂ : XVals s₂ B o wx mx X := by
    rw [show s₂ = { s₂ with mem := s.mem } by rw [← hm₂]] ; exact ⟨hX.n, hX.inv, hX.one⟩
  refine WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega) hX1 hj)
    fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, f₃, k₃⟩ => ⟨hc₃, hX₃, hlt₃, by rw [← hm₂]; exact hv₃, ?_, ?_, ?_⟩
  · rw [← hm₂]; exact f₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  · rw [← hm₂]; exact f₃
  · exact (k₂.trans k₃).mono (by simp [mmRegs])


/-- Back to `n`'s workspace, whose header the prime's phase kept. -/
theorem leaveBack_ok {s₀ t : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {o wx : Nat}
    (hg : Good s₀ B Z w minv) (hc : SubCtx t B Z o w wx mx) (hf : Frm B [xRange o wx] s₀.mem t.mem)
    (hlo : slot w 8 ≤ o) :
    WP isa (.block [leave]) t fun t' => Good t' B Z w minv ∧ t'.mem = t.mem ∧ Keep [.rdi] t t' := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hl : InRegions (t.rd ++ t.wr) (off (off B o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by unfold sLink sFn; omega)
  refine WP.mono (WP.keep [.rdi] (Q := fun t' => t'.gpr .rdi = B ∧ t'.mem = t.mem)
    (by xrun [leave, State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl) fun t' ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hb : ∀ d, d + 8 ≤ o → word t'.mem B d = word s₀.mem B d := fun d hd => by
    rw [hm]; exact hf.x_below hd ho64
  have hH := hg.hdr
  exact ⟨⟨hc.scr.congr k.2.2, hdi, (hb _ (by unfold sW; omega)).trans hH.hw,
    (hb _ (by unfold sMinv; omega)).trans hH.hminv,
    fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hH.harr j hj)⟩, hm, k⟩


/-- `K = 2` chunks of the prime's words in `n`'s. -/
theorem nChunks_two {w wx : Nat} (hw2 : w = 2 * wx) (hwx : 1 ≤ wx) : nChunks w wx = 2 := by
  show (w + wx - 1) / wx = 2
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- `prep`: `R_X` into the prime's `aY`, `x R_X` into its `aXc`, from `n`'s
`R_n² mod n` and `x R_n mod n` (`R_n = R_X²`). Only the prime's workspace
changes. -/
theorem prep_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C : Nat}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (hwx2 : 2 ≤ wx) (hw2 : w = 2 * wx) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hN : NVals s B w minv N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1) :
    WP isa (seqs (CrtIfma.prep M.mm sl)) s fun t => Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧
      XVals t B o wx mx X ∧ wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
      wv t.mem (off B o) (slot wx aXc) wx < X ∧
      (X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X) ∧
      Frm B [xRange o wx] s.mem t.mem ∧ Keep mmRegs s t ∧
      word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX) := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  have hwx : wx ≤ w := by omega
  have hK := nChunks_two hw2 (by omega)
  have hRx : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have hRR : Nat.Coprime (2 ^ (64 * wx * 2)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  have e2 : 2 ^ (64 * w) = 2 ^ (64 * wx * 2) := by rw [hw2]; congr 1; omega
  have lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
  have hrm : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := fun r hr => by
    simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn, slot, hdrBytes] <;>
      omega
  have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rw [show CrtIfma.prep M.mm sl = (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
      redc M.mm Public.aR2) ++ (copyArr Public.aY aXc ++ (redc M.mm Public.aXm ++ (([M.mm aT Public.aY aXc] :
      List (Prog isa)) ++ (copyArr aXc aT ++ [M.mm Public.aY Public.aY Public.aOne, .block [leave]])))) by
    simp only [CrtIfma.prep, List.append_assoc]]
  -- `aXc := R_n² R_X^-2 = R_X²`.
  refine wp_seqs_append (by simp) (by simp [copyArr]) (WP.mono (enterRedc_ok M (j := Public.aR2) (by decide) hg
    hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1) fun s₁ ⟨hc₁, hX₁, hlt₁, hv₁, f₁, r₁, k₁⟩ => ?_)
  -- `aY := aXc`.
  refine wp_seqs_append (by simp [copyArr]) (by simp [redc]) (WP.mono (copyArr_ok hc₁.good (Nat.le_refl _)
    (by omega) (by omega) (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide))
    fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hK] at hv₁
  have hc₂ := hc₁.of_frm (rs := [(slot wx Public.aY, 8 * wx)]) (Frm.of_outside ho₂ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₂.2.2 (k₂.gpr (by decide))
  have hX₂ : XVals s₂ B o wx mx X := hX₁.of_outside ho₂ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₁.good.scr.nowrap; omega)
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem :=
    (ho₂.mono (o' := slot wx Public.aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _)
  have f02 := f₁.trans fx₂
  -- `aXc := x R_n R_X^-2 = x`.
  refine wp_seqs_append (by simp [redc]) (by simp) (WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega) hX1
    (j := Public.aXm) (by decide)) fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, r₃, k₃⟩ => ?_)
  rw [show (w + wx - 1) / wx = 2 from hK] at hv₃
  have fx₃ : Frm B [xRange o wx] s₂.mem s₃.mem := r₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hXm₂ : wv s₂.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    wv_congr fun i hi => f02.x_below (by have := slot_le (w := w) (show Public.aXm < 8 by decide); omega) ho64
  have hY₃ : wv s₃.mem (off B o) (slot wx Public.aY) wx = wv s₁.mem (off B o) (slot wx aXc) wx := by
    rw [r₃.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hv₂]
  -- `aT := x R_X`.
  refine wp_seqs_append (by simp) (by simp [copyArr]) (WP.mono (M.mm_ok (o := aT) (a := Public.aY) (b := aXc)
    hc₃.good (Nat.le_refl _) hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX₃.inv (by rw [hX₃.n]; exact hlt₃)) fun s₄ ⟨_, hT₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hX₃.n] at hT₄ hm₄
  obtain ⟨hc₄, hX₄, fx₄⟩ := hc₃.of_arrays hX₃ ha₄ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₄.2.2 (k₄.gpr (by decide)) (by omega)
  have hz₄ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₄.good.scr.nowrap; omega
  have hY₄ : wv s₄.mem (off B o) (slot wx Public.aY) wx = wv s₃.mem (off B o) (slot wx Public.aY) wx :=
    ha₄.wv_of_not_mem (by decide) (by decide) hz₄
  -- `aXc := aT`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hc₄.good (Nat.le_refl _)
    (by omega) (by omega) (o := aXc) (a := aT) (by decide) (by decide) (by decide))
    fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_)
  have lC := slot_le (w := wx) (show aXc < 8 by decide)
  have hC0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have hc₅ := hc₄.of_frm (rs := [(slot wx aXc, 8 * wx)]) (Frm.of_outside ho₅ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₅.2.2 (k₅.gpr (by decide))
  have hX₅ : XVals s₅ B o wx mx X := hX₄.of_outside ho₅ (by decide) (by decide) (by decide) (by omega) hz₄
  have fx₅ : Frm B [xRange o wx] s₄.mem s₅.mem :=
    (ho₅.mono (o' := slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _)
  have hY₅ : wv s₅.mem (off B o) (slot wx Public.aY) wx = wv s₄.mem (off B o) (slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    exact ho₅.wv (by omega) (by omega)
  -- `aY := R_X² R_X^-1 = R_X`.
  refine WP.seq (WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aOne) hc₅.good (Nat.le_refl _)
    hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₅.inv
    (by rw [hX₅.n, hX₅.one]; exact hX1)) fun s₆ ⟨_, hlt₆, hm₆, ha₆, k₆⟩ => ?_)
  rw [hX₅.n, hX₅.one, Nat.mul_one] at hm₆
  rw [hX₅.n] at hlt₆
  obtain ⟨hc₆, hX₆, fx₆⟩ := hc₅.of_arrays hX₅ ha₆ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₆.2.2 (k₆.gpr (by decide)) (by omega)
  have hC₆ : wv s₆.mem (off B o) (slot wx aXc) wx = wv s₄.mem (off B o) (slot wx aT) wx := by
    rw [ha₆.wv_of_not_mem (by decide) (by decide) hz₄, hv₅]
  have fall := ((((f02.trans fx₃).trans fx₄).trans fx₅).trans fx₆)
  refine WP.mono (leaveBack_ok hg hc₆ fall hlo) fun t ⟨hg', hm', k'⟩ => ?_
  have kall := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k'
  refine ⟨hg', by rw [hm']; exact hc₆.ws, ?_, by rw [hm']; exact hlt₆, fun hd => ?_,
    by rw [hm', hC₆]; exact hT₄, fun hd => ?_, by rw [hm']; exact fall, ⟨fun r hr => ?_, kall.2⟩, ?_⟩
  · rw [show t = { t with mem := s₆.mem } by rw [← hm']]; exact ⟨hX₆.n, hX₆.inv, hX₆.one⟩
  · -- `aXc₁ = R_X²`, so `aY R_X ≡ R_X²`.
    have h1 : wv s₁.mem (off B o) (slot wx aXc) wx % X = 2 ^ (64 * wx * 2) % X :=
      VG.Proof.Bignum.mont_cancel hRR (by
        rw [hv₁, ← Nat.mod_mod_of_dvd _ hd, hN.r2, Nat.mod_mod_of_dvd _ hd, e2, ← Nat.pow_add])
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hm', hm₆, hY₅, hY₄, hY₃, h1, ← Nat.pow_add]
    congr 2; omega
  · -- `aXc₃ = x`, so `aT₄ R_X ≡ R_X² x`.
    have h3 : wv s₃.mem (off B o) (slot wx aXc) wx % X = C % X :=
      VG.Proof.Bignum.mont_cancel hRR (by
        rw [hv₃, hXm₂, ← Nat.mod_mod_of_dvd _ hd, hXm, Nat.mod_mod_of_dvd _ hd, e2])
    have h1 : wv s₁.mem (off B o) (slot wx aXc) wx % X = 2 ^ (64 * wx * 2) % X :=
      VG.Proof.Bignum.mont_cancel hRR (by
        rw [hv₁, ← Nat.mod_mod_of_dvd _ hd, hN.r2, Nat.mod_mod_of_dvd _ hd, e2, ← Nat.pow_add])
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hm', hC₆, hm₄, hY₃, Nat.mul_mod, h3, h1, ← Nat.mul_mod, Nat.mul_comm, Nat.mul_assoc C, ← Nat.pow_add]
    congr 3; omega
  · by_cases h : r = .rdi
    · subst h; rw [hg'.rdi, hg.rdi]
    · exact kall.1 r (by simp only [mmRegs, List.mem_cons, List.mem_append] at hr ⊢; simp_all)
  · have hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega
    rw [hm', ha₆.hslot (by decide), ho₅.word (.inl (by omega)) (by omega), ha₄.hslot (by decide),
      r₃.word_eq hrm (by omega), ho₂.word (.inl (by omega)) (by omega), r₁.word_eq hrm (by omega)]

/-- `n`'s values after a write to another of its arrays. -/
theorem NVals.of_outsideArr {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N j n : Nat}
    (h : NVals s B w minv N) (ho : Outside B (slot w j) n s.mem t.mem) (hj : j < 8) (h1 : j ≠ Public.aN)
    (h2 : j ≠ Public.aR2) (h3 : j ≠ Public.aOne) (hn : n ≤ 8 * (w + 2)) (hz : B.toNat + slot w 8 ≤ 2 ^ 64) :
    NVals t B w minv N := by
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  have l1 := slot_le (w := w) (show Public.aN < 8 by decide)
  have l2 := slot_le (w := w) (show Public.aR2 < 8 by decide)
  have l3 := slot_le (w := w) (show Public.aOne < 8 by decide)
  have lj := slot_le (w := w) hj
  exact ⟨by rw [ho.wv (by omega) (by omega)]; exact h.n,
    by rw [ho.word (by omega) (by omega)]; exact h.inv,
    by rw [ho.wv (by omega) (by omega)]; exact h.r2, by rw [ho.wv (by omega) (by omega)]; exact h.r2lt,
    by rw [ho.wv (by omega) (by omega)]; exact h.one⟩

theorem Good.of_outsideArr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {j n : Nat}
    (h : Good s B Z w minv) (ho : Outside B (slot w j) n s.mem t.mem) (hk : Keep mmRegs s t) :
    Good t B Z w minv := by
  have hn := h.scr.nowrap
  have hh : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot w j hi; omega)) (by have := hdr_lt_slot w j hi; omega)
  exact ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, (hh _ (by decide)).trans h.hdr.hw,
    (hh _ (by decide)).trans h.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩


/-- `n`'s header and the arrays but `aAcc`, `aTmp`, `aY` and `aX`, and both primes' workspaces: what
`pre` may change (it changes only the primes' workspaces). -/
def preRanges (w op wp oq wq : Nat) : List (Nat × Nat) :=
  gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange oq wq, xRange op wp]

/-- A prime's values after a change on either side of its workspace. -/
theorem XVals.of_disj {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (h : XVals s B o wx mx X) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  have hN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have hd : ∀ d n, d + n ≤ slot wx 8 → ∀ r ∈ rs, o + d + n ≤ r.1 ∨ r.1 + r.2 ≤ o + d := fun d n hd r h' => by
    rcases hr r h' with h | h <;> omega
  exact ⟨by rw [wv_off, hf.wv_eq (hd _ _ (by omega)) (by omega), ← wv_off]; exact h.n,
    by rw [word_off, hf.word_eq (fun r h' => by have := hd (slot wx Public.aN) 8 (by omega) r h'; omega)
      (by omega), ← word_off]; exact h.inv,
    by rw [wv_off, hf.wv_eq (hd _ _ (by omega)) (by omega), ← wv_off]; exact h.one⟩

theorem _root_.VG.Proof.Bignum.WsAt.of_disj {m m' : Mem} {B : Addr} {o wx : Nat} {mx : BitVec 64} {rs : List (Nat × Nat)}
    (h : WsAt m B o wx mx) (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + 8 * 17 ≤ r.1)
    (ho : o + 8 * 17 ≤ 2 ^ 64) : WsAt m' B o wx mx :=
  h.of_words fun i hi => by
    rw [word_off, word_off]
    exact hf.word_eq (fun r h' => by rcases hr r h' with h | h <;> omega) (by omega)

theorem wvX_disj {m m' : Mem} {B : Addr} {o wx j : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) (hj : j < 8) :
    wv m' (off B o) (slot wx j) wx = wv m (off B o) (slot wx j) wx := by
  have := slot_le (w := wx) hj
  rw [wv_off, wv_off]
  exact hf.wv_eq (fun r h' => by rcases hr r h' with h | h <;> omega) (by omega)

theorem gRanges_lt (w : Nat) : ∀ r ∈ gRanges w, 8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

/-- `n`'s header words but `sD` and `sCnt` are kept by a change within `gRanges` and above. -/
theorem gRanges_hdr {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)}
    (hf : Frm B (gRanges w ++ rs) m m') (hr : ∀ r ∈ rs, hdrBytes ≤ r.1) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD)
    (h2 : i ≠ Public.sCnt) (hz : 8 * i + 8 ≤ 2 ^ 64) : word m' B (8 * i) = word m B (8 * i) :=
  hf.word_eq (fun r hr' => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · have := hdr_lt_slot w Public.aAcc hi
      have := hdr_lt_slot w Public.aTmp hi
      have := hdr_lt_slot w Public.aY hi
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
        unfold Crt.sD sFn at h1 ⊢; omega
      · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
        unfold Public.sCnt sFn at h2 ⊢; omega
    · exact Or.inl (by have := hr r hr'; unfold hdrBytes at this; omega)) hz

/-- An array of `n` but `aAcc`, `aTmp`, `aY` is kept by a change within `gRanges` and above. -/
theorem gRanges_arr {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)}
    {j : Nat} (hf : Frm B (gRanges w ++ rs) m m') (hr : ∀ r ∈ rs, slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j)
    (hj : j < 8)
    (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY) (hz : slot w 8 ≤ 2 ^ 64) :
    wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  exact hf.wv_eq (fun r hr' => by
    rcases List.mem_append.mp hr' with hr' | hr'
    · simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
      have := slot_sep (w := w) h1
      have := slot_sep (w := w) h2
      have := slot_sep (w := w) h3
      have := hdr_lt_slot w j (show Crt.sD < 32 by decide)
      have := hdr_lt_slot w j (show Public.sCnt < 32 by decide)
      rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega
    · exact hr r hr') (by omega)

/-- A prime's part of `pre`'s result: `R_X` in its `aY`, `x R_X` in its `aXc`. -/
structure PrimeRdy (t : State) (B : Addr) (o wx : Nat) (mx : BitVec 64) (N X C : Nat) : Prop where
  ws : WsAt t.mem B o wx mx
  x : XVals t B o wx mx X
  ylt : wv t.mem (off B o) (slot wx Public.aY) wx < X
  yv : X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X
  clt : wv t.mem (off B o) (slot wx aXc) wx < X
  cv : X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X

theorem PrimeRdy.of_disj {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {N X C : Nat}
    {rs : List (Nat × Nat)} (h : PrimeRdy s B o wx mx N X C) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) :
    PrimeRdy t B o wx mx N X C := by
  have h17 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine ⟨h.ws.of_disj hf (fun r hr' => by rcases hr r hr' with h | h <;> omega) (by omega),
    h.x.of_disj hf hr ho, ?_, fun hd => ?_, ?_, fun hd => ?_⟩
  · rw [wvX_disj hf hr ho (by decide)]; exact h.ylt
  · rw [wvX_disj hf hr ho (by decide)]; exact h.yv hd
  · rw [wvX_disj hf hr ho (by decide)]; exact h.clt
  · rw [wvX_disj hf hr ho (by decide)]; exact h.cv hd

/-- `pre`: both primes ready; only their workspaces change. -/
theorem pre_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {N P Q C op wp oq : Nat}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hpq : op + slot wp 8 + tabBytes wp ≤ oq) (hoq : oq + slot wp 8 + tabBytes wp ≤ Z) (hwp2 : 2 ≤ wp)
    (hw2 : w = 2 * wp) (hsp : word s.mem B (8 * sWsP) = off B op) (hsq : word s.mem B (8 * sWsQ) = off B oq)
    (hwsp : WsAt s.mem B op wp mp) (hwsq : WsAt s.mem B oq wp mq) (hN : NVals s B w minv N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hP : XVals s B op wp mp P) (hP1 : 1 < P) (hPodd : P % 2 = 1)
    (hQ : XVals s B oq wp mq Q) (hQ1 : 1 < Q) (hQodd : Q % 2 = 1) :
    WP isa (seqs (CrtIfma.pre M.mm)) s fun t => Good t B Z w minv ∧ NVals t B w minv N ∧
      PrimeRdy t B op wp mp N P C ∧ PrimeRdy t B oq wp mq N Q C ∧
      Frm B (preRanges w op wp oq wp) s.mem t.mem ∧ Keep mmRegs s t ∧
      word t.mem (off B op) (8 * sMaskX) = word s.mem (off B op) (8 * sMaskX) := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hmk : 8 * sMaskX + 8 ≤ slot wp 8 := by unfold sMaskX sFn; omega
  -- `q`.
  refine wp_seqs_append (by simp [CrtIfma.prep]) (by simp [CrtIfma.prep]) (WP.mono (prep_ok (C := C) M hg hw28
    (by omega) hoq hwp2 hw2 (by decide) hsq hwsq hN hXm hQ hQ1 hQodd)
    fun s₁ ⟨hg₁, hwsq₁, hQ₁, hqy, hqyv, hqx, hqxv, fQ, kQ, _⟩ => ?_)
  have ho64 : oq < 2 ^ 64 := by omega
  have hb : ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := fun d hd => fQ.x_below hd ho64
  have hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega)
  have hN₁ : NVals s₁ B w minv N := hN.of_frm (fQ.mono fun r hr => List.mem_append_right _ hr) (by omega) hz
    (by omega)
  have hXm₁ : wv s₁.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    wv_congr fun i hi => hb _ (by have := slot_le (w := w) (show Public.aXm < 8 by decide); omega)
  -- `p`.
  refine WP.mono (prep_ok (C := C) M hg₁ hw28 hlo (by omega) hwp2 hw2 (by decide)
    (by rw [hb _ (by unfold sWsP sFn; omega)]; exact hsp)
    (hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega)) hN₁
    (by rw [hXm₁]; exact hXm) (hP.of_disj fQ hQd (by omega)) hP1 hPodd)
    fun t ⟨hgt, hwspt, hPt, hpy, hpyv, hpx, hpxv, fP, kP, mkP⟩ => ?_
  have hPd : ∀ r ∈ [xRange op wp], r.1 + r.2 ≤ oq ∨ oq + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega)
  refine ⟨hgt, hN₁.of_frm (fP.mono fun r hr => List.mem_append_right _ hr) hlo hz (by omega),
    ⟨hwspt, hPt, hpy, hpyv, hpx, hpxv⟩,
    PrimeRdy.of_disj ⟨hwsq₁, hQ₁, hqy, hqyv, hqx, hqxv⟩ fP hPd (by omega),
    (fQ.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [preRanges]).trans
      (fP.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [preRanges]),
    kQ.trans kP |>.mono (by simp [mmRegs]), ?_⟩
  rw [mkP, word_off, word_off, fQ.word_eq (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega)]

end VG.Proof.Bignum.X86_64
