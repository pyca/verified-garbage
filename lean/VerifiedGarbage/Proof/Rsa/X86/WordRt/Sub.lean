module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Sub
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Ptr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # `WordModRt` on i686: `t = r 2^32 + u - q̂ m`

`mulSub` over `W' + 1` words, for the digit `u` in the header (`oDig`):
word 0 is `u - lo(q̂ m₀)` (`subHead_ok`), the words up to `W' - 1`
`R2Words`' `subBody` (`subLoop_ok`), and word `W'` `r[W' - 1] - c`
(`subFinal_ok`), so that `t + q̂ m = u + r 2^32 + 2^(32 (W' + 1)) b`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Impl.Rsa.X86.WordModRt (oQ oDig h0)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem oQ_val : oQ = 76 := rfl
theorem oDig_val : oDig = 92 := rfl

/-- Word 0 of `mulSub`, with `ebx` at `m₀` (`a`), `ebp` at `t₀` (`tt`), `q̂` in `ecx` and the
digit `u` at `oDig`: `t₀ + q̂ m₀ = u + 2^32 c` for the carry `c` in `t₁`; then `ebx` and `ebp`
a word on and `edi = 4 (W' - 1)`. -/
theorem subHead_ok {t : State} {is : List Instr} {Q : State → Prop} {bytes ml a' a tt : Nat}
    (ws : Ws t B bytes) (di : PtrAt t B .edi 0) (pb : PtrAt t B .ebx a) (pp : PtrAt t B .ebp tt)
    (ha : a + 4 ≤ bytes) (ht : tt + 8 ≤ bytes) (hdig : oDig + 4 ≤ tt) (hm : MLen t B bytes ml a') (hl : 1 ≤ a')
    (kk : ∀ t', w32 t'.mem B tt + (t.gpr .ecx).toNat * w32 t.mem B a =
        w32 t.mem B oDig + 2 ^ 32 * w32 t'.mem B (tt + 4) →
      Outside B tt 8 t.mem t'.mem → PtrAt t' B .ebx (a + 4) → PtrAt t' B .ebp (tt + 4) →
      t'.gpr .edi = BitVec.ofNat 32 (4 * wq a' - 4) → Keeps [.eax, .ebx, .edx, .ebp, .edi] t t' →
      WP isa (.block is) t' Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.subHead ml ++ is)) t Q := by
  have nw := ws.nowrap
  simp only [VG.Impl.Rsa.X86.WordModRt.subHead, List.append_assoc, List.cons_append]
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun t₁ U₁ _ => wp_mul fun t₂ U₂ => ?_
  have ws₂ := ws.of_wr (U₂.wr.trans U₁.wr)
  have pp₂ : PtrAt t₂ B .ebp tt := by rw [PtrAt, U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact pp
  have di₂ : PtrAt t₂ B .edi 0 := by rw [PtrAt, U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact di
  refine wp_storeS (ea_ptr ws₂ pp₂ (d := 4) (by omega)) (ws_write ws₂ (by omega)) fun t₃ M₃ => ?_
  have ws₃ := ws₂.of_wr M₃.wr
  have di₃ : PtrAt t₃ B .edi 0 := by rw [PtrAt, M₃.gpr]; exact di₂
  have rdig := readSrc_ptr ws₃ di₃ (d := oDig) (by rw [oDig_val] at hdig ⊢; omega)
  rw [Nat.zero_add] at rdig
  refine wp_movS rdig fun t₄ U₄ _ => wp_subS rfl fun t₅ U₅ c₅ => ?_
  have ws₅ := ws₃.of_wr (U₅.wr.trans U₄.wr)
  have pp₅ : PtrAt t₅ B .ebp tt := by rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), M₃.gpr]; exact pp₂
  refine wp_storeS (ea_ptr ws₅ pp₅ (d := 0) (by omega)) (ws_write ws₅ (by omega)) fun t₆ M₆ => ?_
  refine wp_sbbS rfl (by rw [M₆.cf]; exact c₅) fun t₇ U₇ _ => ?_
  have ws₇ := ws₅.of_wr (U₇.wr.trans M₆.wr)
  have pp₇ : PtrAt t₇ B .ebp tt := by rw [PtrAt, U₇.other _ (by decide), M₆.gpr]; exact pp₅
  refine wp_movS (readSrc_ptr ws₇ pp₇ (d := 4) (by omega)) fun t₈ U₈ _ => wp_subS rfl fun t₉ U₉ _ => ?_
  have ws₉ := ws₇.of_wr (U₉.wr.trans U₈.wr)
  have pp₉ : PtrAt t₉ B .ebp tt := by rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide)]; exact pp₇
  refine wp_storeS (ea_ptr ws₉ pp₉ (d := 4) (by omega)) (ws_write ws₉ (by omega)) fun t₁₀ M₁₀ => ?_
  have K₁₀ : Keeps [.eax, .edx] t t₁₀ :=
    ((((U₁.keeps.mono (by decide)).trans U₂.keeps).trans (M₃.keeps _)).trans
      (((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans (M₆.keeps _))).trans
      (((U₇.keeps.mono (by decide)).trans (U₈.keeps.mono (by decide))).trans
      ((U₉.keeps.mono (by decide)).trans (M₁₀.keeps _)))
  -- The values.
  have hA : (t₁.gpr .eax).toNat = w32 t.mem B a := by rw [U₁.gpr, Nat.add_zero]
  have hq : t₁.gpr .ecx = t.gpr .ecx := U₁.other _ (by decide)
  have lo : (t₂.gpr .eax).toNat = w32 t.mem B a * (t.gpr .ecx).toNat % 2 ^ 32 := by
    rw [U₂.eax, hA, hq, BitVec.toNat_ofNat]
  have hb := (mul_words (t.mem.readW (off B a) 32) (t.gpr .ecx)).2
  have hi : (t₂.gpr .edx).toNat = w32 t.mem B a * (t.gpr .ecx).toNat / 2 ^ 32 := by
    rw [U₂.edx, hA, hq, BitVec.toNat_ofNat]; simp only [w32] at *; omega
  have m₃ : t₃.mem = t.mem.writeW (off B (tt + 4)) (t₂.gpr .edx) := by rw [M₃.mem, U₂.mem, U₁.mem]
  have dg : (t₄.gpr .edx).toNat = w32 t.mem B oDig := by
    rw [U₄.gpr, m₃]
    change w32 _ B oDig = _
    rw [w32_write_ne (size := bytes) nw (by omega) (by rw [oDig_val] at hdig ⊢; omega) (by omega)]
  generalize hu : w32 t.mem B oDig = u at dg
  have hu32 : u < 2 ^ 32 := by rw [← hu]; exact (t.mem.readW _ 32).isLt
  have b₇ : (t₇.gpr .eax).toNat = if u < w32 t.mem B a * (t.gpr .ecx).toNat % 2 ^ 32 then 2 ^ 32 - 1 else 0 := by
    rw [U₇.gpr, VG.Proof.Bignum.X86.R2Words.sbb_self, U₄.other .eax (by decide), M₃.gpr, dg, lo]
    by_cases e : u < w32 t.mem B a * (t.gpr .ecx).toNat % 2 ^ 32
    · rw [ite_eq_left (by simp only [decide_eq_true_eq]; exact e), ite_eq_left e]
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact e), ite_eq_right e]
  have t₀ : (t₅.gpr .edx).toNat = (2 ^ 32 - w32 t.mem B a * (t.gpr .ecx).toNat % 2 ^ 32 + u) % 2 ^ 32 := by
    rw [U₅.gpr, BitVec.toNat_sub, dg, U₄.other .eax (by decide), M₃.gpr, lo]
  have m₆ : t₆.mem = t₃.mem.writeW (off B tt) (t₅.gpr .edx) := by rw [M₆.mem, U₅.mem, U₄.mem, Nat.add_zero]
  have hi₈ : t₈.gpr .edx = t₂.gpr .edx := by
    rw [U₈.gpr, U₇.mem, m₆]
    apply BitVec.eq_of_toNat_eq
    change w32 _ B (tt + 4) = _
    rw [w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega), m₃, w32_write_self]
  have c₉ : (t₉.gpr .edx).toNat = w32 t.mem B a * (t.gpr .ecx).toNat / 2 ^ 32 +
      (if u < w32 t.mem B a * (t.gpr .ecx).toNat % 2 ^ 32 then 1 else 0) := by
    rw [U₉.gpr, BitVec.toNat_sub, U₈.other .eax (by decide), b₇, hi₈, hi]
    by_cases e : u < w32 t.mem B a * (t.gpr .ecx).toNat % 2 ^ 32
    · simp only [e, ↓reduceIte]; simp only [w32] at *; omega
    · simp only [e, ↓reduceIte]; simp only [w32] at *; omega
  have m₁₀ : t₁₀.mem = (t₃.mem.writeW (off B tt) (t₅.gpr .edx)).writeW (off B (tt + 4)) (t₉.gpr .edx) := by
    rw [M₁₀.mem, U₉.mem, U₈.mem, U₇.mem, m₆]
  have O₁₀ : Outside B tt 8 t.mem t₁₀.mem := by
    rw [m₁₀, m₃]
    exact (((writeW32_outside _ B _ (d := tt + 4) (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ B _ (d := tt) (by omega)).mono (by omega) (by omega))).trans
      ((writeW32_outside _ B _ (d := tt + 4) (by omega)).mono (by omega) (by omega))
  have hm₁₀ := hm.keep K₁₀ (by decide) (O₁₀.mono (by omega) (by omega))
  refine width4_ok hm₁₀ fun u' Ku mu eu => ?_
  refine wp_subS rfl fun u₁ V₁ _ => wp_addS rfl fun u₂ V₂ _ => wp_addS rfl fun u₃ V₃ _ => ?_
  have pb₁₀ : PtrAt t₁₀ B .ebx a := by
    rw [PtrAt, K₁₀.1 _ (by decide)]; exact pb
  have pp₁₀ : PtrAt t₁₀ B .ebp tt := by rw [PtrAt, M₁₀.gpr]; exact pp₉
  have hw : 1 ≤ wq a' := by simp only [wq]; omega
  have hw' : 4 * wq a' < 2 ^ 32 := by have := hm.le; simp only [wq]; omega
  refine kk u₃ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [V₃.mem, V₂.mem, V₁.mem, mu, m₁₀, w32_write_ne (size := bytes) nw (by omega) (by omega) (by omega),
      w32_write_self, w32_write_self, t₀, c₉, Nat.mul_comm (t.gpr .ecx).toNat, hu]
    simp only [w32] at *
    generalize (t.mem.readW (off B a) 32).toNat * (t.gpr .ecx).toNat = P at *
    split <;> omega
  · rw [V₃.mem, V₂.mem, V₁.mem, mu]; exact O₁₀
  · rw [PtrAt, V₃.other _ (by decide), V₂.gpr, V₁.other _ (by decide), Ku.1 _ (by decide), ptr_add pb₁₀]; rfl
  · rw [PtrAt, V₃.gpr, V₂.other _ (by decide), V₁.other _ (by decide), Ku.1 _ (by decide), ptr_add pp₁₀]; rfl
  · rw [V₃.other _ (by decide), V₂.other _ (by decide), V₁.gpr, eu]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  · exact (K₁₀.mono (by decide)).trans ((Ku.mono (by decide)).trans
      (((V₁.keeps.mono (by decide)).trans (V₂.keeps.mono (by decide))).trans (V₃.keeps.mono (by decide))))

/-- After words `0, …, j - 1` of `mulSub` from `s`, for `q̂ = q` in `ecx` and the digit `u`: the
words `T_j` of `t` (at `to`) and the carry `c` in `t[j]`:
`T_j + q m_j = u + r_(j-1) 2^32 + 2^(32 j) c`, for `m` at `mo` and `r` at `xo`. -/
structure SubI (s : State) (B : Addr) (mo xo to W q u j : Nat) (v : State) : Prop where
  bx : PtrAt v B .ebx (mo + 4 * j)
  si : PtrAt v B .esi (xo + 4 * (j - 1))
  bp : PtrAt v B .ebp (to + 4 * j)
  di : v.gpr .edi = BitVec.ofNat 32 (4 * (W - j))
  cx : v.gpr .ecx = BitVec.ofNat 32 q
  qlt : q < 2 ^ 32
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s v
  out : Outside B to (4 * (j + 1)) s.mem v.mem
  val : val32 v.mem B to j + q * val32 s.mem B mo j =
    u + val32 s.mem B xo (j - 1) * 2 ^ 32 + 2 ^ (32 * j) * w32 v.mem B (to + 4 * j)

/-- Where `mulSub`'s numbers are: `m` and `r` of `W` words and `t` of `W + 1`, `t` apart from both. -/
structure SubGeo (B : Addr) (bytes mo xo to W : Nat) : Prop where
  nw : B.toNat + bytes ≤ 2 ^ 32
  m : mo + 4 * W ≤ bytes
  x : xo + 4 * W ≤ bytes
  t : to + 4 * (W + 1) ≤ bytes
  mt : mo + 4 * W ≤ to ∨ to + 4 * (W + 1) ≤ mo
  xt : xo + 4 * W ≤ to ∨ to + 4 * (W + 1) ≤ xo
  w2 : 2 ≤ W

/-- The arithmetic of a word of `mulSub`. -/
theorem subStepD_val {T q M Y G t' A C c' Xw : Nat}
    (hI : T + q * M = Y + G * 2 ^ 32 * C) (hv : t' + q * A + C = Xw + 2 ^ 32 * c') :
    T + G * 2 ^ 32 * t' + q * (M + G * 2 ^ 32 * A) = Y + G * 2 ^ 32 * Xw + G * 2 ^ 32 * 2 ^ 32 * c' := by
  have e := congrArg (G * 2 ^ 32 * ·) hv
  simp only [Nat.mul_add] at e
  grind

/-- A word of `mulSub`'s loop. -/
theorem subStep_ok {s v : State} {bytes mo xo to W q u j : Nat} (ws : Ws s B bytes) (g : SubGeo B bytes mo xo to W)
    (hj1 : 1 ≤ j) (hj : j < W) (I : SubI s B mo xo to W q u j v) :
    WP isa (.block VG.Impl.Bignum.X86.R2Words.subBody) v fun v' => v'.zf = some (decide (j + 1 = W)) ∧
      SubI s B mo xo to W q u (j + 1) v' := by
  have nw := g.nw
  have gm := g.m; have gx := g.x; have gt := g.t; have gmt := g.mt; have gxt := g.xt
  have wsv : Ws v B bytes := ws.of_wr I.keep.2.2
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.subBody_ok wsv I.bx I.si I.bp (by omega) (by omega) (by omega)
    (by omega)) fun v' ⟨hv, O', pb', ps', pp', di', z', K'⟩ => ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := W) (x := v.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  refine ⟨by rw [z', hc.2], ⟨?_, ?_, ?_, ?_, ?_, I.qlt, I.keep.trans (K'.mono (by decide)), ?_, ?_⟩⟩
  · rw [show mo + 4 * (j + 1) = mo + 4 * j + 4 by omega]; exact pb'
  · rw [show xo + 4 * (j + 1 - 1) = xo + 4 * (j - 1) + 4 by omega]; exact ps'
  · rw [show to + 4 * (j + 1) = to + 4 * j + 4 by omega]; exact pp'
  · apply BitVec.eq_of_toNat_eq
    rw [di', hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [K'.1 _ (by decide)]; exact I.cx
  · exact (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  · have hA : w32 v.mem B (mo + 4 * j) = w32 s.mem B (mo + 4 * j) := I.out.w32 (by omega) (by omega)
    have hX : w32 v.mem B (xo + 4 * (j - 1)) = w32 s.mem B (xo + 4 * (j - 1)) := I.out.w32 (by omega) (by omega)
    have hT : val32 v'.mem B to j = val32 v.mem B to j := O'.val32 (.inl (by omega)) (by omega)
    have hq : (v.gpr .ecx).toNat = q := by rw [I.cx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt I.qlt]
    rw [hA, hX, hq] at hv
    rw [val32_succ, val32_succ, hT, show j + 1 - 1 = (j - 1) + 1 by omega, val32_succ,
      show 32 * (j + 1) = 32 * (j - 1) + 32 + 32 by omega, show 32 * j = 32 * (j - 1) + 32 by omega,
      show to + 4 * (j + 1) = to + 4 * j + 4 by omega, Nat.pow_add, Nat.pow_add]
    have hI := I.val
    rw [show 32 * j = 32 * (j - 1) + 32 by omega, Nat.pow_add] at hI
    have e := subStepD_val hI hv
    grind

/-- `mulSub`'s loop: words `1, …, W - 1`. -/
theorem subLoop_ok {s v : State} {bytes mo xo to W q u : Nat} (ws : Ws s B bytes) (g : SubGeo B bytes mo xo to W)
    (I : SubI s B mo xo to W q u 1 v) :
    WP isa (.loop (.block VG.Impl.Bignum.X86.R2Words.subBody) .ne) v fun v' => SubI s B mo xo to W q u W v' := by
  have hw := g.w2
  refine WP.loop (M := isa) (fun n v => ∃ j, n = W - j ∧ 1 ≤ j ∧ j < W ∧ SubI s B mo xo to W q u j v) ?_ _ v
    ⟨1, rfl, Nat.le_refl _, by omega, I⟩
  rintro n v ⟨j, rfl, hj1, hj, I⟩
  refine WP.mono (subStep_ok ws g hj1 hj I) fun v' ⟨z, I'⟩ => ?_
  by_cases e : j + 1 = W
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], W - (j + 1),
      by omega, j + 1, rfl, by omega, by omega, I'⟩

/-- Word `W'` of `mulSub`, with `esi` at `r[W' - 1]` (`xx`) and `ebp` at `t[W']` (`tt`), holding
the carry: `t[W'] + c = r[W' - 1] + 2^32 b`; and `edi` set back. -/
theorem subTop_ok {t : State} {bytes xx tt : Nat} {v : BitVec 32} (ws : Ws t B bytes)
    (ps : PtrAt t B .esi xx) (pp : PtrAt t B .ebp tt) (hx : xx + 4 ≤ bytes) (ht : tt + 4 ≤ bytes)
    (ca : CallArgument t B bytes L.ws v) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.subTop L)) t fun t' => ∃ b, b < 2 ∧
      w32 t'.mem B tt + w32 t.mem B tt = w32 t.mem B xx + 2 ^ 32 * b ∧
      t'.mem = t.mem.writeW (off B tt) (BitVec.ofNat 32 (w32 t'.mem B tt)) ∧
      t'.gpr .edi = v ∧ Keeps [.edx, .edi] t t' := by
  have nw := ws.nowrap
  simp only [VG.Impl.Rsa.X86.WordModRt.subTop, restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr ws ps (d := 0) (by omega)) fun t₁ U₁ _ => ?_
  have pp₁ : PtrAt t₁ B .ebp tt := by rw [PtrAt, U₁.other _ (by decide)]; exact pp
  have ws₁ := ws.of_wr U₁.wr
  refine wp_subS (readSrc_ptr ws₁ pp₁ (d := 0) (by omega)) fun t₂ U₂ _ => ?_
  have pp₂ : PtrAt t₂ B .ebp tt := by rw [PtrAt, U₂.other _ (by decide)]; exact pp₁
  have ws₂ := ws₁.of_wr U₂.wr
  refine wp_storeS (ea_ptr ws₂ pp₂ (d := 0) (by omega)) (ws_write ws₂ (by omega)) fun t₃ M₃ => ?_
  have K₃ : Keeps [.edx, .edi] t t₃ := ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (M₃.keeps _)
  have m₃ : t₃.mem = t.mem.writeW (off B tt) (t₂.gpr .edx) := by rw [M₃.mem, U₂.mem, U₁.mem, Nat.add_zero]
  have O₃ : Outside B 0 bytes t.mem t₃.mem := by
    rw [m₃]; exact (writeW32_outside _ B _ (d := tt) (by omega)).mono (by omega) (by omega)
  refine wp_movS (ca.keep K₃ (by decide) O₃).readSrc fun t₄ U₄ _ => WP.block_nil ?_
  have e₂ : (t₂.gpr .edx).toNat = (2 ^ 32 - w32 t.mem B tt + w32 t.mem B xx) % 2 ^ 32 := by
    rw [U₂.gpr, BitVec.toNat_sub, U₁.gpr, U₁.mem, Nat.add_zero, Nat.add_zero]
  have hw : w32 t₄.mem B tt = (t₂.gpr .edx).toNat := by rw [U₄.mem, m₃, w32_write_self]
  have hc : w32 t.mem B tt < 2 ^ 32 := (t.mem.readW (off B tt) 32).isLt
  have hxl : w32 t.mem B xx < 2 ^ 32 := (t.mem.readW (off B xx) 32).isLt
  refine ⟨if w32 t.mem B xx < w32 t.mem B tt then 1 else 0, by split <;> omega, ?_, ?_, U₄.gpr,
    K₃.trans (U₄.keeps.mono (by decide))⟩
  · rw [hw, e₂]; split <;> omega
  · rw [hw, BitVec.ofNat_toNat, BitVec.setWidth_eq, U₄.mem, m₃]

theorem subFinalD_val {mt mu ms : Mem} {T M X q W b u : Nat} (hW : 1 ≤ W)
    (hT : val32 mt B T W = val32 mu B T W)
    (hI : val32 mu B T W + q * val32 ms B M W =
      u + val32 ms B X (W - 1) * 2 ^ 32 + 2 ^ (32 * W) * w32 mu B (T + 4 * W))
    (hv : w32 mt B (T + 4 * W) + w32 mu B (T + 4 * W) = w32 ms B (X + 4 * (W - 1)) + 2 ^ 32 * b) :
    val32 mt B T (W + 1) + q * val32 ms B M W = u + val32 ms B X W * 2 ^ 32 + 2 ^ (32 * (W + 1)) * b := by
  obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hI hv
  rw [val32_succ mt B T (k + 1), hT, val32_succ ms B X k, show 32 * (k + 1 + 1) = 32 * k + 32 + 32 by omega,
    show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, Nat.pow_add]
  rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add] at hI
  have e := congrArg (2 ^ (32 * k) * 2 ^ 32 * ·) hv
  simp only [Nat.mul_add] at e
  grind

/-- `mulSub ml r m t`: `t = r 2^32 + u - q̂ m` over `W' + 1` words, for `q̂` at `oQ` and the
digit `u` at `oDig`: `t + q̂ m = u + r 2^32 + 2^(32 (W' + 1)) b`, over `m`'s and `r`'s `W'` words. -/
theorem mulSub_ok {s : State} (h : RtWs L s B Z len N) {ml a r m t : Nat} (hm : MLen s B Z ml a)
    (hr : r < N) (hmN : m < N) (ht : t < N) (hrt : r ≠ t) (hmt : m ≠ t) (h2 : 2 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulSub L ml r m t) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [t] [] s.mem v.mem ∧
      (∃ b, b < 2 ∧ val32 v.mem B (arr (kw len) t) (wq a + 1) + slot s.mem B oQ * val32 s.mem B (arr (kw len) m) (wq a) =
        slot s.mem B oDig + val32 s.mem B (arr (kw len) r) (wq a) * 2 ^ 32 + 2 ^ (32 * (wq a + 1)) * b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fr := h.ws.arr_fit hr
  have fm := h.ws.arr_fit hmN
  have ft := h.ws.arr_fit ht
  have hdr := h.ws.hdr_le
  simp only [S] at fr fm ft
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have ws := h.rt
  have sep : ∀ {i j : Nat}, i ≠ j → arr (kw len) i + 4 * (kw len + 2) ≤ arr (kw len) j ∨
      arr (kw len) j + 4 * (kw len + 2) ≤ arr (kw len) i := fun hij => by
    have := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hij; simpa only [S] using this
  have g : SubGeo B Z (arr (kw len) m) (arr (kw len) r) (arr (kw len) t) (wq a) :=
    ⟨nw, by omega, by omega, by omega, by have := sep hmt; omega, by have := sep hrt; omega, h2⟩
  have tdig : oDig + 4 ≤ arr (kw len) t := by rw [oDig_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  obtain ⟨q, hq⟩ : ∃ q, q = slot s.mem B oQ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = slot s.mem B oDig := ⟨_, rfl⟩
  rw [← hq, ← hu]
  unfold VG.Impl.Rsa.X86.WordModRt.mulSub
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs, VG.Impl.Rsa.X86.WordModRt.subPtrs, List.append_assoc,
    List.cons_append, List.nil_append]
  refine WP.seq (arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := m) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_)
  have edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok ((lenSrc h).keep K₁ (by decide) m₁) h.lenLe edi₁ (r := .esi) (t := .edx) (j := r) (by decide)
    (by decide) (by omega) fun u₂ K₂ m₂ p₂ _ => ?_
  have edi₂ : (u₂.gpr .edi).toNat = B.toNat := by rw [K₂.1 _ (by decide)]; exact edi₁
  refine arrPtr_ok (((lenSrc h).keep K₁ (by decide) m₁).keep K₂ (by decide) m₂) h.lenLe edi₂ (r := .ebp) (t := .edx)
    (j := t) (by decide) (by decide) (by omega) fun u₃ K₃ m₃ p₃ _ => ?_
  have K₁₃ : Keeps [.ebx, .edx, .esi, .ebp] s u₃ := ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
    (K₃.mono (by decide))
  have m₁₃ : u₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have di₃ : PtrAt u₃ B .edi 0 := by
    rw [PtrAt, K₁₃.1 _ (by decide), h.edi, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have rq := readSrc_ptr (ws.of_keeps K₁₃) di₃ (d := oQ) (by rw [oQ_val]; omega)
  rw [Nat.zero_add] at rq
  refine wp_movS rq fun u₄ U₄ _ => ?_
  have K₁₄ : Keeps [.ebx, .ecx, .edx, .esi, .ebp] s u₄ := (K₁₃.mono (by decide)).trans (U₄.keeps.mono (by decide))
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, m₁₃]
  have pb₄ : PtrAt u₄ B .ebx (arr (kw len) m) := by
    rw [PtrAt, U₄.other _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
  have ps₄ : PtrAt u₄ B .esi (arr (kw len) r) := by
    rw [PtrAt, U₄.other _ (by decide), K₃.1 _ (by decide)]; exact p₂
  have pp₄ : PtrAt u₄ B .ebp (arr (kw len) t) := by rw [PtrAt, U₄.other _ (by decide)]; exact p₃
  have di₄ : PtrAt u₄ B .edi 0 := by rw [PtrAt, U₄.other _ (by decide)]; exact di₃
  have hq32 : q < 2 ^ 32 := by rw [hq]; exact (s.mem.readW _ 32).isLt
  have q₄ : u₄.gpr .ecx = BitVec.ofNat 32 q := by
    apply BitVec.eq_of_toNat_eq
    rw [U₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32, hq, m₁₃]
  have hm₄ : MLen u₄ B Z ml a := hm.keep K₁₄ (by decide) (by rw [m₄]; exact Outside.refl _ _ _ _)
  rw [← List.append_nil (VG.Impl.Rsa.X86.WordModRt.subHead ml)]
  refine subHead_ok (ws.of_keeps K₁₄) di₄ pb₄ pp₄ (by omega) (by omega) tdig hm₄ (by simp only [wq] at h2; omega)
    fun v hv O pb pp di K => WP.block_nil ?_
  have hu' : w32 s.mem B oDig = u := hu.symm
  rw [m₄, hu'] at hv
  refine WP.seq (WP.mono (subLoop_ok (u := u) (q := q) ws g ⟨by rw [Nat.mul_one]; exact pb, ?_, by rw [Nat.mul_one]; exact pp, ?_,
      by rw [K.1 _ (by decide)]; exact q₄, hq32, (K₁₄.mono (by decide)).trans (K.mono (by decide)), ?_, ?_⟩)
    fun v' I => ?_)
  · rw [PtrAt, K.1 _ (by decide), Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact ps₄
  · rw [di]; congr 1; omega
  · rw [← m₄]; exact O
  · have e1 : ∀ (mm : Mem) d, val32 mm B d 1 = w32 mm B d := fun mm d => by
      rw [show (1 : Nat) = 0 + 1 from rfl, val32_succ]; simp [val32]
    have hq' : (u₄.gpr .ecx).toNat = q := by rw [q₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq32]
    rw [hq'] at hv
    rw [e1, e1, Nat.sub_self, show val32 s.mem B (arr (kw len) r) 0 = 0 from rfl, Nat.zero_mul, Nat.add_zero,
      Nat.mul_one, Nat.mul_one]
    exact hv
  -- The top word.
  have wsv := ws.of_wr I.keep.2.2
  have ca := h.wsArg.keep I.keep (by decide) (I.out.mono (by omega) (by omega))
  refine WP.mono (subTop_ok wsv I.si I.bp (by omega) (by omega) ca) fun t' ⟨b, hb, hv', hmt', hdi, K'⟩ => ?_
  have O' := writeW32_outside v'.mem B (d := arr (kw len) t + 4 * wq a)
    (BitVec.ofNat 32 (w32 t'.mem B (arr (kw len) t + 4 * wq a))) (by omega)
  rw [← hmt'] at O'
  have Ot : Outside B (arr (kw len) t) (4 * (wq a + 1)) s.mem t'.mem :=
    (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t' :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((I.keep.trans (K'.mono (by decide))).mono (by decide)) (hdi.trans h.edi_eq.symm)
  refine ⟨h.keep Kall (by decide) (by decide) (Ot.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr (d := 0) (by simpa using Ot) (by simp only [S]; omega) (by simp), ⟨b, hb, ?_⟩, Kall⟩
  have hX : w32 v'.mem B (arr (kw len) r + 4 * (wq a - 1)) = w32 s.mem B (arr (kw len) r + 4 * (wq a - 1)) :=
    I.out.w32 (by have := sep hrt; omega) (by omega)
  have hT : val32 t'.mem B (arr (kw len) t) (wq a) = val32 v'.mem B (arr (kw len) t) (wq a) :=
    O'.val32 (.inl (by omega)) (by omega)
  rw [hX] at hv'
  exact subFinalD_val (by omega) hT I.val hv'

end VG.Proof.Rsa.X86.WordRt
