module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Ptr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Bignum.WordStepNorm32

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-!
# `R2Words` on x86: the estimate of a step's quotient

`top` leaves the top words `u₁`, `u₂` of `2^z x` in `ebp` and `eax`, and
`u₀`, `u₂` in the header, from the top four words of `x` and `p = 2^z`
(`top_ok`); `quot` the 2-by-1 estimate (`quot_ok`); `refine3` corrects it to
the 3-by-2 estimate (`quot3_ok`, `fix3_ok`, `refine3_ok`,
`WordStep32.quot3_val`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt

/-- Word `W' - i` of number `j`. -/
abbrev topW (m : Mem) (base : Addr) (len j i : Nat) : Nat := w32 m base (numAt len j + 4 * wp len - 4 * i)

theorem ofNat_add_lo (a b : Nat) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a % 2 ^ 32 + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem hi_lt (a b : BitVec 32) : a.toNat * b.toNat / 2 ^ 32 < 2 ^ 32 := by
  have := (mul_words a b).2; omega_using [this]

/-- The registers a step writes. -/
abbrev k6 : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .ebp]

theorem sbb_self (x : BitVec 32) (c : Bool) :
    (x - x - (BitVec.ofBool c).setWidth 32).toNat = if c then 2 ^ 32 - 1 else 0 := by
  rw [BitVec.sub_self]; cases c <;> rfl

theorem _root_.VG.X86.Wp.Fupd.keeps6 {s t : State} (F : Fupd s t) : Keeps k6 s t := ⟨fun _ _ => by rw [F.gpr], F.rd, F.wr⟩

/-- A mask's bits: all ones or none. -/
theorem and_mask (x : BitVec 32) (c : Prop) [Decidable c] :
    (x &&& BitVec.ofNat 32 (if c then 2 ^ 32 - 1 else 0)).toNat = if c then x.toNat else 0 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, show BitVec.ofNat 32 (2 ^ 32 - 1) = BitVec.allOnes 32 from rfl,
      BitVec.and_allOnes]
  · rw [ite_eq_right h, ite_eq_right h]; simp

/-- The words of `(v + 2^32) u + a` from those of `v u`. -/
theorem mgP_words (X u a : Nat) (ha : a < 2 ^ 32) :
    (X % 2 ^ 32 + a) % 2 ^ 32 = (X + 2 ^ 32 * u + a) % 2 ^ 32 ∧
    (X / 2 ^ 32 % 2 ^ 32 + u % 2 ^ 32 + (decide (2 ^ 32 ≤ X % 2 ^ 32 + a)).toNat) % 2 ^ 32 =
      (X + 2 ^ 32 * u + a) / 2 ^ 32 % 2 ^ 32 := by
  constructor
  · omega_using []
  · cases h : decide (2 ^ 32 ≤ X % 2 ^ 32 + a) <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega_arith

theorem ofBool_toNat (c : Prop) [Decidable c] : (decide c).toNat = if c then 1 else 0 := by
  by_cases h : c <;> simp [h]

/-- `mg_quot` with the corrections' conditions as the code computes them. -/
theorem mg_quot' {d u a P Q r Q1 r1 : Nat} (hd : d < 2 ^ 32) (hn : 2 ^ 31 ≤ d) (hu : u < d) (ha : a < 2 ^ 32)
    (hP : P = (2 ^ 64 - 1) / d * u + a) (hQ : Q = (P / 2 ^ 32 + 1) % 2 ^ 32)
    (hr : r = (a + (2 ^ 32 - Q * d % 2 ^ 32)) % 2 ^ 32)
    (hQ1 : Q1 = (Q + if P % 2 ^ 32 < r then 2 ^ 32 - 1 else 0) % 2 ^ 32)
    (hr1 : r1 = (r + if P % 2 ^ 32 < r then d else 0) % 2 ^ 32) :
    (Q1 + 0 % 2 ^ 32 + (if d - 1 < r1 then 1 else 0)) % 2 ^ 32 = (u * 2 ^ 32 + a) / d := by
  rw [Nat.zero_mod, Nat.add_zero]
  exact VG.Proof.Bignum.WordStep32.mg_quot hd hn hu ha rfl hP hQ hr hQ1 hr1

/-- `quot`: `q̂` at `h + 20` (`R2Words`' own: 180), `min(⌊(u₂ 2^32 + u₁) / d⌋, 2^32 - 1)` for `u₂ ≤ d`. -/
theorem quot_ok {h : Nat} {s : State} {base : Addr} {bytes : Nat} {u2 u1 d : Nat}
    (ws : Ws s base bytes) (di : PtrAt s base .edi 0) (hb : h + 24 ≤ bytes)
    (hax : s.gpr .eax = BitVec.ofNat 32 u2) (hbp : s.gpr .ebp = BitVec.ofNat 32 u1)
    (hD : w32 s.mem base (oD h) = d) (hV : w32 s.mem base (oV h) = (2 ^ 64 - 1) / d - 2 ^ 32)
    (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) (hu2 : u2 ≤ d) (hu1 : u1 < 2 ^ 32) :
    WP isa (.block (quot h)) s fun t =>
      w32 t.mem base (oQ h) = (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) ∧
      Outside base (oMask h) 12 s.mem t.mem ∧ w32 t.mem base (oSteps h) = w32 s.mem base (oSteps h) ∧ Keeps k6 s t := by
  have nw := ws.nowrap
  have hu2' : u2 < 2 ^ 32 := by omega_using [hd2, hu2]
  have pt : ∀ {t : State}, Keeps k6 s t → PtrAt t base .edi 0 := fun K => by rw [PtrAt, K.1 _ (by decide)]; exact di
  have wt : ∀ {t : State}, Keeps k6 s t → Ws t base bytes := fun K => ws.of_keeps K
  have rd : ∀ {t : State} (o : Nat), Keeps k6 s t → o + 4 ≤ bytes →
      readSrc t (.mem (hd o)) = some (t.mem.readW (off base o) 32) := fun o K ho => by
    have r := readSrc_ptr (wt K) (pt K) (d := o) (by omega_using [ho])
    rw [Nat.zero_add] at r; exact r
  have hd0 : 0 < d := by omega_using [hd1]
  -- The mask of `u₂ = d`.
  refine wp_movS (rd (oD h) (Keeps.refl _ _) (by simp only [oD]; omega_using [hb])) fun t₁ U₁ _ => ?_
  refine wp_subS rfl fun t₂ U₂ _ => wp_cmpi fun t₃ F₃ c₃ _ => wp_sbbS rfl c₃ fun t₄ U₄ _ => ?_
  have K₄ : Keeps k6 s t₄ := (U₁.keeps.mono (by decide)).trans (((U₂.keeps.mono (by decide)).trans F₃.keeps6).trans
    (U₄.keeps.mono (by decide)))
  have m₄ : t₄.mem = s.mem := by rw [U₄.mem, F₃.mem, U₂.mem, U₁.mem]
  have e₂ : (t₂.gpr .ecx).toNat = d - u2 := by
    rw [U₂.gpr, U₁.gpr, U₁.other _ (by decide), hax, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu2']
    change (2 ^ 32 - u2 + w32 s.mem base (oD h)) % 2 ^ 32 = _
    rw [hD]; omega_using [hd2, hu2]
  have e₄ : t₄.gpr .ecx = BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [U₄.gpr, F₃.gpr, sbb_self]
    by_cases e : u2 = d
    · rw [ite_eq_left (by rw [e₂]; simp only [decide_eq_true_eq]; show d - u2 < 1; omega_using [e]), ite_eq_left e]; rfl
    · rw [ite_eq_right (by rw [e₂]; simp only [decide_eq_true_eq]; show ¬ d - u2 < 1; omega_using [hu2, e]), ite_eq_right e]; rfl
  refine wp_storeS (ea_ptr (wt K₄) (pt K₄) (d := (oMask h)) (by simp only [oMask]; omega_using [hb]))
    (ws_write (wt K₄) (by simp only [oMask]; omega_using [hb])) fun t₅ M₅ => ?_
  refine wp_logicS (Or.inr rfl) rfl fun t₆ U₆ => wp_logicS (Or.inl rfl) rfl fun t₇ U₇ => ?_
  have K₇ : Keeps k6 s t₇ := K₄.trans (((M₅.keeps _).trans (U₆.keeps.mono (by decide))).trans (U₇.keeps.mono (by decide)))
  have m₇ : t₇.mem = s.mem.writeW (off base (0 + (oMask h))) (BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else 0)) := by
    rw [U₇.mem, U₆.mem, M₅.mem, m₄, e₄]
  -- `u = u₂` but `0` where `u₂ = d`.
  have e₇ : (t₇.gpr .eax).toNat = if u2 = d then 0 else u2 := by
    rw [U₇.gpr, ite_eq_left rfl, U₆.gpr, U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), F₃.gpr,
      U₂.other _ (by decide), U₁.other _ (by decide), hax, ite_eq_right (by decide), e₄]
    by_cases e : u2 = d
    · rw [ite_eq_left e, ite_eq_left e,
        show BitVec.ofNat 32 (2 ^ 32 - 1) ^^^ -1 = 0#32 from rfl, BitVec.and_zero]; rfl
    · rw [ite_eq_right e, ite_eq_right e, show (0#32 ^^^ -1 : BitVec 32) = BitVec.allOnes 32 from rfl,
        BitVec.and_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu2']
  -- `(q₁, q₀) = V u + u₁`.
  have hVB : 2 ^ 32 ≤ (2 ^ 64 - 1) / d := by
    rw [Nat.le_div_iff_mul_le hd0]
    have := Nat.mul_le_mul_left (2 ^ 32) (show d ≤ 2 ^ 32 - 1 by omega_using [hd2]); omega_using [hd2]
  have bp₇ : t₇.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), F₃.gpr,
      U₂.other _ (by decide), U₁.other _ (by decide), hbp]
  obtain ⟨u, hu⟩ : ∃ u, u = if u2 = d then 0 else u2 := ⟨_, rfl⟩
  rw [← hu] at e₇
  have hud : u < d := by
    by_cases e : u2 = d
    · rw [hu, ite_eq_left e]; exact hd0
    · rw [hu, ite_eq_right e]; omega_using [hu2, e]
  have hmask : ∀ k, (k + 4 ≤ (oMask h) ∨ (oMask h) + 4 ≤ k) → k + 4 ≤ 2 ^ 64 → w32 t₇.mem base k = w32 s.mem base k :=
    fun k h1 h2 => by rw [m₇, Nat.zero_add]; exact (writeW32_outside _ base _ (by simp only [oMask]; omega_using [hb, nw])).w32 h1 h2
  refine wp_movS rfl fun t₈ U₈ _ => ?_
  have K₈ : Keeps k6 s t₈ := K₇.trans (U₈.keeps.mono (by decide))
  refine wp_movS (rd (oV h) K₈ (by simp only [oV]; omega_using [hb])) fun t₉ U₉ _ => wp_mul fun t₁₀ U₁₀ => ?_
  refine wp_addS rfl fun t₁₁ U₁₁ c₁₁ => wp_adcS rfl c₁₁ fun t₁₂ U₁₂ _ => ?_
  have K₁₂ : Keeps k6 s t₁₂ := K₈.trans ((U₉.keeps.mono (by decide)).trans ((U₁₀.keeps.mono (by decide)).trans
    ((U₁₁.keeps.mono (by decide)).trans (U₁₂.keeps.mono (by decide)))))
  have m₁₂ : t₁₂.mem = t₇.mem := by rw [U₁₂.mem, U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem]
  have v₉ : (t₉.gpr .eax).toNat = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [U₉.gpr, U₈.mem]; change w32 t₇.mem base (oV h) = _
    rw [hmask (oV h) (.inl (by simp only [oV, oMask]; omega_using [])) (by simp only [oV]; omega_using [hb, nw]), hV]
  have x₉ : (t₉.gpr .ecx).toNat = u := by rw [U₉.other _ (by decide), U₈.gpr, e₇]
  have b₁₀ : t₁₀.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₁₀.other _ (by decide) (by decide), U₉.other _ (by decide), U₈.other _ (by decide), bp₇]
  obtain ⟨v, hv⟩ : ∃ v, v = (2 ^ 64 - 1) / d - 2 ^ 32 := ⟨_, rfl⟩
  rw [← hv] at v₉
  obtain ⟨P, hP⟩ : ∃ P, P = (2 ^ 64 - 1) / d * u + u1 := ⟨_, rfl⟩
  have hP' : P = v * u + 2 ^ 32 * u + u1 := by
    rw [hP, show (2 ^ 64 - 1) / d = v + 2 ^ 32 by omega_using [hVB, hv], Nat.add_mul, Nat.mul_comm (2 ^ 32) u]
  have hu32 : u < 2 ^ 32 := by omega_using [e₇]
  have ea₁₀ : (t₁₀.gpr .eax).toNat = v * u % 2 ^ 32 := by rw [U₁₀.eax, BitVec.toNat_ofNat, v₉, x₉]
  have a₁₂ : (t₁₂.gpr .eax).toNat = P % 2 ^ 32 := by
    rw [U₁₂.other _ (by decide), U₁₁.gpr, BitVec.toNat_add, ea₁₀, b₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu1, hP']
    exact (mgP_words _ u _ hu1).1
  have d₁₂ : (t₁₂.gpr .edx).toNat = P / 2 ^ 32 % 2 ^ 32 := by
    rw [U₁₂.gpr, add3_toNat, U₁₁.other .edx (by decide), U₁₁.other .ecx (by decide), ea₁₀, b₁₀, U₁₀.edx,
      U₁₀.other .ecx (by decide) (by decide), x₉, BitVec.toNat_ofNat, BitVec.toNat_ofNat, v₉,
      Nat.mod_eq_of_lt hu1, hP']
    have := (mgP_words (v * u) u u1 hu1).2
    rw [Nat.mod_eq_of_lt hu32] at this; exact this
  -- The candidate `Q = q₁ + 1` and its remainder.
  refine wp_movS rfl fun t₁₃ U₁₃ _ => wp_addS rfl fun t₁₄ U₁₄ _ => wp_movS rfl fun t₁₅ U₁₅ _ =>
    wp_movS rfl fun t₁₆ U₁₆ _ => ?_
  have K₁₆ : Keeps k6 s t₁₆ := K₁₂.trans (((U₁₃.keeps.mono (by decide)).trans (U₁₄.keeps.mono (by decide))).trans
    ((U₁₅.keeps.mono (by decide)).trans (U₁₆.keeps.mono (by decide))))
  have m₁₆ : t₁₆.mem = t₇.mem := by rw [U₁₆.mem, U₁₅.mem, U₁₄.mem, U₁₃.mem, m₁₂]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (P / 2 ^ 32 + 1) % 2 ^ 32 := ⟨_, rfl⟩
  have bx₁₄ : (t₁₄.gpr .ebx).toNat = Q := by
    rw [U₁₄.gpr, BitVec.toNat_add, U₁₃.gpr, d₁₂, hQ]
    show (P / 2 ^ 32 % 2 ^ 32 + 1) % 2 ^ 32 = _; omega_using []
  have q₁₆ : (t₁₆.gpr .eax).toNat = Q := by rw [U₁₆.gpr, U₁₅.other .ebx (by decide), bx₁₄]
  have bx₁₆ : (t₁₆.gpr .ebx).toNat = Q := by rw [U₁₆.other .ebx (by decide), U₁₅.other .ebx (by decide), bx₁₄]
  have cx₁₆ : (t₁₆.gpr .ecx).toNat = P % 2 ^ 32 := by
    rw [U₁₆.other .ecx (by decide), U₁₅.gpr, U₁₄.other .eax (by decide), U₁₃.other .eax (by decide), a₁₂]
  have bp₁₆ : t₁₆.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₁₆.other .ebp (by decide), U₁₅.other .ebp (by decide), U₁₄.other .ebp (by decide),
      U₁₃.other .ebp (by decide), U₁₂.other .ebp (by decide), U₁₁.other .ebp (by decide), b₁₀]
  refine wp_movS (rd (oD h) K₁₆ (by simp only [oD]; omega_using [hb])) fun t₁₇ U₁₇ _ => wp_mul fun t₁₈ U₁₈ => ?_
  refine wp_movS rfl fun t₁₉ U₁₉ _ => wp_subS rfl fun t₂₀ U₂₀ _ => ?_
  have si₁₇ : (t₁₇.gpr .esi).toNat = d := by
    rw [U₁₇.gpr, m₁₆]; change w32 t₇.mem base (oD h) = _
    rw [hmask (oD h) (.inl (by simp only [oD, oMask]; omega_using [])) (by simp only [oD]; omega_using [hb, nw]), hD]
  obtain ⟨r, hr⟩ : ∃ r, r = (u1 + (2 ^ 32 - Q * d % 2 ^ 32)) % 2 ^ 32 := ⟨_, rfl⟩
  have dx₂₀ : (t₂₀.gpr .edx).toNat = r := by
    rw [U₂₀.gpr, BitVec.toNat_sub, U₁₉.gpr, U₁₉.other .eax (by decide), U₁₈.eax, U₁₈.other .ebp (by decide) (by decide),
      U₁₇.other .ebp (by decide), U₁₇.other .eax (by decide), bp₁₆, q₁₆, si₁₇, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hu1, hr]
    omega_using []
  have cx₂₀ : (t₂₀.gpr .ecx).toNat = P % 2 ^ 32 := by
    rw [U₂₀.other .ecx (by decide), U₁₉.other .ecx (by decide), U₁₈.other .ecx (by decide) (by decide),
      U₁₇.other .ecx (by decide), cx₁₆]
  have si₂₀ : (t₂₀.gpr .esi).toNat = d := by
    rw [U₂₀.other .esi (by decide), U₁₉.other .esi (by decide), U₁₈.other .esi (by decide) (by decide), si₁₇]
  have bx₂₀ : (t₂₀.gpr .ebx).toNat = Q := by
    rw [U₂₀.other .ebx (by decide), U₁₉.other .ebx (by decide), U₁₈.other .ebx (by decide) (by decide),
      U₁₇.other .ebx (by decide), bx₁₆]
  have K₂₀ : Keeps k6 s t₂₀ := K₁₆.trans (((U₁₇.keeps.mono (by decide)).trans (U₁₈.keeps.mono (by decide))).trans
    ((U₁₉.keeps.mono (by decide)).trans (U₂₀.keeps.mono (by decide))))
  have m₂₀ : t₂₀.mem = t₇.mem := by rw [U₂₀.mem, U₁₉.mem, U₁₈.mem, U₁₇.mem, m₁₆]
  -- One less if `r > q₀`.
  refine wp_cmp fun t₂₁ F₂₁ c₂₁ _ => wp_sbbS rfl c₂₁ fun t₂₂ U₂₂ _ => wp_addS rfl fun t₂₃ U₂₃ _ => ?_
  refine wp_logicS (Or.inl rfl) rfl fun t₂₄ U₂₄ => wp_addS rfl fun t₂₅ U₂₅ _ => ?_
  have mk₂₂ : t₂₂.gpr .eax = BitVec.ofNat 32 (if P % 2 ^ 32 < r then 2 ^ 32 - 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [U₂₂.gpr, F₂₁.gpr, sbb_self, cx₂₀, dx₂₀, BitVec.toNat_ofNat]
    by_cases e : P % 2 ^ 32 < r
    · rw [ite_eq_left (by simp only [decide_eq_true_eq]; exact e), ite_eq_left e]
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact e), ite_eq_right e]
  obtain ⟨Q1, hQ1⟩ : ∃ Q1, Q1 = (Q + if P % 2 ^ 32 < r then 2 ^ 32 - 1 else 0) % 2 ^ 32 := ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ r1, r1 = (r + if P % 2 ^ 32 < r then d else 0) % 2 ^ 32 := ⟨_, rfl⟩
  have bx₂₃ : (t₂₃.gpr .ebx).toNat = Q1 := by
    rw [U₂₃.gpr, BitVec.toNat_add, mk₂₂, U₂₂.other .ebx (by decide), F₂₁.gpr, bx₂₀, BitVec.toNat_ofNat, hQ1]
    congr 1; split <;> omega_using []
  have si₂₃ : (t₂₃.gpr .esi).toNat = d := by
    rw [U₂₃.other .esi (by decide), U₂₂.other .esi (by decide), F₂₁.gpr, si₂₀]
  have si₂₃' : t₂₃.gpr .esi = BitVec.ofNat 32 d :=
    BitVec.eq_of_toNat_eq (by rw [si₂₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2])
  have dx₂₅ : (t₂₅.gpr .edx).toNat = r1 := by
    rw [U₂₅.gpr, BitVec.toNat_add, U₂₄.gpr, ite_eq_left rfl, U₂₄.other .edx (by decide), U₂₃.other .eax (by decide),
      U₂₃.other .edx (by decide), mk₂₂, U₂₂.other .edx (by decide), F₂₁.gpr, dx₂₀, hr1,
      si₂₃', BitVec.and_comm, and_mask]
    congr 1; split <;> simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]
  -- One more if then `r ≥ d`.
  refine wp_movS rfl fun t₂₆ U₂₆ _ => wp_subS rfl fun t₂₇ U₂₇ _ => wp_cmp fun t₂₈ F₂₈ c₂₈ _ => ?_
  refine wp_adcS rfl c₂₈ fun t₂₉ U₂₉ _ => ?_
  have K₂₉ : Keeps k6 s t₂₉ := K₂₀.trans ((F₂₁.keeps6.trans ((U₂₂.keeps.mono (by decide)).trans
    (U₂₃.keeps.mono (by decide)))).trans (((U₂₄.keeps.mono (by decide)).trans (U₂₅.keeps.mono (by decide))).trans
    (((U₂₆.keeps.mono (by decide)).trans (U₂₇.keeps.mono (by decide))).trans (F₂₈.keeps6.trans
    (U₂₉.keeps.mono (by decide))))))
  have m₂₉ : t₂₉.mem = t₇.mem := by
    rw [U₂₉.mem, F₂₈.mem, U₂₇.mem, U₂₆.mem, U₂₅.mem, U₂₄.mem, U₂₃.mem, U₂₂.mem, F₂₁.mem, m₂₀]
  have ax₂₇ : (t₂₇.gpr .eax).toNat = d - 1 := by
    rw [U₂₇.gpr, BitVec.toNat_sub, U₂₆.gpr, U₂₅.other .esi (by decide), U₂₄.other .esi (by decide), si₂₃]
    show (2 ^ 32 - 1 + d) % 2 ^ 32 = _; omega_using [hd1, hd2]
  have dx₂₇ : (t₂₇.gpr .edx).toNat = r1 := by
    rw [U₂₇.other .edx (by decide), U₂₆.other .edx (by decide), dx₂₅]
  have bx₂₉ : (t₂₉.gpr .ebx).toNat = (u * 2 ^ 32 + u1) / d := by
    rw [U₂₉.gpr, add3_toNat, F₂₈.gpr, U₂₇.other .ebx (by decide), U₂₆.other .ebx (by decide),
      U₂₅.other .ebx (by decide), U₂₄.other .ebx (by decide), bx₂₃, ax₂₇, dx₂₇, ofBool_toNat]
    exact mg_quot' hd2 hd1 hud hu1 hP hQ hr hQ1 hr1
  refine wp_orS (rd (oMask h) K₂₉ (by simp only [oMask]; omega_using [hb])) fun t₃₀ U₃₀ => ?_
  have K₃₀ : Keeps k6 s t₃₀ := K₂₉.trans (U₃₀.keeps.mono (by decide))
  refine wp_storeS (ea_ptr (wt K₃₀) (pt K₃₀) (d := (oQ h)) (by simp only [oQ]; omega_using [hb]))
    (ws_write (wt K₃₀) (by simp only [oQ]; omega_using [hb])) fun t₃₁ M₃₁ => WP.block_nil ?_
  have m₃₁ : t₃₁.mem = (s.mem.writeW (off base (oMask h)) (BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else 0))).writeW
      (off base (oQ h)) (t₃₀.gpr .ebx) := by rw [M₃₁.mem, U₃₀.mem, m₂₉, m₇, Nat.zero_add, Nat.zero_add]
  refine ⟨?_, ?_, ?_, K₃₀.trans (M₃₁.keeps _)⟩
  · rw [m₃₁, w32_write_self, U₃₀.gpr, m₂₉, m₇, Nat.zero_add, Mem.readW_writeW_self32]
    by_cases e : u2 = d
    · rw [ite_eq_left e, ite_eq_left e, show BitVec.ofNat 32 (2 ^ 32 - 1) = BitVec.allOnes 32 from rfl,
        BitVec.or_allOnes]; rfl
    · rw [ite_eq_right e, ite_eq_right e, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.or_zero, bx₂₉, hu,
        ite_eq_right e]
  · rw [m₃₁]
    exact ((writeW32_outside _ base _ (d := (oMask h)) (by simp only [oMask]; omega_using [hb, nw])).mono (by omega_using [])
      (by simp only [oMask]; omega_using [])).trans
      ((writeW32_outside _ base _ (d := (oQ h)) (by simp only [oQ]; omega_using [hb, nw])).mono (by simp only [oMask, oQ]; omega_using [])
        (by simp only [oMask, oQ]; omega_using []))
  · rw [m₃₁, w32_write_ne (size := bytes) nw (by simp only [oQ]; omega_using [hb]) (by simp only [oSteps]; omega_using [hb])
      (by simp only [oQ, oSteps]; omega_using []), w32_write_ne (size := bytes) nw (by simp only [oMask]; omega_using [hb])
      (by simp only [oSteps]; omega_using [hb]) (by simp only [oMask, oSteps]; omega_using [])]

/-! ## The 3-by-2 estimate -/

/-- `sbb`, as numbers: `a - b - c`, plus `2^32` if it borrows. -/
theorem sbb32_toNat (a b : BitVec 32) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 32).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 32 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- `adc`, as numbers. -/
theorem adc32_toNat (a b : BitVec 32) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 32).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, hc]
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- `add`, as numbers. -/
theorem add32_toNat (a b : BitVec 32) :
    (a + b).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_using [h]

/-- A header word through `edi`, for `xrun`. -/
theorem hdr_read {s : State} {base : Addr} {bytes o : Nat} (ws : Ws s base bytes) (di : PtrAt s base .edi 0)
    (ho : o + 4 ≤ bytes) :
    s.gpr .edi = BitVec.ofNat 32 (base.toNat + 0) ∧ addr (BitVec.ofNat 32 (base.toNat + 0)) o = off base (0 + o) ∧
      InRegions (s.rd ++ s.wr) (off base (0 + o)) 4 :=
  ⟨ptr_eq di, addr_off base (by have := ws.nowrap; omega_using [ho, this]), ws_read ws (by omega_using [ho])⟩

/-- `t` in `eax`, `ebp`, `esi`. -/
abbrev rem3 (s : State) : Nat := (s.gpr .eax).toNat * 2 ^ 64 + (s.gpr .ebp).toNat * 2 ^ 32 + (s.gpr .esi).toNat

/-- `quot3`: `q̂` (`h + 20`) into `ecx`, and `t = U - q̂ D` over three words, with
its borrow `b`, for `U = (u₂, u₁, u₀)` (`h + 28`, `ebp`, `h + 24`) and `D = (d, d₁)`
(`h + 4`, `h + 32`). -/
theorem quot3_ok {h : Nat} {s : State} {base : Addr} {bytes : Nat} (ws : Ws s base bytes) (di : PtrAt s base .edi 0)
    (hb : h + 36 ≤ bytes) :
    WP isa (.block (quot3 h)) s fun t => (t.gpr .ecx).toNat = w32 s.mem base (oQ h) ∧
      (∃ b < 2, rem3 t + w32 s.mem base (oQ h) * (w32 s.mem base (oD h) * 2 ^ 32 + w32 s.mem base (oD1 h)) =
        w32 s.mem base (oU2 h) * 2 ^ 64 + (s.gpr .ebp).toNat * 2 ^ 32 + w32 s.mem base (oU0 h) + 2 ^ 96 * b) ∧
      t.mem = s.mem ∧ Keeps k6 s t := by
  refine WP.mono (WP.keeps k6 (Q := fun t => (t.gpr .ecx).toNat = w32 s.mem base (oQ h) ∧
      (∃ b < 2, rem3 t + w32 s.mem base (oQ h) * (w32 s.mem base (oD h) * 2 ^ 32 + w32 s.mem base (oD1 h)) =
        w32 s.mem base (oU2 h) * 2 ^ 64 + (s.gpr .ebp).toNat * 2 ^ 32 + w32 s.mem base (oU0 h) + 2 ^ 96 * b) ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  obtain ⟨hdi, aQ, rQ⟩ := hdr_read (o := (oQ h)) ws di (by simp only [oQ]; omega_using [hb])
  obtain ⟨-, aD, rD⟩ := hdr_read (o := (oD h)) ws di (by simp only [oD]; omega_using [hb])
  obtain ⟨-, aD1, rD1⟩ := hdr_read (o := (oD1 h)) ws di (by simp only [oD1]; omega_using [hb])
  obtain ⟨-, aU0, rU0⟩ := hdr_read (o := (oU0 h)) ws di (by simp only [oU0]; omega_using [hb])
  obtain ⟨-, aU2, rU2⟩ := hdr_read (o := (oU2 h)) ws di (by simp only [oU2]; omega_using [hb])
  dsimp only [rem3]
  xrun [quot3, hd, execMul, hdi, aQ, rQ, aD, rD, aD1, rD1, aU0, rU0, aU2, rU2]
  simp only [Nat.zero_add]
  refine ⟨trivial, ?_⟩
  dsimp only [w32]
  generalize s.mem.readW (off base (oU2 h)) 32 = u2
  generalize s.mem.readW (off base (oU0 h)) 32 = u0
  generalize s.gpr .ebp = u1
  generalize s.mem.readW (off base (oD h)) 32 = d1
  generalize s.mem.readW (off base (oD1 h)) 32 = d0
  generalize s.mem.readW (off base (oQ h)) 32 = q
  have m1 := (mul_words d1 q).1; have l1 := (mul_words d1 q).2
  have m0 := (mul_words d0 q).1
  have eq : q.toNat * (d1.toNat * 2 ^ 32 + d0.toNat) = d1.toNat * q.toNat * 2 ^ 32 + d0.toNat * q.toNat := by
    rw [Nat.mul_comm, Nat.add_mul, Nat.mul_right_comm]
  rw [eq]
  generalize d1.toNat * q.toNat = p1 at *
  generalize d0.toNat * q.toNat = p0 at *
  generalize BitVec.ofNat 32 (p1 / 2 ^ 32) = H1 at *
  generalize BitVec.ofNat 32 p1 = P1 at *
  generalize BitVec.ofNat 32 (p0 / 2 ^ 32) = H0 at *
  generalize BitVec.ofNat 32 p0 = P0 at *
  have hH0 := H0.isLt; have hH1 := H1.isLt; have hP1 := P1.isLt
  have a1 := adc32_toNat H1 0 (decide (2 ^ 32 ≤ P1.toNat + H0.toNat))
  have a0 := add32_toNat P1 H0
  rw [show (0 : BitVec 32).toNat = 0 from rfl] at a1
  have s0 := sbb32_toNat u0 P0 false
  have s1 := sbb32_toNat u1 (P1 + H0) (decide (u0.toNat < P0.toNat))
  have s2 := sbb32_toNat u2 (H1 + 0 + (BitVec.ofBool (decide (2 ^ 32 ≤ P1.toNat + H0.toNat))).setWidth 32)
    (decide (u1.toNat < (P1 + H0).toNat + (decide (u0.toNat < P0.toNat)).toNat))
  simp only [Bool.toNat_false, Nat.add_zero, show (BitVec.ofBool false).setWidth 32 = 0#32 from rfl,
    BitVec.sub_zero] at s0
  generalize decide (u0.toNat < P0.toNat) = c0 at *
  generalize decide (2 ^ 32 ≤ P1.toNat + H0.toNat) = c1 at *
  generalize decide (u1.toNat < (P1 + H0).toNat + c0.toNat) = c2 at *
  generalize decide (u2.toNat < _ + c2.toNat) = c3 at s2
  generalize (u2 - _ - (BitVec.ofBool c2).setWidth 32) = R2 at *
  generalize (u1 - (P1 + H0) - (BitVec.ofBool c0).setWidth 32) = R1 at *
  generalize (u0 - P0) = R0 at *
  generalize (H1 + 0 + (BitVec.ofBool c1).setWidth 32) = RDX at *
  generalize (P1 + H0) = RAX at *
  have := Bool.toNat_le c1
  exact ⟨c3.toNat, Bool.toNat_lt _, by omega_using [l1, m1, m0, s0, a1, s2, a0, s1]⟩

/-- `fix3`: if `t` (`rem3`) is negative, `q̂ := q̂ - 1` (`ecx`) and `t := t + D`,
with its carry `c`, for `D = (d, d₁)` (`h + 4`, `h + 32`). -/
theorem fix3_ok {h : Nat} {s : State} {base : Addr} {bytes : Nat} (ws : Ws s base bytes) (di : PtrAt s base .edi 0)
    (hb : h + 36 ≤ bytes) :
    WP isa (.block (fix3 h)) s fun t =>
      (∀ n, (s.gpr .ecx).toNat = n + (if 2 ^ 96 / 2 ≤ rem3 s then 1 else 0) → (t.gpr .ecx).toNat = n) ∧
      (∃ c < 2, rem3 t + 2 ^ 96 * c = rem3 s + if 2 ^ 96 / 2 ≤ rem3 s then (w32 s.mem base (oD h) * 2 ^ 32 + w32 s.mem base (oD1 h)) else 0) ∧
      t.mem = s.mem ∧ Keeps k6 s t := by
  refine WP.mono (WP.keeps k6 (Q := fun t =>
      (∀ n, (s.gpr .ecx).toNat = n + (if 2 ^ 96 / 2 ≤ rem3 s then 1 else 0) → (t.gpr .ecx).toNat = n) ∧
      (∃ c < 2, rem3 t + 2 ^ 96 * c = rem3 s + if 2 ^ 96 / 2 ≤ rem3 s then (w32 s.mem base (oD h) * 2 ^ 32 + w32 s.mem base (oD1 h)) else 0) ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  obtain ⟨hdi, aD, rD⟩ := hdr_read (o := (oD h)) ws di (by simp only [oD]; omega_using [hb])
  obtain ⟨-, aD1, rD1⟩ := hdr_read (o := (oD1 h)) ws di (by simp only [oD1]; omega_using [hb])
  dsimp only [rem3]
  xrun [fix3, hd, hdi, aD, rD, aD1, rD1]
  simp only [Nat.zero_add]
  dsimp only [w32]
  generalize s.mem.readW (off base (oD h)) 32 = d1
  generalize s.mem.readW (off base (oD1 h)) 32 = d0
  generalize s.gpr .ecx = q
  have l0 := (s.gpr .esi).isLt; have l1 := (s.gpr .ebp).isLt; have l2 := (s.gpr .eax).isLt; have lq := q.isLt
  by_cases hn : 2 ^ 32 ≤ (s.gpr .eax).toNat + (s.gpr .eax).toNat
  · have hc : 2 ^ 96 / 2 ≤ (s.gpr .eax).toNat * 2 ^ 64 + (s.gpr .ebp).toNat * 2 ^ 32 + (s.gpr .esi).toNat := by omega_using [hn]
    simp only [hc, ↓reduceIte, hn, decide_true]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true)) = BitVec.allOnes 32 by decide,
      BitVec.allOnes_and, BitVec.allOnes_and]
    have e1 := add32_toNat (s.gpr .esi) d0
    generalize decide (2 ^ 32 ≤ (s.gpr .esi).toNat + d0.toNat) = c1 at *
    have e2 := adc32_toNat (s.gpr .ebp) d1 c1
    generalize decide (2 ^ 32 ≤ (s.gpr .ebp).toNat + d1.toNat + c1.toNat) = c2 at *
    have e3 := adc32_toNat (s.gpr .eax) 0 c2
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at e3
    refine ⟨fun n hq => ?_, _, Bool.toNat_lt (decide (2 ^ 32 ≤ (s.gpr .eax).toNat + 0 + c2.toNat)), ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_allOnes]; omega_using [hq]
    · omega_using [e1, e2, e3]
  · have hc : ¬ 2 ^ 96 / 2 ≤ (s.gpr .eax).toNat * 2 ^ 64 + (s.gpr .ebp).toNat * 2 ^ 32 + (s.gpr .esi).toNat := by
      omega_using [hn]
    simp only [hc, ↓reduceIte, hn, decide_false]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false)) = 0#32 by decide, BitVec.zero_and, BitVec.zero_and]
    have e1 := add32_toNat (s.gpr .esi) 0#32
    generalize decide (2 ^ 32 ≤ (s.gpr .esi).toNat + (0#32).toNat) = c1 at *
    have e2 := adc32_toNat (s.gpr .ebp) 0#32 c1
    generalize decide (2 ^ 32 ≤ (s.gpr .ebp).toNat + (0#32).toNat + c1.toNat) = c2 at *
    have e3 := adc32_toNat (s.gpr .eax) 0 c2
    rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at e1 e2
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at e3
    refine ⟨fun n hq => ?_, _, Bool.toNat_lt (decide (2 ^ 32 ≤ (s.gpr .eax).toNat + 0 + c2.toNat)), ?_⟩
    · rw [BitVec.add_zero]; omega_using [hq]
    · omega_using [e1, e2, e3]

theorem rem3_lt (t : State) : rem3 t < 2 ^ 96 := by
  have := (t.gpr .eax).isLt; have := (t.gpr .ebp).isLt; have := (t.gpr .esi).isLt; dsimp only [rem3]; omega_using []

theorem two_words_lt {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : 4 * (a * 2 ^ 32 + b) < 2 ^ 96 / 2 := by
  omega_using [ha, hb]

/-- `refine3`: `q̂` at `h + 20`, `Q ≤ q̂ ≤ Q + 2`, refined to `Q = min(⌊U / D⌋, 2^32 - 1)`,
for `U = (u₂, u₁, u₀)` (`h + 28`, `ebp`, `h + 24`) and `D = (d, d₁)` (`h + 4`, `h + 32`), `U < (2^32 + 1) D`. -/
theorem refine3_ok {h : Nat} {s : State} {base : Addr} {bytes : Nat} (ws : Ws s base bytes) (di : PtrAt s base .edi 0)
    (hb : h + 36 ≤ bytes) {U D : Nat}
    (hU : U = w32 s.mem base (oU2 h) * 2 ^ 64 + (s.gpr .ebp).toNat * 2 ^ 32 + w32 s.mem base (oU0 h))
    (hD : D = w32 s.mem base (oD h) * 2 ^ 32 + w32 s.mem base (oD1 h)) (hD0 : 0 < D) (hUD : U < (2 ^ 32 + 1) * D)
    (hge : min (U / D) (2 ^ 32 - 1) ≤ w32 s.mem base (oQ h)) (hle : w32 s.mem base (oQ h) ≤ min (U / D) (2 ^ 32 - 1) + 2) :
    WP isa (.block (refine3 h)) s fun t =>
      t.mem = s.mem.writeW (off base (oQ h)) (BitVec.ofNat 32 (min (U / D) (2 ^ 32 - 1))) ∧ Keeps k6 s t := by
  have pt : ∀ {t : State} {rs : List Reg}, .edi ∉ rs → Keeps rs s t → PtrAt t base .edi 0 := fun hr K => by
    rw [PtrAt, K.1 _ hr]; exact di
  have bQ : 0 + (oQ h) < bytes := by simp only [oQ]; omega_using [hb]
  have bQ' : 0 + (oQ h) + 4 ≤ bytes := by simp only [oQ]; omega_using [hb]
  simp only [refine3, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (quot3_ok ws di hb) fun t₁ ⟨hq₁, ⟨b, hb', h1⟩, hm₁, K₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fix3_ok (ws.of_keeps K₁) (pt (by decide) K₁) hb) fun t₂ ⟨hq₂, ⟨c, hc, h2⟩, hm₂, K₂⟩ => ?_
  rw [WP.block_append_iff]
  have K₁₂ := K₁.trans K₂
  refine WP.mono (fix3_ok (ws.of_keeps K₁₂) (pt (by decide) K₁₂) hb) fun t₃ ⟨hq₃, _, hm₃, K₃⟩ => ?_
  have K₁₃ := K₁₂.trans K₃
  refine wp_storeS (ea_ptr (ws.of_keeps K₁₃) (pt (by decide) K₁₃) (d := (oQ h)) bQ)
    (ws_write (ws.of_keeps K₁₃) bQ') fun t₄ M₄ => WP.block_nil ⟨?_, (K₁₃.trans (M₄.keeps _)).mono (by decide)⟩
  rw [← hU, ← hD] at h1
  rw [hm₁, ← hD] at h2
  have hDW : 4 * D < 2 ^ 96 / 2 := hD ▸ two_words_lt (s.mem.readW _ 32).isLt (s.mem.readW _ 32).isLt
  have hT1 := rem3_lt t₁
  have hT2 := rem3_lt t₂
  have hv := VG.Proof.Bignum.WordStep32.quot3_val (W := 2 ^ 96) (T1 := rem3 t₁) (T2 := rem3 t₂) hD0 hDW hUD hge hle
    (by dsimp only [w32]; exact BitVec.isLt _) hT1 hb' h1 hT2 hc h2
  have e3 := hq₃ (min (U / D) (2 ^ 32 - 1)) (hq₂ (min (U / D) (2 ^ 32 - 1) + if 2 ^ 96 / 2 ≤ rem3 t₂ then 1 else 0)
    (by rw [hq₁, hv, Nat.add_right_comm]))
  have hQ : min (U / D) (2 ^ 32 - 1) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  rw [M₄.mem, hm₃, hm₂, hm₁, Nat.zero_add,
    show t₃.gpr .ecx = BitVec.ofNat 32 (min (U / D) (2 ^ 32 - 1)) from
      BitVec.eq_of_toNat_eq (by rw [e3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQ])]

/-- `top`: `ebp = u₁ = lo(x[W' - 2] p) + hi(x[W' - 3] p)` and `eax = u₂ = lo(x[W' - 1] p) +
hi(x[W' - 2] p)`, and `u₀ = lo(x[W' - 3] p) + hi(x[W' - 4] p)` at 184 and `u₂` at 188. -/
theorem top_ok {s : State} {is : List Instr} {Q : State → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} (h : PcIn base bytes len args s)
    (kk : ∀ t, Keeps k6 s t →
      t.mem = (s.mem.writeW (off base oU0) (BitVec.ofNat 32 (topW s.mem base len 4 3 * w32 s.mem base oP % 2 ^ 32 + topW s.mem base len 4 4 * w32 s.mem base oP / 2 ^ 32))).writeW (off base oU2)
        (BitVec.ofNat 32 (topW s.mem base len 4 1 * w32 s.mem base oP % 2 ^ 32 + topW s.mem base len 4 2 * w32 s.mem base oP / 2 ^ 32)) →
      t.gpr .ebp = BitVec.ofNat 32 (topW s.mem base len 4 2 * w32 s.mem base oP % 2 ^ 32 + topW s.mem base len 4 3 * w32 s.mem base oP / 2 ^ 32) → t.gpr .eax = BitVec.ofNat 32 (topW s.mem base len 4 1 * w32 s.mem base oP % 2 ^ 32 + topW s.mem base len 4 2 * w32 s.mem base oP / 2 ^ 32) → WP isa (.block is) t Q) :
    WP isa (.block (top ++ is)) s Q := by
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have f4 := (h.fits (j := 4) (by decide)).1
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega_using [hl]
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  rw [top, List.append_assoc]
  refine topPtr_ok h (r := .ebx) (t := .ecx) (j := 4) (i := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hwp16]) fun u K m p _ => ?_
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  have di : PtrAt u base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [nw', f4, hwp, hwp16])]; exact hu.edi
  have ws := hu.ws
  obtain ⟨hdi, aP, rP⟩ := hdr_read (o := oP) ws di (by simp only [oP]; omega_using [f4, e4])
  have hbx := ptr_eq p
  have a0 := addr_off base (x := numAt len 4 + 4 * wp len - 4 * 4) (d := 0) (by rw [e4]; omega_using [nw', f4, hwp, e4])
  have a1 := addr_off base (x := numAt len 4 + 4 * wp len - 4 * 4) (d := 4) (by rw [e4]; omega_using [nw', f4, hwp, e4])
  have a2 := addr_off base (x := numAt len 4 + 4 * wp len - 4 * 4) (d := 8) (by rw [e4]; omega_using [nw', f4, hwp, e4])
  have a3 := addr_off base (x := numAt len 4 + 4 * wp len - 4 * 4) (d := 12) (by rw [e4]; omega_using [nw', f4, hwp, e4])
  have r0 := ws_read ws (y := numAt len 4 + 4 * wp len - 4 * 4 + 0) (n := 4) (by rw [e4]; omega_using [f4, hwp, e4])
  have r1 := ws_read ws (y := numAt len 4 + 4 * wp len - 4 * 4 + 4) (n := 4) (by rw [e4]; omega_using [f4, hwp, e4])
  have r2 := ws_read ws (y := numAt len 4 + 4 * wp len - 4 * 4 + 8) (n := 4) (by rw [e4]; omega_using [f4, hwp, e4])
  have r3 := ws_read ws (y := numAt len 4 + 4 * wp len - 4 * 4 + 12) (n := 4) (by rw [e4]; omega_using [f4, hwp, e4])
  obtain ⟨-, aU0, -⟩ := hdr_read (o := oU0) ws di (by simp only [oU0]; omega_using [f4, e4])
  obtain ⟨-, aU2, -⟩ := hdr_read (o := oU2) ws di (by simp only [oU2]; omega_using [f4, e4])
  have wU0 := ws_write ws (y := 0 + oU0) (n := 4) (by simp only [oU0]; omega_using [f4, e4])
  have wU2 := ws_write ws (y := 0 + oU2) (n := 4) (by simp only [oU2]; omega_using [f4, e4])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keeps k6 (Q := fun t => t.mem = (u.mem.writeW (off base oU0) (BitVec.ofNat 32 (topW u.mem base len 4 3 * w32 u.mem base oP % 2 ^ 32 + topW u.mem base len 4 4 * w32 u.mem base oP / 2 ^ 32))).writeW (off base oU2)
        (BitVec.ofNat 32 (topW u.mem base len 4 1 * w32 u.mem base oP % 2 ^ 32 + topW u.mem base len 4 2 * w32 u.mem base oP / 2 ^ 32)) ∧
      t.gpr .ebp = BitVec.ofNat 32 (topW u.mem base len 4 2 * w32 u.mem base oP % 2 ^ 32 + topW u.mem base len 4 3 * w32 u.mem base oP / 2 ^ 32) ∧ t.gpr .eax = BitVec.ofNat 32 (topW u.mem base len 4 1 * w32 u.mem base oP % 2 ^ 32 + topW u.mem base len 4 2 * w32 u.mem base oP / 2 ^ 32)) ?_ rfl)
    fun t ⟨⟨hm, hbp, hax⟩, Kt⟩ => kk t ((K.mono (by decide)).trans Kt) (by rw [hm, m]) (by rw [hbp, m]) (by rw [hax, m])
  xrun [topWords, hd, execMul, hdi, aP, rP, hbx, a0, a1, a2, a3, r0, r1, r2, r3, aU0, aU2, wU0, wU2]
  have i0 : numAt len 4 + 4 * wp len - 4 * 4 + 0 = numAt len 4 + 4 * wp len - 4 * 4 := rfl
  have i1 : numAt len 4 + 4 * wp len - 4 * 4 + 4 = numAt len 4 + 4 * wp len - 4 * 3 := by omega_using [hwp16]
  have i2 : numAt len 4 + 4 * wp len - 4 * 4 + 8 = numAt len 4 + 4 * wp len - 4 * 2 := by omega_using [hwp16]
  have i3 : numAt len 4 + 4 * wp len - 4 * 4 + 12 = numAt len 4 + 4 * wp len - 4 * 1 := by omega_using [hwp16]
  simp only [Nat.zero_add, i0, i1, i2, i3]
  dsimp only [topW, w32]
  refine ⟨?_, ?_, ?_⟩
  · rw [ofNat_add_lo _ _ (hi_lt _ _), ofNat_add_lo _ _ (hi_lt _ _)]
  · rw [ofNat_add_lo _ _ (hi_lt _ _)]
  · rw [ofNat_add_lo _ _ (hi_lt _ _)]

end VG.Proof.Bignum.X86.R2Words
