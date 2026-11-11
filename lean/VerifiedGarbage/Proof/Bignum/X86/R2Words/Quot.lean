module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Ptr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep32

/-!
# `R2Words` on x86: the estimate of a step's quotient

`top` leaves the top words `u₁`, `u₂` of `2^z x` in `ebp` and `eax`, from
the top three words of `x` and `p = 2^z` (`top_ok`).
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
  have := (mul_words a b).2; omega

/-- `top`: `ebp = lo(x[W' - 2] p) + hi(x[W' - 3] p)` and `eax = lo(x[W' - 1] p) + hi(x[W' - 2] p)`. -/
theorem top_ok {s : State} {is : List Instr} {Q : State → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} (h : PcIn base bytes len args s)
    (kk : ∀ t, Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t → t.mem = s.mem →
      t.gpr .ebp = BitVec.ofNat 32 (topW s.mem base len 4 2 * w32 s.mem base oP % 2 ^ 32 +
        topW s.mem base len 4 3 * w32 s.mem base oP / 2 ^ 32) →
      t.gpr .eax = BitVec.ofNat 32 (topW s.mem base len 4 1 * w32 s.mem base oP % 2 ^ 32 +
        topW s.mem base len 4 2 * w32 s.mem base oP / 2 ^ 32) → WP isa (.block is) t Q) :
    WP isa (.block (top ++ is)) s Q := by
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have f4 := (h.fits (j := 4) (by decide)).1
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  simp only [top, List.append_assoc, List.cons_append, List.nil_append]
  refine topPtr_ok h (r := .ebx) (t := .ecx) (j := 4) (i := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) fun u K m p _ => ?_
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  have di : PtrAt u base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact hu.edi
  have ws := hu.ws
  refine wp_movS (readSrc_ptr ws di (d := oP) (by simp only [oP]; omega)) fun t₁ U₁ _ => ?_
  have p₁ : PtrAt t₁ base .ebx (numAt len 4 + 4 * wp len - 4 * 3) := by rw [PtrAt, U₁.other _ (by decide)]; exact p
  have ws₁ := ws.of_wr U₁.wr
  refine wp_movS (readSrc_ptr ws₁ p₁ (d := 0) (by rw [e4]; omega)) fun t₂ U₂ _ => ?_
  refine wp_mul fun t₃ U₃ => wp_movS rfl fun t₄ U₄ _ => ?_
  have p₄ : PtrAt t₄ base .ebx (numAt len 4 + 4 * wp len - 4 * 3) := by
    rw [PtrAt, U₄.other _ (by decide), U₃.other _ (by decide) (by decide), U₂.other _ (by decide)]; exact p₁
  have ws₄ := ws₁.of_wr (U₄.wr.trans (U₃.wr.trans U₂.wr))
  refine wp_movS (readSrc_ptr ws₄ p₄ (d := 4) (by rw [e4]; omega)) fun t₅ U₅ _ => ?_
  refine wp_mul fun t₆ U₆ => wp_addS rfl fun t₇ U₇ _ => wp_movS rfl fun t₈ U₈ _ => wp_movS rfl fun t₉ U₉ _ => ?_
  have p₉ : PtrAt t₉ base .ebx (numAt len 4 + 4 * wp len - 4 * 3) := by
    rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide),
      U₆.other _ (by decide) (by decide), U₅.other _ (by decide)]; exact p₄
  have ws₉ := ws₄.of_wr (U₉.wr.trans (U₈.wr.trans (U₇.wr.trans (U₆.wr.trans U₅.wr))))
  refine wp_movS (readSrc_ptr ws₉ p₉ (d := 8) (by rw [e4]; omega)) fun t₁₀ U₁₀ _ => ?_
  refine wp_mul fun t₁₁ U₁₁ => wp_addS rfl fun t₁₂ U₁₂ _ => ?_
  have K₁₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t₁₂ := by
    refine (K.mono (by decide)).trans ?_
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have h1 : r ≠ .eax := by revert hr; cases r <;> decide
      have h2 : r ≠ .ebx := by revert hr; cases r <;> decide
      have h3 : r ≠ .ecx := by revert hr; cases r <;> decide
      have h4 : r ≠ .edx := by revert hr; cases r <;> decide
      have h5 : r ≠ .esi := by revert hr; cases r <;> decide
      have h6 : r ≠ .ebp := by revert hr; cases r <;> decide
      rw [U₁₂.other _ h1, U₁₁.other _ h1 h4, U₁₀.other _ h1, U₉.other _ h3, U₈.other _ h6, U₇.other _ h1,
        U₆.other _ h1 h4, U₅.other _ h1, U₄.other _ h3, U₃.other _ h1 h4, U₂.other _ h1, U₁.other _ h5]
    · rw [U₁₂.rd, U₁₁.rd, U₁₀.rd, U₉.rd, U₈.rd, U₇.rd, U₆.rd, U₅.rd, U₄.rd, U₃.rd, U₂.rd, U₁.rd]
    · rw [U₁₂.wr, U₁₁.wr, U₁₀.wr, U₉.wr, U₈.wr, U₇.wr, U₆.wr, U₅.wr, U₄.wr, U₃.wr, U₂.wr, U₁.wr]
  have m₁₂ : t₁₂.mem = s.mem := by
    rw [U₁₂.mem, U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem, m]
  -- The values, in the memory `u.mem = s.mem`.
  have mm : ∀ k, t₁.mem.readW (off base k) 32 = s.mem.readW (off base k) 32 := fun k => by rw [U₁.mem, m]
  have si : ∀ v : BitVec 32, v = t₁.gpr .esi → v.toNat = w32 s.mem base oP := fun v e => by
    rw [e, U₁.gpr, Nat.zero_add, m]
  have s₂ := si (t₂.gpr .esi) (U₂.other _ (by decide))
  have s₅ := si (t₅.gpr .esi) (by rw [U₅.other _ (by decide), U₄.other _ (by decide),
    U₃.other _ (by decide) (by decide), U₂.other _ (by decide)])
  have s₁₀ := si (t₁₀.gpr .esi) (by rw [U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide),
    U₇.other _ (by decide), U₆.other _ (by decide) (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
    U₃.other _ (by decide) (by decide), U₂.other _ (by decide)])
  have a₂ : (t₂.gpr .eax).toNat = topW s.mem base len 4 3 := by
    rw [U₂.gpr, Nat.add_zero, U₁.mem, m]
  have a₅ : (t₅.gpr .eax).toNat = topW s.mem base len 4 2 := by
    rw [U₅.gpr, U₄.mem, U₃.mem, U₂.mem, U₁.mem, m, topW]
    exact congrArg (fun d => (s.mem.readW (off base d) 32).toNat) (by rw [e4]; omega)
  have a₁₀ : (t₁₀.gpr .eax).toNat = topW s.mem base len 4 1 := by
    rw [U₁₀.gpr, U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem, m, topW]
    exact congrArg (fun d => (s.mem.readW (off base d) 32).toNat) (by rw [e4]; omega)
  refine kk t₁₂ K₁₂ m₁₂ ?_ ?_
  · rw [U₁₂.other _ (by decide), U₁₁.other _ (by decide) (by decide), U₁₀.other _ (by decide),
      U₉.other _ (by decide), U₈.gpr, U₇.gpr, U₆.eax, U₆.other .ecx (by decide) (by decide), U₅.other .ecx (by decide),
      U₄.gpr, U₃.edx, a₅, s₅, a₂, s₂]
    exact ofNat_add_lo _ _ (by rw [← a₂, ← s₂]; exact hi_lt _ _)
  · rw [U₁₂.gpr, U₁₁.eax, U₁₁.other .ecx (by decide) (by decide), U₁₀.other .ecx (by decide), U₉.gpr,
      U₈.other _ (by decide), U₇.other _ (by decide), U₆.edx, a₁₀, s₁₀, a₅, s₅]
    exact ofNat_add_lo _ _ (by rw [← a₅, ← s₅]; exact hi_lt _ _)

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
  · omega
  · cases h : decide (2 ^ 32 ≤ X % 2 ^ 32 + a) <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h <;>
      simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

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

/-- `quot`: `q̂` at 180, `min(⌊(u₂ 2^32 + u₁) / d⌋, 2^32 - 1)` for `u₂ ≤ d`. -/
theorem quot_ok {s : State} {base : Addr} {bytes : Nat} {u2 u1 d : Nat}
    (ws : Ws s base bytes) (di : PtrAt s base .edi 0) (hb : 184 ≤ bytes)
    (hax : s.gpr .eax = BitVec.ofNat 32 u2) (hbp : s.gpr .ebp = BitVec.ofNat 32 u1)
    (hD : w32 s.mem base oD = d) (hV : w32 s.mem base oV = (2 ^ 64 - 1) / d - 2 ^ 32)
    (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) (hu2 : u2 ≤ d) (hu1 : u1 < 2 ^ 32) :
    WP isa (.block quot) s fun t =>
      w32 t.mem base oQ = (if u2 = d then 2 ^ 32 - 1 else (u2 * 2 ^ 32 + u1) / d) ∧
      Outside base oMask 12 s.mem t.mem ∧ Keeps k6 s t := by
  have nw := ws.nowrap
  have hu2' : u2 < 2 ^ 32 := by omega
  have pt : ∀ {t : State}, Keeps k6 s t → PtrAt t base .edi 0 := fun K => by rw [PtrAt, K.1 _ (by decide)]; exact di
  have wt : ∀ {t : State}, Keeps k6 s t → Ws t base bytes := fun K => ws.of_keeps K
  have rd : ∀ {t : State} (o : Nat), Keeps k6 s t → o + 4 ≤ bytes →
      readSrc t (.mem (hd o)) = some (t.mem.readW (off base o) 32) := fun o K ho => by
    have r := readSrc_ptr (wt K) (pt K) (d := o) (by omega)
    rw [Nat.zero_add] at r; exact r
  have hd0 : 0 < d := by omega
  -- The mask of `u₂ = d`.
  refine wp_movS (rd oD (Keeps.refl _ _) (by simp only [oD]; omega)) fun t₁ U₁ _ => ?_
  refine wp_subS rfl fun t₂ U₂ _ => wp_cmpi fun t₃ F₃ c₃ _ => wp_sbbS rfl c₃ fun t₄ U₄ _ => ?_
  have K₄ : Keeps k6 s t₄ := (U₁.keeps.mono (by decide)).trans (((U₂.keeps.mono (by decide)).trans F₃.keeps6).trans
    (U₄.keeps.mono (by decide)))
  have m₄ : t₄.mem = s.mem := by rw [U₄.mem, F₃.mem, U₂.mem, U₁.mem]
  have e₂ : (t₂.gpr .ecx).toNat = d - u2 := by
    rw [U₂.gpr, U₁.gpr, U₁.other _ (by decide), hax, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu2']
    change (2 ^ 32 - u2 + w32 s.mem base oD) % 2 ^ 32 = _
    rw [hD]; omega
  have e₄ : t₄.gpr .ecx = BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [U₄.gpr, F₃.gpr, sbb_self]
    by_cases e : u2 = d
    · rw [ite_eq_left (by rw [e₂]; simp only [decide_eq_true_eq]; show d - u2 < 1; omega), ite_eq_left e]; rfl
    · rw [ite_eq_right (by rw [e₂]; simp only [decide_eq_true_eq]; show ¬ d - u2 < 1; omega), ite_eq_right e]; rfl
  refine wp_storeS (ea_ptr (wt K₄) (pt K₄) (d := oMask) (by simp only [oMask]; omega))
    (ws_write (wt K₄) (by simp only [oMask]; omega)) fun t₅ M₅ => ?_
  refine wp_logicS (Or.inr rfl) rfl fun t₆ U₆ => wp_logicS (Or.inl rfl) rfl fun t₇ U₇ => ?_
  have K₇ : Keeps k6 s t₇ := K₄.trans (((M₅.keeps _).trans (U₆.keeps.mono (by decide))).trans (U₇.keeps.mono (by decide)))
  have m₇ : t₇.mem = s.mem.writeW (off base (0 + oMask)) (BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else 0)) := by
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
    have := Nat.mul_le_mul_left (2 ^ 32) (show d ≤ 2 ^ 32 - 1 by omega); omega
  have bp₇ : t₇.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), F₃.gpr,
      U₂.other _ (by decide), U₁.other _ (by decide), hbp]
  obtain ⟨u, hu⟩ : ∃ u, u = if u2 = d then 0 else u2 := ⟨_, rfl⟩
  rw [← hu] at e₇
  have hud : u < d := by
    by_cases e : u2 = d
    · rw [hu, ite_eq_left e]; exact hd0
    · rw [hu, ite_eq_right e]; omega
  have hmask : ∀ k, (k + 4 ≤ oMask ∨ oMask + 4 ≤ k) → k + 4 ≤ 2 ^ 64 → w32 t₇.mem base k = w32 s.mem base k :=
    fun k h1 h2 => by rw [m₇, Nat.zero_add]; exact (writeW32_outside _ base _ (by simp only [oMask]; omega)).w32 h1 h2
  refine wp_movS rfl fun t₈ U₈ _ => ?_
  have K₈ : Keeps k6 s t₈ := K₇.trans (U₈.keeps.mono (by decide))
  refine wp_movS (rd oV K₈ (by simp only [oV]; omega)) fun t₉ U₉ _ => wp_mul fun t₁₀ U₁₀ => ?_
  refine wp_addS rfl fun t₁₁ U₁₁ c₁₁ => wp_adcS rfl c₁₁ fun t₁₂ U₁₂ _ => ?_
  have K₁₂ : Keeps k6 s t₁₂ := K₈.trans ((U₉.keeps.mono (by decide)).trans ((U₁₀.keeps.mono (by decide)).trans
    ((U₁₁.keeps.mono (by decide)).trans (U₁₂.keeps.mono (by decide)))))
  have m₁₂ : t₁₂.mem = t₇.mem := by rw [U₁₂.mem, U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem]
  have v₉ : (t₉.gpr .eax).toNat = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [U₉.gpr, U₈.mem]; change w32 t₇.mem base oV = _
    rw [hmask oV (.inl (by simp only [oV, oMask]; omega)) (by simp only [oV]; omega), hV]
  have x₉ : (t₉.gpr .ecx).toNat = u := by rw [U₉.other _ (by decide), U₈.gpr, e₇]
  have b₁₀ : t₁₀.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₁₀.other _ (by decide) (by decide), U₉.other _ (by decide), U₈.other _ (by decide), bp₇]
  obtain ⟨v, hv⟩ : ∃ v, v = (2 ^ 64 - 1) / d - 2 ^ 32 := ⟨_, rfl⟩
  rw [← hv] at v₉
  obtain ⟨P, hP⟩ : ∃ P, P = (2 ^ 64 - 1) / d * u + u1 := ⟨_, rfl⟩
  have hP' : P = v * u + 2 ^ 32 * u + u1 := by
    rw [hP, show (2 ^ 64 - 1) / d = v + 2 ^ 32 by omega, Nat.add_mul, Nat.mul_comm (2 ^ 32) u]
  have hu32 : u < 2 ^ 32 := by omega
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
    show (P / 2 ^ 32 % 2 ^ 32 + 1) % 2 ^ 32 = _; omega
  have q₁₆ : (t₁₆.gpr .eax).toNat = Q := by rw [U₁₆.gpr, U₁₅.other .ebx (by decide), bx₁₄]
  have bx₁₆ : (t₁₆.gpr .ebx).toNat = Q := by rw [U₁₆.other .ebx (by decide), U₁₅.other .ebx (by decide), bx₁₄]
  have cx₁₆ : (t₁₆.gpr .ecx).toNat = P % 2 ^ 32 := by
    rw [U₁₆.other .ecx (by decide), U₁₅.gpr, U₁₄.other .eax (by decide), U₁₃.other .eax (by decide), a₁₂]
  have bp₁₆ : t₁₆.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₁₆.other .ebp (by decide), U₁₅.other .ebp (by decide), U₁₄.other .ebp (by decide),
      U₁₃.other .ebp (by decide), U₁₂.other .ebp (by decide), U₁₁.other .ebp (by decide), b₁₀]
  refine wp_movS (rd oD K₁₆ (by simp only [oD]; omega)) fun t₁₇ U₁₇ _ => wp_mul fun t₁₈ U₁₈ => ?_
  refine wp_movS rfl fun t₁₉ U₁₉ _ => wp_subS rfl fun t₂₀ U₂₀ _ => ?_
  have si₁₇ : (t₁₇.gpr .esi).toNat = d := by
    rw [U₁₇.gpr, m₁₆]; change w32 t₇.mem base oD = _
    rw [hmask oD (.inl (by simp only [oD, oMask]; omega)) (by simp only [oD]; omega), hD]
  obtain ⟨r, hr⟩ : ∃ r, r = (u1 + (2 ^ 32 - Q * d % 2 ^ 32)) % 2 ^ 32 := ⟨_, rfl⟩
  have dx₂₀ : (t₂₀.gpr .edx).toNat = r := by
    rw [U₂₀.gpr, BitVec.toNat_sub, U₁₉.gpr, U₁₉.other .eax (by decide), U₁₈.eax, U₁₈.other .ebp (by decide) (by decide),
      U₁₇.other .ebp (by decide), U₁₇.other .eax (by decide), bp₁₆, q₁₆, si₁₇, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hu1, hr]
    omega
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
    congr 1; split <;> omega
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
    show (2 ^ 32 - 1 + d) % 2 ^ 32 = _; omega
  have dx₂₇ : (t₂₇.gpr .edx).toNat = r1 := by
    rw [U₂₇.other .edx (by decide), U₂₆.other .edx (by decide), dx₂₅]
  have bx₂₉ : (t₂₉.gpr .ebx).toNat = (u * 2 ^ 32 + u1) / d := by
    rw [U₂₉.gpr, add3_toNat, F₂₈.gpr, U₂₇.other .ebx (by decide), U₂₆.other .ebx (by decide),
      U₂₅.other .ebx (by decide), U₂₄.other .ebx (by decide), bx₂₃, ax₂₇, dx₂₇, ofBool_toNat]
    exact mg_quot' hd2 hd1 hud hu1 hP hQ hr hQ1 hr1
  refine wp_orS (rd oMask K₂₉ (by simp only [oMask]; omega)) fun t₃₀ U₃₀ => ?_
  have K₃₀ : Keeps k6 s t₃₀ := K₂₉.trans (U₃₀.keeps.mono (by decide))
  refine wp_storeS (ea_ptr (wt K₃₀) (pt K₃₀) (d := oQ) (by simp only [oQ]; omega))
    (ws_write (wt K₃₀) (by simp only [oQ]; omega)) fun t₃₁ M₃₁ => WP.block_nil ?_
  have m₃₁ : t₃₁.mem = (s.mem.writeW (off base oMask) (BitVec.ofNat 32 (if u2 = d then 2 ^ 32 - 1 else 0))).writeW
      (off base oQ) (t₃₀.gpr .ebx) := by rw [M₃₁.mem, U₃₀.mem, m₂₉, m₇, Nat.zero_add, Nat.zero_add]
  refine ⟨?_, ?_, K₃₀.trans (M₃₁.keeps _)⟩
  · rw [m₃₁, w32_write_self, U₃₀.gpr, m₂₉, m₇, Nat.zero_add, Mem.readW_writeW_self32]
    by_cases e : u2 = d
    · rw [ite_eq_left e, ite_eq_left e, show BitVec.ofNat 32 (2 ^ 32 - 1) = BitVec.allOnes 32 from rfl,
        BitVec.or_allOnes]; rfl
    · rw [ite_eq_right e, ite_eq_right e, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.or_zero, bx₂₉, hu,
        ite_eq_right e]
  · rw [m₃₁]
    exact ((writeW32_outside _ base _ (d := oMask) (by simp only [oMask]; omega)).mono (by omega)
      (by simp only [oMask]; omega)).trans
      ((writeW32_outside _ base _ (d := oQ) (by simp only [oQ]; omega)).mono (by simp only [oMask, oQ]; omega)
        (by simp only [oMask, oQ]; omega))

end VG.Proof.Bignum.X86.R2Words
