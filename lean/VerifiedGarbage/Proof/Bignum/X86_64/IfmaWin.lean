import VerifiedGarbage.Proof.Bignum.X86_64.IfmaTab

/-!
# RSA with AVX512_IFMA on x86-64: a window of the exponentiations

`ExpSt`: the regions' moduli (`Ar`), the table (`T_j ≡ x^j R`) and
`Y ≡ x^E R` for each prime, `R = 2¹⁰⁴⁰`. A window (`window_ok`) squares
`Y` four times (`sq_ok`), reads `T_v` into `S` for the top 4 bits `v` of
each prime's quadword at `oV` (`select_ok`), rotates that quadword up by
4 bits, and multiplies `Y` by `S` (`mulS_ok`): `Y ≡ x^(16 E + v) R`. It
writes only `Y`, `S` and `V` of each region (`OutW`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oTab oS oV oX oY oE mask52)

/-- The state of the exponentiations: `Y ≡ x^E R`. -/
structure ExpSt (m : Mem) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) : Prop where
  ar : Ar m B M k
  tab : ∀ j < 16, ∀ p < 2, Good m B M (oTab + 160 * j) p ∧
    (Q → val52 m B (D * p + (oTab + 160 * j)) % M p = x p ^ j * 2 ^ (52 * 20) % M p)
  y : ∀ p < 2, Good m B M oY p
  yv : Q → ∀ p < 2, val52 m B (D * p + oY) % M p = x p ^ E p * 2 ^ (52 * 20) % M p

/-- `m'` agrees with `m` but on `Y`, `S` and `V` of each region. -/
def OutW (B : Addr) (m m' : Mem) : Prop :=
  ∀ a, (∀ p < 2, (ofs B a < D * p + oY ∨ D * p + oY + 160 ≤ ofs B a) ∧
    (ofs B a < D * p + oS ∨ D * p + oS + 160 ≤ ofs B a) ∧ (ofs B a < D * p + oV ∨ D * p + oV + 8 ≤ ofs B a)) →
    m' a = m a

theorem OutW.refl (B : Addr) (m : Mem) : OutW B m m := fun _ _ => rfl

theorem OutW.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : OutW B m₁ m₂) (h₂ : OutW B m₂ m₃) : OutW B m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem OutW.ofY {B : Addr} {m m' : Mem} (h : Out2 B oY 160 m m') : OutW B m m' :=
  fun a ha => h a fun p hp => (ha p hp).1

theorem OutW.ofS {B : Addr} {m m' : Mem} (h : Out2 B oS 160 m m') : OutW B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.1

theorem OutW.ofV {B : Addr} {m m' : Mem} (h : Out2 B oV 8 m m') : OutW B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.2

/-- The table after a write elsewhere. -/
theorem ExpSt.tab_of {m m' : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (h : ExpSt m B M k x Q E) {o n : Nat} (hf : Out2 B o n m m') (ho : o + n ≤ oTab ∨ oTab + 2560 ≤ o)
    (hoD : o + n ≤ D) :
    ∀ j < 16, ∀ p < 2, Good m' B M (oTab + 160 * j) p ∧
      (Q → val52 m' B (D * p + (oTab + 160 * j)) % M p = x p ^ j * 2 ^ (52 * 20) % M p) := fun j hj p hp => by
  have hc : oTab + 160 * j + 160 ≤ o ∨ o + n ≤ oTab + 160 * j := by
    rcases ho with ho | ho
    · exact .inr (by omega)
    · exact .inl (by simp only [oTab] at ho ⊢; omega)
  have hcD : oTab + 160 * j + 160 ≤ D := by simp only [oTab, D]; omega
  obtain ⟨g, v⟩ := h.tab j hj p hp
  exact ⟨g.of_out2 hp hf hc hcD hoD, fun hq => by rw [hf.val hp hc hcD hoD]; exact v hq⟩

/-- `Y := Y² / R`: `x^E R` becomes `x^(2E) R`. -/
theorem sq_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (h : ExpSt s.mem B M k x Q E) :
    WP isa (VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oY) s fun s' => ExpSt s'.mem B M k x Q (fun p => 2 * E p) ∧
      OutW B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (amm2_ok hB hs h.ar (by decide) (by decide) (by decide) (by decide) h.y h.y)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hf (.inl (by decide)) (by decide),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, OutW.ofY hf, hg, hrd, hwr, hx⟩
  exact VG.Proof.Bignum.mont_sq (hR p hp) (h.yv hq p hp) (hv p hp).2

/-- `Y := Y S / R`: `x^E R` and `S ≡ x^v R` give `x^(E+v) R`. -/
theorem mulS_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (h : ExpSt s.mem B M k x Q E) (gs : ∀ p < 2, Good s.mem B M oS p)
    (vs : Q → ∀ p < 2, val52 s.mem B (D * p + oS) % M p = x p ^ v p * 2 ^ (52 * 20) % M p) :
    WP isa (VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oS) s fun s' => ExpSt s'.mem B M k x Q (fun p => E p + v p) ∧
      OutW B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (amm2_ok hB hs h.ar (by decide) (by decide) (by decide) (by decide) h.y gs)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hf (.inl (by decide)) (by decide),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, OutW.ofY hf, hg, hrd, hwr, hx⟩
  exact mont_mul2 (hR p hp) (h.yv hq p hp) (vs hq p hp) (hv p hp).2


/-- The squarings' count down, `ZF` at 0. -/
theorem r15Dec_ok {s : State} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 4) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .sub .r15 (.imm 1)]) s fun s' =>
      s'.gpr .r15 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r15] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r15] (Q := fun s' =>
    s'.gpr .r15 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h15]
    have e : BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← VG.Offset.ofNat_sub_ofNat hn]
    and_intros
    · exact e
    · rw [e]; congr 1
      by_cases h : n - 1 = 0
      · simp only [h, decide_true]; rfl
      · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro h'
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- After `4 - n` squarings, from `s₀`. -/
structure SqInv (s₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) (n : Nat) (t : State) :
    Prop where
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  st : ExpSt t.mem B M k x Q (fun p => E p * 2 ^ (4 - n))
  frame : OutW B s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- The four squarings: `Y ≡ x^E R` becomes `x^(16 E) R`. -/
theorem sqLoop_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (h : ExpSt s.mem B M k x Q E) :
    WP isa (.seq (.block [.mov32 .r15 (.imm 4)])
      (.loop (.seq (VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oY) (.block [.alu .sub .r15 (.imm 1)])) .ne)) s
      fun s' => SqInv s B M k x Q E 0 s' := by
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s.setReg32 .r15 4, rfl, WP.block_nil ?_⟩
  have i₀ : SqInv s B M k x Q E 4 (s.setReg32 .r15 4) :=
    ⟨by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl, by
      show ExpSt s.mem B M k x Q (fun p => E p * 2 ^ (4 - 4))
      simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]; exact h, OutW.refl _ _,
      fun r _ _ _ _ _ _ _ _ _ h15 => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ h15], rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (c := .ne) (Q := SqInv s B M k x Q E 0)
    (fun n t => 1 ≤ n ∧ n ≤ 4 ∧ SqInv s B M k x Q E n t) ?_ 4 _ ⟨by decide, by decide, i₀⟩
  intro n t ⟨h1, h4, hI⟩
  have hB' : t.gpr .rbx = B := by
    rw [hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  refine WP.seq (WP.mono (sq_ok hB' (hs.congr hI.wr) hR hI.st) fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 n := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hI.r15
  refine WP.mono (r15Dec_ok h1 h4 r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₂⟩ => ?_
  have hI' : SqInv s B M k x Q E (n - 1) t₂ := ⟨r15₂, ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
    by rw [k₂.2.1, rd₁, hI.rd], by rw [k₂.2.2, wr₁, hI.wr], by rw [x₂, x₁, hI.mxcsr]⟩
  · simp only [eval, z₂, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · exact .inl ⟨by simp, hI'⟩
    · exact .inr ⟨by simp only [decide_eq_false (show ¬ (n - 1 = 0) by omega), Bool.not_false], n - 1,
        by omega, by omega, by omega, hI'⟩
  · rw [me₂]
    refine ⟨st₁.ar, st₁.tab, st₁.y, fun hq p hp => ?_⟩
    rw [st₁.yv hq p hp, show 2 * (E p * 2 ^ (4 - n)) = E p * 2 ^ (4 - (n - 1)) by
      rw [show 4 - (n - 1) = (4 - n) + 1 by omega, Nat.pow_succ]; grind]
  · rw [me₂]; exact hI.frame.trans f₁
  · rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9]
    exact hI.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10

end VG.Proof.Bignum.X86_64.AmmSym
