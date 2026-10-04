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
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off writeW_outside)
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
      Out2 B oY 160 s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (amm2_ok hB hs h.ar (by decide) (by decide) (by decide) (by decide) h.y h.y)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hf (.inl (by decide)) (by decide),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact VG.Proof.Bignum.mont_sq (hR p hp) (h.yv hq p hp) (hv p hp).2

/-- `Y := Y S / R`: `x^E R` and `S ≡ x^v R` give `x^(E+v) R`. -/
theorem mulS_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (h : ExpSt s.mem B M k x Q E) (gs : ∀ p < 2, Good s.mem B M oS p)
    (vs : Q → ∀ p < 2, val52 s.mem B (D * p + oS) % M p = x p ^ v p * 2 ^ (52 * 20) % M p) :
    WP isa (VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oS) s fun s' => ExpSt s'.mem B M k x Q (fun p => E p + v p) ∧
      Out2 B oY 160 s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (amm2_ok hB hs h.ar (by decide) (by decide) (by decide) (by decide) h.y gs)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hf (.inl (by decide)) (by decide),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
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
  frame : Out2 B oY 160 s₀.mem t.mem
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
      simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]; exact h, Out2.refl _ _ _ _,
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


theorem ea_at' (t : State) (r : Reg) (d : Nat) :
    t.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-- `V` of prime `p` rotated up by 4 bits. -/
theorem rotV_ok {s : State} {B : Addr} {p : Nat} (hp : p < 2) (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) :
    WP isa (.block [.mov .rax (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (D * p + oV))), .shift .ror .rax 60,
        .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (D * p + oV)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off B (D * p + oV)) ((word s.mem B (D * p + oV)).rotateRight 60) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hDp : D * p ≤ 3872 := by rcases D_mul hp with h | h <;> omega
  have hd : D * p + oV + 8 ≤ 2 * D := by simp only [oV, D] at hDp ⊢; omega
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (D * p + oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region hd (by decide); ⟨_, List.mem_append_right _ h, c⟩
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (D * p + oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region hd (by decide); ⟨_, h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (D * p + oV)) ((word s.mem B (D * p + oV)).rotateRight 60) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_at', hB, hld, hst]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩


theorem wp_seqs_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (VG.Impl.Bignum.X86_64.seqs a) s fun t => WP isa (VG.Impl.Bignum.X86_64.seqs b) t Q) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (a ++ b)) s Q := by
  induction a generalizing s with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact WP.seq h
    | cons d rest =>
      simp only [VG.Impl.Bignum.X86_64.seqs, List.cons_append] at h ⊢
      exact WP.seq (WP.mono (WP.seq_iff.mp h) fun t ht => ih (by simp) ht)

theorem Outside.limb' {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {c : Nat}
    (hc : c + 160 ≤ o ∨ o + n ≤ c) (hc' : c + 160 ≤ 2 ^ 64) {j : Nat} (hj : j < 20) :
    limb m' B c j = limb m B c j := by
  have := off_lt j hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [h.word (by omega) (by omega)]

/-- `S := T_v` for both primes. -/
theorem sel2_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (h : ExpSt s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (VG.Impl.Rsa.X86_64.CrtIfma.select 0 ++ VG.Impl.Rsa.X86_64.CrtIfma.select 1))
      s fun s' => ExpSt s'.mem B M k x Q E ∧
        (∀ p < 2, Good s'.mem B M oS p ∧
          (Q → val52 s'.mem B (D * p + oS) % M p = x p ^ nib s.mem B p * 2 ^ (52 * 20) % M p)) ∧
        (∀ p < 2, word s'.mem B (D * p + oV) = word s.mem B (D * p + oV)) ∧ Out2 B oS 160 s.mem s'.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3872 := rfl
  have hn := hs.nowrap
  refine wp_seqs_app (by simp [VG.Impl.Rsa.X86_64.CrtIfma.select]) (by simp [VG.Impl.Rsa.X86_64.CrtIfma.select])
    (WP.mono (select_ok (p := 0) (by decide) hB hs) fun s₁ ⟨l₁, o₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hB
  refine WP.mono (select_ok (p := 1) (by decide) hB₁ (hs.congr wr₁)) fun s₂ ⟨l₂, o₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  have f₁ : Out2 B oS 160 s.mem s₁.mem := Out2.of_outside (p := 0) (by decide) o₁
  have f₂ : Out2 B oS 160 s₁.mem s₂.mem := Out2.of_outside (p := 1) (by decide) o₂
  have v₁ : nib s₁.mem B 1 = nib s.mem B 1 := by
    unfold nib; rw [o₁.word (by simp only [oS, oV, D]; omega) (by simp only [oV]; omega)]
  have ex₁ := h.tab_of f₁ (.inl (by decide)) (by decide)
  -- entry 0 and entry 1
  have hv0 := nib_lt s.mem B 0
  have hv1 := nib_lt s.mem B 1
  have t0 := h.tab (nib s.mem B 0) hv0 0 (by decide)
  have t1 := ex₁ (nib s.mem B 1) hv1 1 (by decide)
  have L0 : ∀ l < 20, limb s₂.mem B (D * 0 + oS) l = limb s.mem B (D * 0 + (oTab + 160 * nib s.mem B 0)) l :=
    fun l hl => by
      rw [Outside.limb' o₂ (.inl (by simp only [oS, D]; omega)) (by simp only [oS]; omega) hl, l₁ l hl, Nat.add_assoc]
  have L1 : ∀ l < 20, limb s₂.mem B (D * 1 + oS) l = limb s₁.mem B (D * 1 + (oTab + 160 * nib s.mem B 1)) l :=
    fun l hl => by rw [l₂ l hl, v₁, Nat.add_assoc]
  refine ⟨⟨?_, h.tab_of (f₁.trans f₂) (.inl (by decide)) (by decide), fun p hp => ?_, fun hq p hp => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, f₁.trans f₂, fun r r1 r2 r3 r4 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [x₂, x₁]⟩
  · exact (h.ar.of_out2 f₁ (by decide) (by decide)).of_out2 f₂ (by decide) (by decide)
  · exact (h.y p hp).of_out2 hp (f₁.trans f₂) (.inl (by decide)) (by decide) (by decide)
  · rw [(f₁.trans f₂).val hp (.inl (by decide)) (by decide) (by decide)]; exact h.yv hq p hp
  · rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · exact ⟨t0.1.of_limbs L0, fun hq => by rw [val52_of_limbs L0]; exact t0.2 hq⟩
    · exact ⟨t1.1.of_limbs L1, fun hq => by rw [val52_of_limbs L1]; exact t1.2 hq⟩
  · rw [(f₁.trans f₂).word_at hp (.inr (by decide)) (by decide) (by decide)]
  · rw [g₂ r r1 r2 r3 r4, g₁ r r1 r2 r3 r4]


/-- The rotations of both primes' `V`. -/
def rotCode (p : Nat) : List Instr :=
  [.mov .rax (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (D * p + oV))), .shift .ror .rax 60,
    .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (D * p + oV)) .rax]

theorem window_eq : VG.Impl.Rsa.X86_64.CrtIfma.window =
    [.block [.mov32 .r15 (.imm 4)],
      .loop (.seq (VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oY) (.block [.alu .sub .r15 (.imm 1)])) .ne] ++
    ((VG.Impl.Rsa.X86_64.CrtIfma.select 0 ++ VG.Impl.Rsa.X86_64.CrtIfma.select 1) ++
      [.block (rotCode 0 ++ rotCode 1), VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oS]) := by
  simp only [VG.Impl.Rsa.X86_64.CrtIfma.window, List.append_assoc]; rfl

/-- A window: `Y ≡ x^E R` becomes `x^(16 E + v) R` for the top 4 bits `v` of
`V`, which is rotated up by 4 bits. -/
theorem window_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (h : ExpSt s.mem B M k x Q E) :
    WP isa (VG.Impl.Bignum.X86_64.seqs VG.Impl.Rsa.X86_64.CrtIfma.window) s fun s' =>
      ExpSt s'.mem B M k x Q (fun p => E p * 16 + nib s.mem B p) ∧
      (∀ p < 2, word s'.mem B (D * p + oV) = (word s.mem B (D * p + oV)).rotateRight 60) ∧
      OutW B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3872 := rfl
  have hn := hs.nowrap
  rw [window_eq]
  refine wp_seqs_app (by simp) (by simp) (WP.mono (sqLoop_ok hB hs hR h) fun s₁ i₁ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by
    rw [i₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  have w₁ : ∀ p < 2, word s₁.mem B (D * p + oV) = word s.mem B (D * p + oV) := fun p hp =>
    i₁.frame.word_at hp (.inr (by decide)) (by decide) (by decide)
  have nib₁ : ∀ p < 2, nib s₁.mem B p = nib s.mem B p := fun p hp => by unfold nib; rw [w₁ p hp]
  refine wp_seqs_app (by simp [VG.Impl.Rsa.X86_64.CrtIfma.select]) (by simp)
    (WP.mono (sel2_ok hB₁ (hs.congr i₁.wr) i₁.st) fun s₂ ⟨st₂, gs₂, w₂, f₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .rbx = B := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hB₁
  have hs₂ : Scr s₂ B (2 * D) := hs.congr (by rw [wr₂, i₁.wr])
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rotV_ok (p := 0) (by decide) hB₂ hs₂) fun s₃ ⟨m₃, k₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .rbx = B := by rw [k₃.gpr (by decide)]; exact hB₂
  refine WP.mono (rotV_ok (p := 1) (by decide) hB₃ (hs₂.congr k₃.2.2)) fun s₄ ⟨m₄, k₄, x₄⟩ => ?_
  have o₃ : Outside B (D * 0 + oV) 8 s₂.mem s₃.mem := by
    rw [m₃]; exact writeW_outside _ B _ (by simp only [oV]; omega)
  have o₄ : Outside B (D * 1 + oV) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ B _ (by simp only [oV]; omega)
  have f₄ : Out2 B oV 8 s₂.mem s₄.mem :=
    (Out2.of_outside (p := 0) (by decide) o₃).trans (Out2.of_outside (p := 1) (by decide) o₄)
  have hB₄ : s₄.gpr .rbx = B := by rw [k₄.gpr (by decide)]; exact hB₃
  have st₄ : ExpSt s₄.mem B M k x Q (fun p => E p * 2 ^ (4 - 0)) :=
    ⟨st₂.ar.of_out2 f₄ (by decide) (by decide), st₂.tab_of f₄ (.inr (by decide)) (by decide),
      fun p hp => (st₂.y p hp).of_out2 hp f₄ (.inl (by decide)) (by decide) (by decide),
      fun hq p hp => by rw [f₄.val hp (.inl (by decide)) (by decide) (by decide)]; exact st₂.yv hq p hp⟩
  refine WP.mono (mulS_ok (v := fun p => nib s₁.mem B p) hB₄ (hs₂.congr (by rw [k₄.2.2, k₃.2.2])) hR st₄
    (fun p hp => ((gs₂ p hp).1).of_out2 hp f₄ (.inl (by decide)) (by decide) (by decide))
    (fun hq p hp => by rw [f₄.val hp (.inl (by decide)) (by decide) (by decide)]; exact (gs₂ p hp).2 hq))
    fun s₅ ⟨st₅, f₅, g₅, rd₅, wr₅, x₅⟩ => ⟨?_, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
      by rw [rd₅, k₄.2.1, k₃.2.1, rd₂, i₁.rd], by rw [wr₅, k₄.2.2, k₃.2.2, wr₂, i₁.wr],
      by rw [x₅, x₄, x₃, x₂, i₁.mxcsr]⟩
  · refine ⟨st₅.ar, st₅.tab, st₅.y, fun hq p hp => ?_⟩
    rw [st₅.yv hq p hp, nib₁ p hp]
  · rw [f₅.word_at hp (.inr (by decide)) (by decide) (by decide)]
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · rw [o₄.word (by simp only [oV, D]; omega) (by simp only [oV]; omega), m₃, VG.Proof.Bignum.X86_64.word_writeW_self,
        w₂ 0 (by decide), w₁ 0 (by decide)]
    · rw [m₄, VG.Proof.Bignum.X86_64.word_writeW_self, o₃.word (by simp only [oV, D]; omega) (by simp only [oV]; omega),
        w₂ 1 (by decide), w₁ 1 (by decide)]
  · exact ((OutW.ofY i₁.frame).trans (OutW.ofS f₂)).trans ((OutW.ofV f₄).trans (OutW.ofY f₅))
  · rw [g₅ r r1 r2 r3 r4 r5 r6 r7 r8 r9, k₄.gpr (by simp [r1]), k₃.gpr (by simp [r1]), g₂ r r1 r2 r3 r5]
    exact i₁.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10

end VG.Proof.Bignum.X86_64.AmmSym
