module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Win
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Tab
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# RSA with AVX512_IFMA on x86-64, any size: the exponentiations

`expLoop` puts `Y` and `X` into Montgomery form and builds the table
(`convTab_ok`), then does a window for each of the digits of `w` bits of
the exponents `e` (at `oD` of each region, most significant first,
`digit`), from the first, `k0`, that holds a bit of an exponent below
`2^(8 E)` (`digIter_ok`): `Y ≡ x^(e / T^(ND - i)) R` becomes
`x^(e / T^(ND - i - 1)) R`. After all of them `Y ≡ x^e R`, and a last
iteration multiplies by `Fin` (`finIter_ok`): `Y ≡ x^e Fin` (`expLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (mont_out wp_seqs_app ofs_off0 se_ofNat)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- Digit `i` of `e` in base `T`, of `ND` digits, most significant first. -/
def digit (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (e i : Nat) : Nat := e / l.T ^ (l.ND - 1 - i) % l.T

theorem T_pos (hl : LayOk l) : 0 < l.T := by have := hl.T_bounds; omega

theorem digit_lt (hl : LayOk l) (e i : Nat) : digit l e i < l.T := Nat.mod_lt _ (T_pos hl)

/-- The digits up to `i`, and one more. -/
theorem pref_step {e i : Nat} (hi : i < l.ND) :
    e / l.T ^ (l.ND - i) * l.T + digit l e i = e / l.T ^ (l.ND - (i + 1)) := by
  rw [digit, show l.ND - 1 - i = l.ND - (i + 1) by omega_using [hi],
    show l.ND - i = l.ND - (i + 1) + 1 by omega_using [hi], Nat.pow_succ, ← Nat.div_div_eq_div_mul,
    Nat.div_add_mod']

/-- Below the first digit `k0`, the digits of an exponent below `2^(8 E)` are zero. -/
theorem pref_k0 (hl : LayOk l) {e : Nat} (he : e < 2 ^ (8 * l.E)) : e / l.T ^ (l.ND - l.k0) = 0 := by
  refine Nat.div_eq_of_lt (Nat.lt_of_lt_of_le he ?_)
  rw [Lay.T, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by rcases hl with rfl | rfl | rfl <;> decide)

/-- The digit bytes outside `Y`, `S` and `V`. -/
theorem OutW.dig (hl : LayOk l) {B : Addr} {m m' : Mem} (h : OutW l B m m') {p i : Nat} (hp : p < 2)
    (hi : i < l.ND) : dig l m' B p i = dig l m B p i := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_dAt hl hi
  have hD := hl.D_bounds
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  refine congrArg (fun b : BitVec 8 => nibOf l i b.toNat) (h _ fun p' hp' => ?_)
  rw [ofs_off0 B (by omega_using [d2, o7, o10, hD, hDp])]
  rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;>
    omega_using [o2, o4, o6, o7, o8, d1, d2, h1, h2, o10]

/-- The next digit, `ZF` after the last window, `Y Fin`'s. -/
theorem r13Inc_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i ≤ l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.ND + 1)))]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = l.ND + 1)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  have hE : l.ND + 1 < 2 ^ 31 := by rcases hl with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = l.ND + 1)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h13, se_ofNat hE, ofNat_add_one]
    and_intros
    · rw [ofNat_sub_beq (by omega_using [hi, hE]) (by omega_using [hE])]
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

theorem ExpSt.of_outV (hl : LayOk l) {m m' : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (h : ExpSt l m B M k x Q E) (f : Out2 l B l.oV 8 m m') : ExpSt l m' B M k x Q E := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  exact ⟨h.ar.of_out2 hl f (by omega_using [o2, o8]) (by omega_using [o8, o10]),
      h.tab_of hl f (.inr (by omega_using [o5, o8])) (by omega_using [o8, o10]),
    fun p hp => (h.y p hp).of_out2 hl hp f (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10]),
    fun hq p hp => by rw [f.val hl hp (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10])]; exact h.yv hq p hp⟩

theorem ExpSt.congrE {m : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E E' : Nat → Nat}
    (h : ExpSt l m B M k x Q E) (e : ∀ p < 2, E p = E' p) : ExpSt l m B M k x Q E' :=
  ⟨h.ar, h.tab, h.y, fun hq p hp => by rw [← e p hp]; exact h.yv hq p hp⟩

/-- `m'` agrees with `m` but on `Y`, `X`, `S`, `V` and the table of each region. -/
def OutE (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (m m' : Mem) : Prop :=
  ∀ a, (∀ p < 2, (ofs B a < l.D * p + l.oY ∨ l.D * p + l.oY + 2 * l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oS ∨ l.D * p + l.oS + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oV ∨ l.D * p + l.oV + 8 ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oTab ∨ l.D * p + l.oTab + l.T * l.NB ≤ ofs B a)) → m' a = m a

theorem OutE.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : OutE l B m₁ m₂) (h₂ : OutE l B m₂ m₃) : OutE l B m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem OutE.ofW {B : Addr} {m m' : Mem} (h : OutW l B m m') : OutE l B m m' :=
  fun a ha => h a fun p hp => ⟨(ha p hp).1.imp_right fun h => by omega, (ha p hp).2.1, (ha p hp).2.2.1⟩

/-- What `convTab` writes: `Y`, `X`, `S` and the table, which are contiguous. -/
theorem OutE.ofConv {B : Addr} {m m' : Mem} (h : Out2 l B l.oY (l.oTab + l.T * l.NB - l.oY) m m') : OutE l B m m' :=
  fun a ha => h a fun p hp => by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    obtain ⟨h1, h2, -, h4⟩ := ha p hp
    omega_using [h1, h2, h4, o2, o4, o5]

theorem OutE.word_at {B : Addr} {m m' : Mem} (h : OutE l B m m') {p c : Nat} (hp : p < 2)
    (hY : c + 8 ≤ l.oY ∨ l.oY + 2 * l.NB ≤ c) (hS : c + 8 ≤ l.oS ∨ l.oS + l.NB ≤ c) (hV : c + 8 ≤ l.oV ∨ l.oV + 8 ≤ c)
    (hT : c + 8 ≤ l.oTab ∨ l.oTab + l.T * l.NB ≤ c) (hcD : c + 8 ≤ l.D) (hD : l.D + l.NB ≤ 2 ^ 20) :
    word m' B (l.D * p + c) = word m B (l.D * p + c) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mul (l := l) hp with h | h <;> omega_using [hcD, hD, hi, h])]
  have : i < 8 := hi
  rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;> omega_using [hY, hS, hV, hT,
      this, h1, h2, hcD, o2, o4, o5, o8, o10]

theorem Good.of_outE (hl : LayOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p)
    (hp : p < 2) (h : OutE l B m m')
    (hY : c + l.NB ≤ l.oY ∨ l.oY + 2 * l.NB ≤ c) (hS : c + l.NB ≤ l.oS ∨ l.oS + l.NB ≤ c)
    (hV : c + l.NB ≤ l.oV ∨ l.oV + 8 ≤ c) (hT : c + l.NB ≤ l.oTab ∨ l.oTab + l.T * l.NB ≤ c)
    (hcD : c + l.NB ≤ l.D) :
    Good l m' B M c p ∧ val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) := by
  have e : ∀ j < l.L, limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := fun j hj => by
    have := off_lt hl hj
    show (word m' B _).toNat = (word m B _).toNat
    rw [Nat.add_assoc, h.word_at hp (by omega_using [hY, this]) (by omega_using [hS, this]) (by omega_using [hV, this])
        (by omega_using [hT, this]) (by omega_using [hcD, this]) hl.D_bounds.2]
  exact ⟨g.of_limbs e, val52_of_limbs e⟩

/-- After the digits below `i` of the exponents `e`, from `t₀`. -/
structure DigInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (e : Nat → Nat)
    (i : Nat) (t : State) : Prop where
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  st : ExpSt l t.mem B M k x Q (fun p => e p / l.T ^ (l.ND - i))
  frame : OutW l B t₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → r ≠ .r15 → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr

/-- The body of the loop over the digits. -/
def digBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prog isa :=
  VG.Impl.Bignum.X86_64.seqs (window l ++
    ([.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (l.ND + 1)))]] : List (Prog isa)))

/-- Digit `i` of both exponents. -/
theorem digIter_ok (hl : LayOk l) {t₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat} {i : Nat}
    (hi : i < l.ND) (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D))
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (hd : ∀ p < 2, ∀ i < l.ND, dig l t₀.mem B p i = digit l (e p) i) (h : DigInv l t₀ B M k x Q e i t) :
    WP isa (digBody l) t fun t' => DigInv l t₀ B M k x Q e (i + 1) t' ∧ t'.zf = some false := by
  have hBt : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hB
  have hdt : ∀ p < 2, dig l t.mem B p i = digit l (e p) i := fun p hp => by
    rw [h.frame.dig hl hp hi]; exact hd p hp i hi
  refine wp_seqs_app (by simp [window]) (by simp)
    (WP.mono (window_ok hl hi h.r13 hBt (hs.congr h.wr) hR h.st fun p hp => by rw [hdt p hp]; exact digit_lt hl _ _)
      fun t₁ ⟨st₁, _, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have r13₁ : t₁.gpr .r13 = BitVec.ofNat 64 i := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.r13
  refine WP.mono (r13Inc_ok hl (Nat.le_of_lt hi) r13₁) fun t₂ ⟨r13₂, z₂, k₂, me₂, x₂⟩ =>
    ⟨⟨r13₂, ?_, by rw [me₂]; exact h.frame.trans f₁, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 => ?_,
      by rw [k₂.2.1, rd₁, h.rd], by rw [k₂.2.2, wr₁, h.wr], by rw [x₂, x₁, h.mxcsr]⟩,
      by rw [z₂, decide_eq_false (by omega_using [hi] : ¬ (i + 1 = l.ND + 1))]⟩
  · rw [me₂]
    exact st₁.congrE fun p hp => by rw [hdt p hp, pref_step hi]
  · rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r11]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11

/-- What the loop over the digits leaves, from `t₀`: `Y ≡ x^e Fin`. -/
structure FinOut (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (B : Addr) (M x : Nat → Nat) (Q : Prop) (e : Nat → Nat)
    (t : State) : Prop where
  y : ∀ p < 2, Good l t.mem B M l.oY p ∧ (Q → val52 l t.mem B (l.D * p + l.oY) % M p =
    x p ^ e p * val52 l t₀.mem B (l.D * p + l.oFin) % M p)
  frame : OutW l B t₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r13 → r ≠ .r15 → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr

theorem OutW.fin (hl : LayOk l) {B : Addr} {m m' : Mem} (h : OutW l B m m') {M : Nat → Nat} {p : Nat} (hp : p < 2)
    (g : Good l m B M l.oFin p) :
    Good l m' B M l.oFin p ∧ val52 l m' B (l.D * p + l.oFin) = val52 l m B (l.D * p + l.oFin) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  exact g.of_outE hl hp (OutE.ofW h) (.inr (by omega_using [o2, o9])) (.inr (by omega_using [o4, o9]))
    (.inr (by omega_using [o8, o9])) (.inr (by omega_using [o5, o9])) (by omega_using [o9, o10])

/-- After the last digit: `Y := Y Fin / R`, `ZF`. -/
theorem finIter_ok (hl : LayOk l) {t₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (gf : ∀ p < 2, Good l t₀.mem B M l.oFin p) (h : DigInv l t₀ B M k x Q e l.ND t) :
    WP isa (digBody l) t fun t' => FinOut l t₀ B M x Q e t' ∧ t'.zf = some true := by
  have hBt : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hB
  have hst : Scr t B (2 * l.D) := hs.congr h.wr
  have gft := fun p (hp : p < 2) => h.frame.fin hl hp (gf p hp)
  refine wp_seqs_app (by simp [window]) (by simp)
    (WP.mono (finWin_ok hl h.r13 hBt hst h.st.ar h.st.y (fun p hp => (gft p hp).1))
      fun t₁ ⟨v₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have h13₁ : t₁.gpr .r13 = BitVec.ofNat 64 l.ND := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact h.r13
  refine WP.mono (r13Inc_ok hl (Nat.le_refl _) h13₁) fun t₂ ⟨_, z₂, k₂, me₂, x₂⟩ =>
    ⟨⟨fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 => ?_, ?_, ?_, ?_⟩, by rw [z₂]; simp⟩
  · rw [me₂]
    refine ⟨(v₁ p hp).1, fun hq => ?_⟩
    rw [← (gft p hp).2]
    have := mont_out (hR p hp) (h.st.yv hq p hp) (v₁ p hp).2
    rwa [Nat.sub_self, Nat.pow_zero, Nat.div_one] at this
  · rw [me₂]; exact h.frame.trans f₁
  · rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r11]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  · rw [k₂.2.1, rd₁, h.rd]
  · rw [k₂.2.2, wr₁, h.wr]
  · rw [x₂, x₁, h.mxcsr]

/-- The loop over the digits, from digit `ND + 1 - n` (digit `ND` the last window, `Y Fin`). -/
theorem digLoop_ok (hl : LayOk l) {t₀ : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (gf : ∀ p < 2, Good l t₀.mem B M l.oFin p)
    (hd : ∀ p < 2, ∀ i < l.ND, dig l t₀.mem B p i = digit l (e p) i) :
    ∀ n t, 1 ≤ n → n ≤ l.ND + 1 → DigInv l t₀ B M k x Q e (l.ND + 1 - n) t →
      WP isa (.loop (digBody l) .ne) t (FinOut l t₀ B M x Q e) := by
  intro n t h1 hE hI
  refine WP.loop (M := isa) (c := .ne) (Q := FinOut l t₀ B M x Q e)
    (fun n t => 1 ≤ n ∧ n ≤ l.ND + 1 ∧ DigInv l t₀ B M k x Q e (l.ND + 1 - n) t) ?_ n t ⟨h1, hE, hI⟩
  intro n t ⟨h1, hE, hI⟩
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine WP.mono (finIter_ok (k := k) (x := x) (Q := Q) (e := e) hl hB hs hR gf (by rw [Nat.add_sub_cancel] at hI; exact hI))
      fun t' ⟨hO, hz⟩ => ?_
    simp only [eval, hz, Option.map_some]
    exact .inl ⟨by simp, hO⟩
  · refine WP.mono (digIter_ok hl (i := l.ND + 1 - n) (by omega_using [hn, hE]) hB hs hR hd hI) fun t' ⟨hI', hz⟩ => ?_
    simp only [eval, hz, Option.map_some]
    refine .inr ⟨by simp, n - 1, by omega_using [hn], by omega_using [hn], by omega_using [hE],
      by rw [show l.ND + 1 - (n - 1) = l.ND + 1 - n + 1 by omega_using [hE, hn]]; exact hI'⟩

theorem k0_le (hl : LayOk l) : l.k0 ≤ l.ND := by rcases hl with rfl | rfl | rfl <;> decide

/-- The exponentiations: `Y ≡ x^e R` for the exponents `e` below `2^(8 E)`,
whose digits are at `oD`, from `Y ≡ R` and `X ≡ x R`. -/
theorem expLoop_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hc : ConvPre l s B M k x Q) (gf : ∀ p < 2, Good l s.mem B M l.oFin p)
    (he : ∀ p < 2, e p < 2 ^ (8 * l.E)) (hd : ∀ p < 2, ∀ i < l.ND, dig l s.mem B p i = digit l (e p) i) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (expLoop l)) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧ (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
        x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧ OutE l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hs := hc.scr
  have hR := hc.hR
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hk0 := k0_le hl
  refine wp_seqs_app (by simp [convTab]) (by simp)
    (WP.mono (convTab_ok hl hc) fun s₁ t₁ => ?_)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg32 .r13 (BitVec.ofNat 32 l.k0), rfl, WP.block_nil ?_⟩
  generalize hu : s₁.setReg32 .r13 (BitVec.ofNat 32 l.k0) = u
  have hk32 : l.k0 < 2 ^ 32 := by rcases hl with rfl | rfl | rfl <;> decide
  have eu : u.mem = s₁.mem ∧ u.rd = s₁.rd ∧ u.wr = s₁.wr ∧ u.mxcsr = s₁.mxcsr ∧
      u.gpr .r13 = BitVec.ofNat 64 l.k0 ∧ ∀ r, r ≠ .r13 → u.gpr r = s₁.gpr r := by
    rw [← hu]
    refine ⟨rfl, rfl, rfl, rfl, ?_, fun r hr => by rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]⟩
    rw [State.setReg32, RegUpd.gpr_setReg_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := l.k0) (b := 2 ^ 32) hk32,
      Nat.mod_eq_of_lt (a := l.k0) (b := 2 ^ 64) (by omega_using [hk32])]
  obtain ⟨mu, rdu, wru, xu, r13u, gu⟩ := eu
  have hBu : u.gpr .rbx = B := by rw [gu _ (by decide)]; exact t₁.rbx
  have hsu : Scr u B (2 * l.D) := hs.congr (by rw [wru, t₁.wr])
  have gfu : ∀ p < 2, Good l u.mem B M l.oFin p ∧
      val52 l u.mem B (l.D * p + l.oFin) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp =>
    (gf p hp).of_outE hl hp (by rw [mu]; exact OutE.ofConv t₁.frame) (.inr (by omega_using [o2, o9]))
      (.inr (by omega_using [o4, o9])) (.inr (by omega_using [o8, o9])) (.inr (by omega_using [o5, o9]))
      (by omega_using [o9, o10])
  have hdu : ∀ p < 2, ∀ i < l.ND, dig l u.mem B p i = digit l (e p) i := fun p hp i hi => by
    rw [← hd p hp i hi, mu]
    obtain ⟨d1, d2⟩ := lay_dAt hl hi
    refine congrArg (fun b : BitVec 8 => nibOf l i b.toNat) (t₁.frame _ fun p' hp' => ?_)
    have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
    rw [ofs_off0 B (by have := hs.nowrap; omega_using [d2, o7, o10, hDp, this])]
    rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;>
      omega_using [o2, o5, o6, o7, d1, d2, h2, o10, h1]
  have st₀ : ExpSt l u.mem B M k x Q (fun p => e p / l.T ^ (l.ND - (l.ND + 1 - (l.ND + 1 - l.k0)))) := by
    rw [mu, show l.ND + 1 - (l.ND + 1 - l.k0) = l.k0 by omega_using [hk0]]
    refine ExpSt.congrE ⟨t₁.ar, t₁.tab, t₁.yg, t₁.yv⟩ fun p hp => ?_
    rw [pref_k0 hl (he p hp)]
  refine WP.mono (digLoop_ok hl hBu hsu hR (fun p hp => (gfu p hp).1) hdu (l.ND + 1 - l.k0) u (by omega_using [hk0])
      (by omega_using [])
    ⟨by rw [show l.ND + 1 - (l.ND + 1 - l.k0) = l.k0 by omega_using [hk0]]; exact r13u, st₀, OutW.refl _ _,
      fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s' b' => ?_
  refine ⟨fun p hp => ⟨(b'.y p hp).1, fun hq => by rw [(b'.y p hp).2 hq, (gfu p hp).2]⟩, ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 => ?_, ?_, ?_, ?_⟩
  · exact (OutE.ofConv t₁.frame).trans (mu ▸ OutE.ofW b'.frame)
  · rw [b'.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11, gu r r10]
    exact t₁.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  · rw [b'.rd, rdu, t₁.rd]
  · rw [b'.wr, wru, t₁.wr]
  · rw [b'.mxcsr, xu, t₁.mxcsr]

end VG.Proof.Bignum.X86_64.Ifma
