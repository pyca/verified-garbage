import VerifiedGarbage.Proof.Bignum.X86_64.IfmaExp

/-!
# RSA with AVX512_IFMA on x86-64: the vector code

`vec` (`vec_ok`): within Intel's MXCSR prologue and epilogue (the caller's
MXCSR saved at `oMx`, `0x1FBF` loaded, and the saved value, bits 31:16
cleared, restored), `X` and `Y` into Montgomery form for `R = 2¹⁰⁴⁰` (by
`K1 ≡ 2¹⁰⁵⁶`, as they hold `x 2¹⁰²⁴` and `2¹⁰²⁴`), the exponentiations,
and `Y := Y Fin / R`: `Y ≡ x^e Fin`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oK1 oTab oS oV oX oY oE oFin oMx mask52)

theorem Scr.mono {s : State} {B : Addr} {Z Z' : Nat} (h : Scr s B Z) (hz : Z' ≤ Z) : Scr s B Z' :=
  let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := h.wr
  ⟨⟨B₀, o, L, hm, hb, by omega, hL'⟩, by have := h.nowrap; omega⟩

/-- The prologue's first half: the caller's MXCSR, bits 31:16 cleared, at `oMx`. -/
theorem mxSave_ok {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D + 8)) :
    WP isa (.block [.stmxcsr (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx),
        .mov32 .r11 (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx)), .alu32 .and .r11 (.imm 0xFFFF),
        .store32 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx) .r11]) s fun s' =>
      s'.mem = (s.mem.writeW (off B oMx) s.mxcsr).writeW (off B oMx) (s.mxcsr &&& 0xFFFF) ∧
      VG.Proof.MlKem.X86_64.Keep [.r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx) (n := 4) (by simp only [oMx]; omega) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx) (n := 4) (by simp only [oMx]; omega) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r11] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B oMx) s.mxcsr).writeW (off B oMx) (s.mxcsr &&& 0xFFFF) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_at', hB, hst, hld, Mem.readW_writeW_self32]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩


/-- The prologue's second half: `MXCSR := 0x1FBF`. -/
theorem mxSet_ok {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D + 8)) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (oMx + 4)) .rax,
        .ldmxcsr (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (oMx + 4)), .lfence]) s fun s' =>
      s'.mem = s.mem.writeW (off B (oMx + 4)) (0x1FBF : BitVec 32) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = 0x1FBF := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (oMx + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx + 4) (n := 4) (by simp only [oMx]; omega) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (oMx + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx + 4) (n := 4) (by simp only [oMx]; omega) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (oMx + 4)) (0x1FBF : BitVec 32) ∧ s'.mxcsr = 0x1FBF) (by
    xrun [ea_at', hB, hst, hld, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem and_ffff_hi (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_two_pow_sub_one]
  simp

/-- The epilogue: the saved MXCSR. -/
theorem mxRestore_ok {s : State} {B : Addr} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D + 8))
    (hv : s.mem.readW (off B oMx) 32 = v &&& 0xFFFF) :
    WP isa (.block [.ldmxcsr (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx oMx), .vop .vzeroupper]) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = v &&& 0xFFFF := by
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 oMx) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := oMx) (n := 4) (by simp only [oMx]; omega) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  rw [WP.block_cons_iff]
  refine ⟨{ s with mxcsr := v &&& 0xFFFF }, ?_, ?_⟩
  · simp only [exec, ea_at', hB, State.load32, hld, ite_true, Option.bind_some]
    rw [show s.mem.readW (B + BitVec.ofNat 64 oMx) 32 = v &&& 0xFFFF from hv, and_ffff_hi]; rfl
  · rw [WP.block_cons_iff]
    exact ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩


/-- Into Montgomery form: `X ≡ a c`, `K ≡ d` with `c d = R²` give `X K / R ≡ a R`. -/
theorem mont_into {X K X' a c d R m : Nat} (hR : Nat.Coprime R m) (hX : X % m = a * c % m) (hK : K % m = d % m)
    (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = a * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hX, hK, ← Nat.mul_mod]
  congr 1
  rw [Nat.mul_assoc, e, Nat.mul_assoc]

theorem mont_into0 {X K X' c d R m y : Nat} (hR : Nat.Coprime R m) (hX : X % m = 1 * c % m)
    (hK : K % m = d % m) (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = y ^ 0 * R % m := by
  rw [Nat.pow_zero]; exact mont_into hR hX hK e h

theorem mont_into1 {X K X' a c d R m : Nat} (hR : Nat.Coprime R m) (hX : X % m = a * c % m)
    (hK : K % m = d % m) (e : c * d = R * R) (h : X' * R % m = X * K % m) : X' % m = a ^ 1 * R % m := by
  rw [Nat.pow_one]; exact mont_into hR hX hK e h

/-- Out of Montgomery form: `Y ≡ b R` gives `Y F / R ≡ b F`. -/
theorem mont_out {Y F Y' b R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = b * R % m)
    (h : Y' * R % m = Y * F % m) : Y' % m = b * F % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, ← Nat.mul_mod]
  congr 1
  grind

/-- A word of a region outside `Y`, `S`, `V` and the table. -/
theorem OutE.word_at {B : Addr} {m m' : Mem} (h : OutE B m m') {p c : Nat} (hp : p < 2)
    (hY : c + 8 ≤ oY ∨ oY + 160 ≤ c) (hS : c + 8 ≤ oS ∨ oS + 160 ≤ c) (hV : c + 8 ≤ oV ∨ oV + 8 ≤ c)
    (hT : c + 8 ≤ oTab ∨ oTab + 2560 ≤ c) (hcD : c + 8 ≤ D) :
    word m' B (D * p + c) = word m B (D * p + c) := by
  have hD : D = 3712 := rfl
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mul hp with h | h <;> omega)]
  have : i < 8 := hi
  simp only [oY, oS, oV, oTab] at *
  rcases D_mul hp with h1 | h1 <;> rcases D_mul hp' with h2 | h2 <;> omega

theorem OutE.limb {B : Addr} {m m' : Mem} (h : OutE B m m') {p c : Nat} (hp : p < 2)
    (hY : c + 160 ≤ oY ∨ oY + 160 ≤ c) (hS : c + 160 ≤ oS ∨ oS + 160 ≤ c) (hV : c + 160 ≤ oV ∨ oV + 8 ≤ c)
    (hT : c + 160 ≤ oTab ∨ oTab + 2560 ≤ c) (hcD : c + 160 ≤ D) {j : Nat} (hj : j < 20) :
    limb m' B (D * p + c) j = limb m B (D * p + c) j := by
  have := off_lt j hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hp (by omega) (by omega) (by omega) (by omega) (by omega)]


theorem pow_split {a b c : Nat} (h : a + b = c + c) : 2 ^ a * 2 ^ b = 2 ^ c * 2 ^ c := by
  rw [← Nat.pow_add, ← Nat.pow_add, h]

theorem Out2.toOutside {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 B o n m m') (hon : o + n ≤ D) :
    Outside B 0 (2 * D) m m' := fun a ha => h a fun p hp => by
  have hD : D = 3712 := rfl
  rcases ha with ha | ha
  · omega
  · have : D * p ≤ D := by rcases D_mul hp with h | h <;> omega
    exact .inr (by omega)

theorem OutE.toOutside {B : Addr} {m m' : Mem} (h : OutE B m m') : Outside B 0 (2 * D) m m' :=
  fun a ha => h a fun p hp => by
    have hD : D = 3712 := rfl
    rcases ha with ha | ha
    · omega
    · have : D * p ≤ D := by rcases D_mul hp with h | h <;> omega
      simp only [oY, oS, oV, oTab] at *
      exact ⟨.inr (by omega), .inr (by omega), .inr (by omega), .inr (by omega)⟩

theorem Out2.byte {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 B o n m m') {p i : Nat} (hp : p < 2)
    (hi : i < 128) (ho : o + n ≤ oE ∨ oE + 128 ≤ o) (hoD : o + n ≤ D) :
    m' (off B (D * p + oE + i)) = m (off B (D * p + oE + i)) := by
  have hD : D = 3712 := rfl
  refine h _ fun p' hp' => ?_
  rw [ofs_off0 B (by rcases D_mul hp with h | h <;> simp only [oE] at * <;> omega)]
  rcases D_mul hp with h1 | h1 <;> rcases D_mul hp' with h2 | h2 <;> simp only [oE] at * <;> omega

theorem Good.of_outE {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good m B M c p) (hp : p < 2)
    (h : OutE B m m')
    (hY : c + 160 ≤ oY ∨ oY + 160 ≤ c) (hS : c + 160 ≤ oS ∨ oS + 160 ≤ c) (hV : c + 160 ≤ oV ∨ oV + 8 ≤ c)
    (hT : c + 160 ≤ oTab ∨ oTab + 2560 ≤ c) (hcD : c + 160 ≤ D) :
    Good m' B M c p ∧ val52 m' B (D * p + c) = val52 m B (D * p + c) := by
  have e : ∀ j < 20, limb m' B (D * p + c) j = limb m B (D * p + c) j := fun j hj =>
    h.limb hp hY hS hV hT hcD hj
  exact ⟨g.of_limbs e, val52_of_limbs e⟩

/-- The vector code inside the MXCSR prologue and epilogue. -/
theorem vecBody_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * D)) (ar : Ar s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (gx : ∀ p < 2, Good s.mem B M oX p) (gy : ∀ p < 2, Good s.mem B M oY p)
    (gk : ∀ p < 2, Good s.mem B M oK1 p) (gf : ∀ p < 2, Good s.mem B M oFin p)
    (vx : Q → ∀ p < 2, val52 s.mem B (D * p + oX) % M p = x p * 2 ^ 1024 % M p)
    (vy : Q → ∀ p < 2, val52 s.mem B (D * p + oY) % M p = 1 * 2 ^ 1024 % M p)
    (vk : Q → ∀ p < 2, val52 s.mem B (D * p + oK1) % M p = 2 ^ 1056 % M p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs ([VG.Impl.Rsa.X86_64.CrtIfma.amm oX oX oK1,
        VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oK1] ++ VG.Impl.Rsa.X86_64.CrtIfma.expLoop ++
        [VG.Impl.Rsa.X86_64.CrtIfma.amm oY oY oFin])) s fun s' =>
      (∀ p < 2, Good s'.mem B M oY p ∧
        (Q → val52 s'.mem B (D * p + oY) % M p =
          x p ^ ev s.mem B p 128 * val52 s.mem B (D * p + oFin) % M p)) ∧
      Outside B 0 (2 * D) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : D = 3712 := rfl
  have e2 : 2 ^ 1024 * 2 ^ 1056 = 2 ^ (52 * 20) * 2 ^ (52 * 20) := by
    simp only [← Nat.pow_add, Nat.reduceAdd, Nat.reduceMul]
  refine wp_seqs_app (by simp) (by simp) (wp_seqs_app (by simp) (by simp [VG.Impl.Rsa.X86_64.CrtIfma.expLoop,
    VG.Impl.Rsa.X86_64.CrtIfma.tabBuild]) ?_)
  refine WP.seq (WP.mono (amm2_ok hB hs ar (by decide) (by decide) (by decide) (by decide) gx gk)
    fun s₁ ⟨v₁, f₁, ar₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB
  have hs₁ : Scr s₁ B (2 * D) := hs.congr wr₁
  have gy₁ : ∀ p < 2, Good s₁.mem B M oY p := fun p hp => (gy p hp).of_out2 hp f₁ (.inl (by decide)) (by decide)
    (by decide)
  have gk₁ : ∀ p < 2, Good s₁.mem B M oK1 p := fun p hp => (gk p hp).of_out2 hp f₁ (.inr (by decide)) (by decide)
    (by decide)
  refine WP.mono (amm2_ok hB₁ hs₁ ar₁ (by decide) (by decide) (by decide) (by decide) gy₁ gk₁)
    fun s₂ ⟨v₂, f₂, ar₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  have hB₂ : s₂.gpr .rbx = B := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hB₁
  have hs₂ : Scr s₂ B (2 * D) := hs₁.congr wr₂
  have gx₂ : ∀ p < 2, Good s₂.mem B M oX p := fun p hp => (v₁ p hp).1.of_out2 hp f₂ (.inr (by decide))
    (by decide) (by decide)
  have vx₂ : Q → ∀ p < 2, val52 s₂.mem B (D * p + oX) % M p = x p ^ 1 * 2 ^ (52 * 20) % M p := fun hq p hp => by
    rw [f₂.val hp (.inr (by decide)) (by decide) (by decide)]
    exact mont_into1 (hR p hp) (vx hq p hp) (vk hq p hp) e2 (v₁ p hp).2
  have vy₂ : Q → ∀ p < 2, val52 s₂.mem B (D * p + oY) % M p = x p ^ 0 * 2 ^ (52 * 20) % M p := fun hq p hp => by
    have e := (v₂ p hp).2
    rw [f₁.val hp (.inl (by decide)) (by decide) (by decide), f₁.val hp (.inr (by decide)) (by decide)
      (by decide)] at e
    exact mont_into0 (hR p hp) (vy hq p hp) (vk hq p hp) e2 e
  refine WP.mono (expLoop_ok hB₂ hs₂ ar₂ hR (fun p hp => (v₂ p hp).1) gx₂ vy₂ vx₂)
    fun s₃ ⟨st₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hB₃ : s₃.gpr .rbx = B := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  -- `Fin`, unchanged
  have gf₃ : ∀ p < 2, Good s₃.mem B M oFin p ∧ val52 s₃.mem B (D * p + oFin) = val52 s.mem B (D * p + oFin) :=
    fun p hp => by
      have g₁ := (gf p hp).of_out2 hp f₁ (.inr (by decide)) (by decide) (by decide)
      have g₂ := g₁.of_out2 hp f₂ (.inr (by decide)) (by decide) (by decide)
      obtain ⟨g₃, e₃⟩ := g₂.of_outE hp f₃ (.inr (by decide)) (.inr (by decide)) (.inr (by decide))
        (.inr (by decide)) (by decide)
      refine ⟨g₃, ?_⟩
      rw [e₃, f₂.val hp (.inr (by decide)) (by decide) (by decide),
        f₁.val hp (.inr (by decide)) (by decide) (by decide)]
  have hev : ∀ p < 2, ev s₂.mem B p 128 = ev s.mem B p 128 := fun p hp =>
    ev_congr 128 fun i hi => (f₂.byte hp hi (.inl (by decide)) (by decide)).trans
      (f₁.byte hp hi (.inl (by decide)) (by decide))
  refine WP.mono (amm2_ok hB₃ (hs₂.congr wr₃) st₃.ar (by decide) (by decide) (by decide) (by decide) st₃.y
    (fun p hp => (gf₃ p hp).1)) fun s₄ ⟨v₄, f₄, ar₄, g₄, rd₄, wr₄, x₄⟩ =>
      ⟨fun p hp => ⟨(v₄ p hp).1, fun hq => ?_⟩, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_,
        by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], by rw [x₄, x₃, x₂, x₁]⟩
  · have e := (v₄ p hp).2
    rw [(gf₃ p hp).2] at e
    rw [← hev p hp]
    exact mont_out (hR p hp) (st₃.yv hq p hp) e
  · exact ((f₁.toOutside (by decide)).trans (f₂.toOutside (by decide))).trans
      (f₃.toOutside.trans (f₄.toOutside (by decide)))
  · rw [g₄ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₃ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12,
      g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9]


/-! ## Writes above both regions -/

theorem writeW32_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 2 ^ 64) :
    Outside base d 4 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

section
variable {m m' : Mem} {B : Addr} {n : Nat} (h : Outside B (2 * D) n m m')
include h

theorem hi_word {p c : Nat} (hp : p < 2) (hc : c + 8 ≤ D) : word m' B (D * p + c) = word m B (D * p + c) :=
  h.word (.inl (by rcases D_mul hp with h | h <;> simp only [D] at * <;> omega))
    (by rcases D_mul hp with h | h <;> simp only [D] at * <;> omega)

theorem hi_limb {p c : Nat} (hp : p < 2) (hc : c + 160 ≤ D) {j : Nat} (hj : j < 20) :
    limb m' B (D * p + c) j = limb m B (D * p + c) j := by
  have := off_lt j hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, hi_word h hp (by omega)]

theorem hi_val {p c : Nat} (hp : p < 2) (hc : c + 160 ≤ D) : val52 m' B (D * p + c) = val52 m B (D * p + c) :=
  val52_of_limbs fun _ hj => hi_limb h hp hc hj

theorem Good.of_hi {M : Nat → Nat} {p c : Nat} (g : Good m B M c p) (hp : p < 2) (hc : c + 160 ≤ D) :
    Good m' B M c p :=
  g.of_limbs fun _ hj => hi_limb h hp hc hj

theorem Ar.of_hi {M k : Nat → Nat} (a : Ar m B M k) : Ar m' B M k := by
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [hi_limb h hp (by decide) hj]; exact a.mlt p hp j hj
  · rw [hi_val h hp (by decide)]; exact a.mv p hp
  · rw [Nat.add_assoc, hi_word h hp (by simp only [oK0, D]; omega), ← Nat.add_assoc]; exact a.kw p hp t ht
  · rw [hi_limb h hp (by decide) (by decide)]; exact a.k0 p hp

theorem ev_of_hi {p : Nat} (hp : p < 2) : ev m' B p 128 = ev m B p 128 :=
  ev_congr 128 fun i hi => h _ (.inl (by
    rw [ofs_off0 B (by have := hi; rcases D_mul hp with h | h <;> simp only [oE, D] at * <;> omega)]
    rcases D_mul hp with h | h <;> simp only [oE, D] at * <;> omega))

end


theorem Outside.readW32 {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) : m'.readW (off B d) 32 = m.readW (off B d) 32 :=
  (Mem.readW_congr fun i hi => (h _ (by have : i < 4 := hi; rw [ofs_off B (by omega)]; omega)).symm).symm

/-- The vector code: `Y ≡ x^e Fin` for each prime. -/
theorem vec_ok {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * D + 8)) (ar : Ar s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p))
    (gx : ∀ p < 2, Good s.mem B M oX p) (gy : ∀ p < 2, Good s.mem B M oY p)
    (gk : ∀ p < 2, Good s.mem B M oK1 p) (gf : ∀ p < 2, Good s.mem B M oFin p)
    (vx : Q → ∀ p < 2, val52 s.mem B (D * p + oX) % M p = x p * 2 ^ 1024 % M p)
    (vy : Q → ∀ p < 2, val52 s.mem B (D * p + oY) % M p = 1 * 2 ^ 1024 % M p)
    (vk : Q → ∀ p < 2, val52 s.mem B (D * p + oK1) % M p = 2 ^ 1056 % M p) :
    WP isa VG.Impl.Rsa.X86_64.CrtIfma.vec s fun s' =>
      (∀ p < 2, Good s'.mem B M oY p ∧
        (Q → val52 s'.mem B (D * p + oY) % M p =
          x p ^ ev s.mem B p 128 * val52 s.mem B (D * p + oFin) % M p)) ∧
      Outside B 0 (2 * D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  have hD : D = 3712 := rfl
  have hn := hs.nowrap
  refine WP.seq (WP.mono (mxSave_ok hB hs) fun s₁ ⟨m₁, k₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  refine WP.seq (WP.seq (WP.mono (mxSet_ok hB₁ (hs.congr k₁.2.2)) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_))
  have hB₂ : s₂.gpr .rbx = B := by rw [k₂.gpr (by decide)]; exact hB₁
  have hs₂ : Scr s₂ B (2 * D + 8) := hs.congr (by rw [k₂.2.2, k₁.2.2])
  have O₁ : Outside B (2 * D) 4 s.mem s₁.mem := by
    rw [m₁]
    exact (writeW32_outside _ B _ (by omega)).trans (writeW32_outside _ B _ (by omega))
  have O₂ : Outside B (2 * D + 4) 4 s₁.mem s₂.mem := by
    rw [m₂]; exact writeW32_outside _ B _ (by omega)
  have O : Outside B (2 * D) 8 s.mem s₂.mem := (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))
  refine WP.seq (WP.mono (vecBody_ok (Q := Q) (x := x) hB₂ (Scr.mono hs₂ (by omega)) (Ar.of_hi O ar) hR
    (fun p hp => (gx p hp).of_hi O hp (by decide)) (fun p hp => (gy p hp).of_hi O hp (by decide))
    (fun p hp => (gk p hp).of_hi O hp (by decide)) (fun p hp => (gf p hp).of_hi O hp (by decide))
    (fun hq p hp => by rw [hi_val O hp (by decide)]; exact vx hq p hp)
    (fun hq p hp => by rw [hi_val O hp (by decide)]; exact vy hq p hp)
    (fun hq p hp => by rw [hi_val O hp (by decide)]; exact vk hq p hp))
    fun s₃ ⟨v₃, O₃, g₃, rd₃, wr₃, x₃⟩ => ?_)
  rw [WP.block_cons_iff]
  refine ⟨s₃, rfl, WP.block_nil ?_⟩
  have hB₃ : s₃.gpr .rbx = B := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  have hv : s₃.mem.readW (off B oMx) 32 = s.mxcsr &&& 0xFFFF := by
    rw [Outside.readW32 O₃ (.inr (by simp only [oMx]; omega)) (by simp only [oMx]; omega),
      Outside.readW32 O₂ (.inl (by simp only [oMx]; omega)) (by simp only [oMx]; omega), m₁, Mem.readW_writeW_self32]
  refine WP.mono (mxRestore_ok hB₃ (hs₂.congr wr₃) hv) fun s₄ ⟨m₄, g₄, rd₄, wr₄, x₄⟩ =>
    ⟨fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_, by rw [rd₄, rd₃, k₂.2.1, k₁.2.1],
      by rw [wr₄, wr₃, k₂.2.2, k₁.2.2], x₄⟩
  · rw [m₄]
    refine ⟨(v₃ p hp).1, fun hq => ?_⟩
    rw [(v₃ p hp).2 hq, ev_of_hi O hp, hi_val O hp (by decide)]
  · rw [m₄]; exact (O.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega))
  · rw [g₄, g₃ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12, k₂.gpr (by simp [r1]), k₁.gpr (by simp [r8])]

end VG.Proof.Bignum.X86_64.AmmSym
