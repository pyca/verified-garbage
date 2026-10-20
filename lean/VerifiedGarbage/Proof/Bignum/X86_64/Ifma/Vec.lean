module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Exp
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64, any size: the vector code

`vec` (`vec_ok`), within Intel's MXCSR prologue
and epilogue (the caller's MXCSR saved at `oMx`, `0x1FBF` loaded, and the
saved value, bits 31:16 cleared, restored), the exponentiations (with `X`
and `Y` into Montgomery form for `R = 2^(208 R)`, `expLoop_ok`), the last
of them `Y := Y Fin / R`: `Y ≡ x^e Fin`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wp_seqs_app ofs_off0 and_ffff_hi mont_into0 mont_into1 mont_out
  writeW32_outside se_ofNat)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The prologue's first half: the caller's MXCSR, bits 31:16 cleared, at `oMx`. -/
theorem mxSave_ok {s : State} {B : Addr} {d Z : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B Z) (hd : d + 8 ≤ Z) :
    WP isa (.block [.stmxcsr (at_ .rbx d), .mov32 .r11 (.mem (at_ .rbx d)), .alu32 .and .r11 (.imm 0xFFFF),
        .store32 (at_ .rbx d) .r11]) s fun s' =>
      s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B d) (s.mxcsr &&& 0xFFFF) ∧
      VG.Proof.MlKem.X86_64.Keep [.r11] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r11] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B d) (s.mxcsr &&& 0xFFFF) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [eaG', hB, hst, hld, Mem.readW_writeW_self32]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- The prologue's second half: `MXCSR := 0x1FBF`. -/
theorem mxSet_ok {s : State} {B : Addr} {d Z : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B Z) (hd : d + 8 ≤ Z) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (d + 4)) .rax,
        .ldmxcsr (at_ .rbx (d + 4)), .lfence]) s fun s' =>
      s'.mem = s.mem.writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = 0x1FBF := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧ s'.mxcsr = 0x1FBF) (by
    xrun [eaG', hB, hst, hld, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- The epilogue: the saved MXCSR. -/
theorem mxRestore_ok {s : State} {B : Addr} {d Z : Nat} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B Z)
    (hd : d + 8 ≤ Z)
    (hv : s.mem.readW (off B d) 32 = v &&& 0xFFFF) :
    WP isa (.block [.ldmxcsr (at_ .rbx d), .vop .vzeroupper]) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = v &&& 0xFFFF := by
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  rw [WP.block_cons_iff]
  refine ⟨{ s with mxcsr := v &&& 0xFFFF }, ?_, ?_⟩
  · simp only [exec, eaG', hB, State.load32, hld, ite_true, Option.bind_some]
    rw [show s.mem.readW (B + BitVec.ofNat 64 d) 32 = v &&& 0xFFFF from hv, and_ffff_hi]; rfl
  · rw [WP.block_cons_iff]
    exact ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem Out2.toOutside {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m')
    (hon : o + n ≤ l.D) : Outside B 0 (2 * l.D) m m' := fun a ha => h a fun p hp => by
  rcases ha with ha | ha
  · omega_using [ha]
  · have : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
    exact .inr (by omega_using [hon, ha, this])

theorem OutE.toOutside {B : Addr} {m m' : Mem} (h : OutE l B m m') : Outside B 0 (2 * l.D) m m' :=
  fun a ha => h a fun p hp => by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    rcases ha with ha | ha
    · omega_using [ha]
    · have : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
      exact ⟨.inr (by omega_using [o2, o10, ha, this]), .inr (by omega_using [o4, o10, ha, this]), .inr
          (by omega_using [o8, o10, ha, this]), .inr (by omega_using [o5, o10, ha, this])⟩

/-- The vector code inside the MXCSR prologue and epilogue. -/
theorem vecBody_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (gx : ∀ p < 2, Good l s.mem B M l.oX p) (gy : ∀ p < 2, Good l s.mem B M l.oY p)
    (gk : ∀ p < 2, Good l s.mem B M l.oK1 p) (gf : ∀ p < 2, Good l s.mem B M l.oFin p)
    (vx : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - 64 * l.W) % M p)
    (he : ∀ p < 2, e p < 2 ^ (8 * l.E)) (hd : ∀ p < 2, ∀ i < l.ND, dig l s.mem B p i = digit l (e p) i) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (expLoop l)) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
          x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (2 * l.D) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  WP.mono (expLoop_ok hl ⟨hB, hs, ar, hR, gx, gy, gk, vx, vy, vk⟩ gf he hd)
    fun _ ⟨v, f, g, rd, wr, x⟩ => ⟨v, f.toOutside, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 _ r12 =>
      g r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12, rd, wr, x⟩

/-! ## Writes above both regions -/

section
variable {m m' : Mem} {B : Addr} {n : Nat} (hl : LayOk l) (h : Outside B (2 * l.D) n m m')
include hl h

theorem hi_word {p c : Nat} (hp : p < 2) (hc : c + 8 ≤ l.D) : word m' B (l.D * p + c) = word m B (l.D * p + c) :=
  have := hl.D_bounds
  h.word (.inl (by rcases D_mul (l := l) hp with h | h <;> omega_using [hc, h]))
    (by rcases D_mul (l := l) hp with h | h <;> omega_using [hc, this, h])

theorem hi_limb {p c : Nat} (hp : p < 2) (hc : c + l.NB ≤ l.D) {j : Nat} (hj : j < l.L) :
    limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := by
  have := off_lt hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, hi_word hl h hp (by omega_using [hc, this])]

theorem hi_val {p c : Nat} (hp : p < 2) (hc : c + l.NB ≤ l.D) :
    val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) :=
  val52_of_limbs fun _ hj => hi_limb hl h hp hc hj

theorem Good.of_hi {M : Nat → Nat} {p c : Nat} (g : Good l m B M c p) (hp : p < 2) (hc : c + l.NB ≤ l.D) :
    Good l m' B M c p :=
  g.of_limbs fun _ hj => hi_limb hl h hp hc hj

theorem Ar.of_hi {M k : Nat → Nat} (a : Ar l m B M k) : Ar l m' B M k := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have := hl.bounds
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [hi_limb hl h hp (by simp only [oM]; omega_using [o10]) hj]; exact a.mlt p hp j hj
  · rw [hi_val hl h hp (by simp only [oM]; omega_using [o10])]; exact a.mv p hp
  · rw [Nat.add_assoc, hi_word hl h hp (by omega_using [o1, o10, ht]), ← Nat.add_assoc]; exact a.kw p hp t ht
  · rw [hi_limb hl h hp (by simp only [oM]; omega_using [o10]) (by simp only [Lay.L]; omega_using [this])]; exact a.k0 p hp

theorem dig_of_hi {p i : Nat} (hp : p < 2) (hi : i < l.ND) : dig l m' B p i = dig l m B p i := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_dAt hl hi
  have := hl.D_bounds
  exact congrArg (fun b : BitVec 8 => nibOf l i b.toNat) (h _ (.inl (by
    rw [ofs_off0 B (by rcases D_mul (l := l) hp with h | h <;> omega_using [d2, o7, o10, this, h])]
    rcases D_mul (l := l) hp with h | h <;> omega_using [d2, o7, o10, h])))

end

/-- The vector code: `Y ≡ x^e Fin` for each prime. -/
theorem vec_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : s.gpr .rbx = B)
    (hs : Scr s B (2 * l.D + 8)) (ar : Ar l s.mem B M k) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (gx : ∀ p < 2, Good l s.mem B M l.oX p) (gy : ∀ p < 2, Good l s.mem B M l.oY p)
    (gk : ∀ p < 2, Good l s.mem B M l.oK1 p) (gf : ∀ p < 2, Good l s.mem B M l.oFin p)
    (vx : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - 64 * l.W) % M p)
    (he : ∀ p < 2, e p < 2 ^ (8 * l.E)) (hd : ∀ p < 2, ∀ i < l.ND, dig l s.mem B p i = digit l (e p) i) :
    WP isa (vec l) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
          x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (2 * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  have hM : l.oMx = 2 * l.D := rfl
  refine WP.seq (WP.mono (mxSave_ok (d := l.oMx) hB hs (by simp only [Lay.oMx]; omega_using [])) fun s₁ ⟨m₁, k₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  refine WP.seq (WP.seq (WP.mono (mxSet_ok (d := l.oMx) hB₁ (hs.congr k₁.2.2) (by simp only [Lay.oMx]; omega_using [])) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_))
  have hB₂ : s₂.gpr .rbx = B := by rw [k₂.gpr (by decide)]; exact hB₁
  have hs₂ : Scr s₂ B (2 * l.D + 8) := hs.congr (by rw [k₂.2.2, k₁.2.2])
  have O₁ : Outside B (2 * l.D) 4 s.mem s₁.mem := by
    rw [m₁, hM]
    exact (writeW32_outside _ B _ (by omega_using [hn])).trans (writeW32_outside _ B _ (by omega_using [hn]))
  have O₂ : Outside B (2 * l.D + 4) 4 s₁.mem s₂.mem := by
    rw [m₂, hM]; exact writeW32_outside _ B _ (by omega_using [hn])
  have O : Outside B (2 * l.D) 8 s.mem s₂.mem :=
    (O₁.mono (by omega_using []) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))
  refine WP.seq (WP.mono (vecBody_ok hl (Q := Q) (x := x) hB₂ (AmmSym.Scr.mono hs₂ (by omega_using [])) (Ar.of_hi hl O ar) hR
    (fun p hp => (gx p hp).of_hi hl O hp (by omega_using [o3, o10])) (fun p hp => (gy p hp).of_hi hl O hp (by omega_using [o2, o10]))
    (fun p hp => (gk p hp).of_hi hl O hp (by omega_using [o7, o10])) (fun p hp => (gf p hp).of_hi hl O hp (by omega_using [o9, o10]))
    (fun hq p hp => by rw [hi_val hl O hp (by omega_using [o3, o10])]; exact vx hq p hp)
    (fun hq p hp => by rw [hi_val hl O hp (by omega_using [o2, o10])]; exact vy hq p hp)
    (fun hq p hp => by rw [hi_val hl O hp (by omega_using [o7, o10])]; exact vk hq p hp) he
    (fun p hp i hi => by rw [dig_of_hi hl O hp hi]; exact hd p hp i hi))
    fun s₃ ⟨v₃, O₃, g₃, rd₃, wr₃, x₃⟩ => ?_)
  rw [WP.block_cons_iff]
  refine ⟨s₃, rfl, WP.block_nil ?_⟩
  have hB₃ : s₃.gpr .rbx = B := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  have hv : s₃.mem.readW (off B l.oMx) 32 = s.mxcsr &&& 0xFFFF := by
    rw [Outside.readW32 O₃ (.inr (by omega_using [hM])) (by omega_using [hn, hM]),
      Outside.readW32 O₂ (.inl (by omega_using [hM])) (by omega_using [hn, hM]), m₁, Mem.readW_writeW_self32]
  refine WP.mono (mxRestore_ok (d := l.oMx) hB₃ (hs₂.congr wr₃) (by simp only [Lay.oMx]; omega_using []) hv) fun s₄ ⟨m₄, g₄, rd₄, wr₄, x₄⟩ =>
    ⟨fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 => ?_, by rw [rd₄, rd₃, k₂.2.1, k₁.2.1],
      by rw [wr₄, wr₃, k₂.2.2, k₁.2.2], x₄⟩
  · rw [m₄]
    refine ⟨(v₃ p hp).1, fun hq => ?_⟩
    rw [(v₃ p hp).2 hq, hi_val hl O hp (by omega_using [o9, o10])]
  · rw [m₄]; exact (O.mono (by omega_using []) (by omega_using [])).trans (O₃.mono (by omega_using []) (by omega_using []))
  · rw [g₄, g₃ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12, k₂.gpr (by simp [r1]), k₁.gpr (by simp [r8])]

end VG.Proof.Bignum.X86_64.Ifma
