import VerifiedGarbage.Proof.Bignum.X86_64.IfmaSel
import VerifiedGarbage.Proof.Bignum.Math

/-!
# RSA with AVX512_IFMA on x86-64: the regions as numbers

The facts about each prime's region that every multiplication needs (`Ar`:
the modulus `M p` at `oM` in limbs of 52 bits, with `4 M p ≤ 2¹⁰⁴⁰`, and
`k₀` at `oK0`); numbers below `2 M p` in limbs of 52 bits (`Good`); and
both kept by writes elsewhere (`Out2.word_at`, `Ar.of_out2`,
`Good.of_out2`). `amm2_ok` is `amm_ok` in these terms.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oTab oS oV mask52)

/-- The facts of both regions about their moduli. -/
structure Ar (m : Mem) (B : Addr) (M k : Nat → Nat) : Prop where
  mlt : ∀ p < 2, ∀ j < 20, limb m B (D * p + oM) j < 2 ^ 52
  mv : ∀ p < 2, val52 m B (D * p + oM) = M p
  kw : ∀ p < 2, ∀ t < 4, word m B (D * p + oK0 + 8 * t) = BitVec.ofNat 64 (k p)
  klt : ∀ p < 2, k p < 2 ^ 52
  k0 : ∀ p < 2, (limb m B (D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0
  bnd : ∀ p < 2, 4 * M p ≤ 2 ^ (52 * 20)

/-- The number at offset `c` of prime `p`'s region: limbs of 52 bits, below `2 M p`. -/
structure Good (m : Mem) (B : Addr) (M : Nat → Nat) (c p : Nat) : Prop where
  lt : ∀ j < 20, limb m B (D * p + c) j < 2 ^ 52
  v : val52 m B (D * p + c) < 2 * M p

theorem D_mul {p : Nat} (hp : p < 2) : D * p = 0 ∨ D * p = 3712 := by
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp [D]

/-- A word of a region outside the windows. -/
theorem Out2.word_at {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 B o n m m') {p c : Nat} (hp : p < 2)
    (hc : c + 8 ≤ o ∨ o + n ≤ c) (hcD : c + 8 ≤ D) (hoD : o + n ≤ D) :
    word m' B (D * p + c) = word m B (D * p + c) := by
  have hD : D = 3712 := rfl
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mul hp with h | h <;> omega)]
  have : i < 8 := hi
  rcases D_mul hp with h1 | h1 <;> rcases D_mul hp' with h2 | h2 <;> omega

theorem Out2.limb {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 B o n m m') {p c : Nat} (hp : p < 2)
    (hc : c + 160 ≤ o ∨ o + n ≤ c) (hcD : c + 160 ≤ D) (hoD : o + n ≤ D) {j : Nat} (hj : j < 20) :
    limb m' B (D * p + c) j = limb m B (D * p + c) j := by
  have := off_lt j hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hp (by omega) (by omega) hoD]

theorem Out2.val {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 B o n m m') {p c : Nat} (hp : p < 2)
    (hc : c + 160 ≤ o ∨ o + n ≤ c) (hcD : c + 160 ≤ D) (hoD : o + n ≤ D) :
    val52 m' B (D * p + c) = val52 m B (D * p + c) := by
  unfold val52; exact lval_congr fun j hj => h.limb hp hc hcD hoD hj

theorem Ar.of_out2 {m m' : Mem} {B : Addr} {M k : Nat → Nat} (a : Ar m B M k) {o n : Nat}
    (h : Out2 B o n m m') (ho : 192 ≤ o) (hoD : o + n ≤ D) : Ar m' B M k := by
  have hc : ∀ c, c + 160 ≤ 192 → c + 160 ≤ o ∨ o + n ≤ c := fun c hc => .inl (by omega)
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [h.limb hp (hc _ (by simp [oM])) (by simp [oM, D]) hoD hj]; exact a.mlt p hp j hj
  · rw [h.val hp (hc _ (by simp [oM])) (by simp [oM, D]) hoD]; exact a.mv p hp
  · rw [Nat.add_assoc, h.word_at hp (by simp only [oK0]; omega) (by simp only [oK0, D]; omega) hoD, ← Nat.add_assoc]
    exact a.kw p hp t ht
  · rw [h.limb hp (hc _ (by simp [oM])) (by simp [oM, D]) hoD (by decide)]; exact a.k0 p hp

theorem Good.of_out2 {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good m B M c p) (hp : p < 2)
    {o n : Nat} (h : Out2 B o n m m') (hc : c + 160 ≤ o ∨ o + n ≤ c) (hcD : c + 160 ≤ D) (hoD : o + n ≤ D) :
    Good m' B M c p :=
  ⟨fun j hj => by rw [h.limb hp hc hcD hoD hj]; exact g.lt j hj, by rw [h.val hp hc hcD hoD]; exact g.v⟩

/-- `amm o a b` on good numbers. -/
theorem amm2_ok {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * D)) (ar : Ar s.mem B M k)
    (ho : o + 160 ≤ D) (ho' : 192 ≤ o) (ha : a + 160 ≤ D) (hb : b + 160 ≤ D)
    (ga : ∀ p < 2, Good s.mem B M a p) (gb : ∀ p < 2, Good s.mem B M b p) :
    WP isa (VG.Impl.Rsa.X86_64.CrtIfma.amm o a b) s fun s' =>
      (∀ p < 2, Good s'.mem B M o p ∧
        val52 s'.mem B (D * p + o) * 2 ^ (52 * 20) % M p = val52 s.mem B (D * p + a) * val52 s.mem B (D * p + b) % M p) ∧
      Out2 B o 160 s.mem s'.mem ∧ Ar s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (amm_ok (k := k) hB hs (by omega) (by omega) (by omega)
    (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
    (fun p hp => by rw [ar.mv p hp]; exact (ga p hp).v) (fun p hp => by rw [ar.mv p hp]; exact (gb p hp).v)
    (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
      ⟨fun p hp => ?_, hf, ar.of_out2 hf ho' ho, hg, hrd, hwr, hx⟩
  obtain ⟨l, v, e⟩ := hv p hp
  rw [ar.mv p hp] at v e
  exact ⟨⟨l, v⟩, e⟩


/-- `ammCore` on good numbers, `r8`, `r9`, `r11` at `a`, `b`, `o`. -/
theorem ammCore2_ok {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (h8 : s.gpr .r8 = off B a) (h9 : s.gpr .r9 = off B b) (h11 : s.gpr .r11 = off B o)
    (hs : Scr s B (2 * D)) (ar : Ar s.mem B M k)
    (ho : o + 160 ≤ D) (ho' : 192 ≤ o) (ha : a + 160 ≤ D) (hb : b + 160 ≤ D)
    (ga : ∀ p < 2, Good s.mem B M a p) (gb : ∀ p < 2, Good s.mem B M b p) :
    WP isa VG.Impl.Rsa.X86_64.CrtIfma.ammCore s fun s' =>
      (∀ p < 2, Good s'.mem B M o p ∧
        val52 s'.mem B (D * p + o) * 2 ^ (52 * 20) % M p =
          val52 s.mem B (D * p + a) * val52 s.mem B (D * p + b) % M p) ∧
      Out2 B o 160 s.mem s'.mem ∧ Ar s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (ammCoreSpec_ok (k := k) hB h8 h9 h11 hs (by omega) (by omega) (by omega)
    (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
    (fun p hp => by rw [ar.mv p hp]; exact (ga p hp).v) (fun p hp => by rw [ar.mv p hp]; exact (gb p hp).v)
    (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
      ⟨fun p hp => ?_, hf, ar.of_out2 hf ho' ho, hg, hrd, hwr, hx⟩
  obtain ⟨l, v, e⟩ := hv p hp
  rw [ar.mv p hp] at v e
  exact ⟨⟨l, v⟩, e⟩

theorem Good.of_limbs {m m' : Mem} {B : Addr} {M : Nat → Nat} {c c' p : Nat} (g : Good m B M c p)
    (h : ∀ l < 20, limb m' B (D * p + c') l = limb m B (D * p + c) l) : Good m' B M c' p :=
  ⟨fun j hj => by rw [h j hj]; exact g.lt j hj, by
    rw [show val52 m' B (D * p + c') = val52 m B (D * p + c) from lval_congr h]; exact g.v⟩

theorem val52_of_limbs {m m' : Mem} {B : Addr} {d d' : Nat} (h : ∀ l < 20, limb m' B d' l = limb m B d l) :
    val52 m' B d' = val52 m B d := lval_congr h

/-- A Montgomery product of `T ≡ x^E R` and `X ≡ x^v R`: `x^(E+v) R`. -/
theorem mont_mul2 {T T' X x E v R m : Nat} (hR : Nat.Coprime R m) (hT : T % m = x ^ E * R % m)
    (hX : X % m = x ^ v * R % m) (h : T' * R % m = T * X % m) : T' % m = x ^ (E + v) * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hT, hX, ← Nat.mul_mod, Nat.pow_add]
  congr 1
  grind


theorem Out2.mono {B : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Out2 B o n m m') (h1 : o' ≤ o)
    (h2 : o + n ≤ o' + n') : Out2 B o' n' m m' := fun x hx => h x fun p hp => by
  rcases hx p hp with h3 | h3 <;> omega

end VG.Proof.Bignum.X86_64.AmmSym
