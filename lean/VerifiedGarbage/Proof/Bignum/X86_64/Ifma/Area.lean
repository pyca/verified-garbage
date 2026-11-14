module
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZCore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl


/-!
# RSA with AVX512_IFMA on x86-64, any size: the regions as numbers

The facts about each prime's region that every
multiplication needs (`Ar`: the modulus `M p` at `oM` in `4 R` limbs of 52
bits, with `4 M p ≤ 2^(208 R)`, and `k₀` at `oK0`); numbers below `2 M p`
in limbs of 52 bits (`Good`); and both kept by writes elsewhere
(`Out2.word_at`, `Ar.of_out2`, `Good.of_out2`). `amm2_ok` is `amm_ok` in
these terms.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (setOff)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The facts of both regions about their moduli. -/
structure Ar0 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k : Nat → Nat) : Prop where
  mlt : ∀ p < l.nl, ∀ j < l.L, limb l m B (l.D * p + oM) j < 2 ^ 52
  mv : ∀ p < l.nl, val52 l m B (l.D * p + oM) = M p
  kw : ∀ p < l.nl, ∀ t < 4, word m B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p)
  klt : ∀ p < l.nl, k p < 2 ^ 52
  k0 : ∀ p < l.nl, (limb l m B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0
  bnd : ∀ p < l.nl, 4 * M p ≤ 2 ^ (52 * l.S)

/-- With `ammCoreZ`: the number `m` at `oMs`, of at most `4 R - 2` limbs, for
which the multiplications reduce by `2¹⁰⁴ m - 1`, a multiple of the modulus
`M p` that is at most `2^(52 S - 16)`. -/
structure ArZ (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) : Prop where
  lt : ∀ p < l.nl, ∀ j < l.L, limb l m B (l.D * p + l.oMs) j < 2 ^ 52
  top : ∀ p < l.nl, limb l m B (l.D * p + l.oMs) (l.L - 2) = 0 ∧ limb l m B (l.D * p + l.oMs) (l.L - 1) = 0
  pos : ∀ p < l.nl, 1 ≤ val52 l m B (l.D * p + l.oMs)
  dvd : ∀ p < l.nl, M p ∣ 2 ^ 104 * val52 l m B (l.D * p + l.oMs) - 1
  bnd : ∀ p < l.nl, 2 ^ 104 * val52 l m B (l.D * p + l.oMs) ≤ 2 ^ (52 * l.S - 16)

/-- The facts every multiplication of the exponentiations needs: `Ar0`, and
with `ammCoreZ` those of the multiples of the moduli (`ArZ`). -/
structure Ar (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k : Nat → Nat) : Prop
    extends Ar0 l m B M k where
  zs : l.z = true → ArZ l m B M

/-- The bound of the exponentiations' numbers, halved: the modulus, or with
`ammCoreZ`, whose multiplications reduce by a multiple of it, `2^(52 S - 15)`. -/
def gb (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (M : Nat) : Nat := if l.z then 2 ^ (52 * l.S - 15) else M

theorem gb_eq (hz : l.z = false) (M : Nat) : gb l M = M := by
  unfold gb; rw [hz, ite_eq_right (by decide)]

/-- The number at offset `c` of prime `p`'s region: limbs of 52 bits, below
`2 gb`. -/
structure Good (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) (c p : Nat) : Prop where
  lt : ∀ j < l.L, limb l m B (l.D * p + c) j < 2 ^ 52
  v : val52 l m B (l.D * p + c) < 2 * gb l (M p)

/-- The number at offset `c` of prime `p`'s region: limbs of 52 bits, below
`2 M p`. -/
structure GoodS (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) (c p : Nat) : Prop where
  lt : ∀ j < l.L, limb l m B (l.D * p + c) j < 2 ^ 52
  v : val52 l m B (l.D * p + c) < 2 * M p

theorem GoodS.good {m : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : GoodS l m B M c p)
    (h : M p ≤ gb l (M p)) : Good l m B M c p := ⟨g.lt, by have := g.v; omega_using [h, this]⟩

theorem Good.strong {m : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p) (hz : l.z = false) :
    GoodS l m B M c p := ⟨g.lt, by have := g.v; rwa [gb_eq hz] at this⟩

/-- The layouts' multiplication: `ammCoreZ`'s, or the others'. -/
theorem AmmOk.zcases (hl : AmmOk l) : l.z = false ∨ ZOk l := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  case inl.inr.inr.inr => exact .inr rfl
  all_goals exact .inl rfl

theorem ZOk.z (hz : ZOk l) : l.z = true := by rw [hz]; rfl

theorem D_mul {p : Nat} (hp : p < 2) : l.D * p = 0 ∨ l.D * p = l.D := by
  rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl <;> simp

/-- A word of a region outside the windows. -/
theorem Out2.word_at (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < l.nl) (hc : c + 8 ≤ o ∨ o + n ≤ c) (hcD : c + 8 ≤ l.D) (hoD : o + n ≤ l.D) :
    word m' B (l.D * p + c) = word m B (l.D * p + c) := by
  have hD := hl.D_bounds
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mulN hl hp with h | h <;> omega_using [hcD, hD, hi, h])]
  have : i < 8 := hi
  rcases D_mulN hl hp with h1 | h1 <;> rcases D_mulN hl hp' with h2 | h2 <;> omega_arith

theorem Out2.limb (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < l.nl) (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D) (hoD : o + n ≤ l.D) {j : Nat}
    (hj : j < l.L) : limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := by
  have := off_ltN hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hl hp (by omega_using [hc, this]) (by omega_using [hcD, this]) hoD]

theorem Out2.val (hl : AmmOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < l.nl) (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D) (hoD : o + n ≤ l.D) :
    val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) := by
  unfold val52; exact lval_congr fun j hj => h.limb hl hp hc hcD hoD hj

theorem oFin_le (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : l.oFin + l.NB ≤ l.D := by
  simp only [Lay.D]; omega_using []

theorem Ar0.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M k : Nat → Nat} (a : Ar0 l m B M k) {o n : Nat}
    (h : Out2 l B o n m m') (ho : l.oY ≤ o) (hoD : o + n ≤ l.D) : Ar0 l m' B M k := by
  have hD' := hl.D_ge
  have hc : ∀ c, c + l.NB ≤ l.NB → c + l.NB ≤ o ∨ o + n ≤ c := fun c hc => .inl (by simp only [Lay.oY] at ho; omega_using [ho, hc])
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [h.limb hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega_using [hD']) hoD hj]; exact a.mlt p hp j hj
  · rw [h.val hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega_using [hD']) hoD]; exact a.mv p hp
  · rw [Nat.add_assoc, h.word_at hl hp (by simp only [Lay.oK0, Lay.oY] at *; omega_using [ho, ht])
      (by simp only [Lay.oK0] at *; omega_using [hD', ht]) hoD, ← Nat.add_assoc]
    exact a.kw p hp t ht
  · rw [h.limb hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega_using [hD']) hoD
      (by have := hl.bounds; simp only [Lay.L]; omega_using [this])]
    exact a.k0 p hp

theorem ArZ.of_out2 (hz : ZOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} (az : ArZ l m B M) {o n : Nat}
    (h : Out2 l B o n m m') (hcz : l.oMs + l.NB ≤ o ∨ o + n ≤ l.oMs) (hoD : o + n ≤ l.D) : ArZ l m' B M := by
  have hl := hz.amm
  have hM := hz.offs.1
  have hL := hz.L
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [h.limb hl hp hcz (by omega_using [hM]) hoD hj]; exact az.lt p hp j hj
  · rw [h.limb hl hp hcz (by omega_using [hM]) hoD (by omega_using [hL]), h.limb hl hp hcz (by omega_using [hM]) hoD (by omega_using [hL])]
    exact az.top p hp
  · rw [h.val hl hp hcz (by omega_using [hM]) hoD]; exact az.pos p hp
  · rw [h.val hl hp hcz (by omega_using [hM]) hoD]; exact az.dvd p hp
  · rw [h.val hl hp hcz (by omega_using [hM]) hoD]; exact az.bnd p hp

theorem Ar.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M k : Nat → Nat} (a : Ar l m B M k) {o n : Nat}
    (h : Out2 l B o n m m') (ho : l.oY ≤ o) (hoF : o + n ≤ l.oFin + l.NB) : Ar l m' B M k := by
  have hoD : o + n ≤ l.D := Nat.le_trans hoF (oFin_le l)
  refine ⟨a.toAr0.of_out2 hl h ho hoD, fun hz => ?_⟩
  have zk : ZOk l := by rcases hl.zcases with h0 | h0 <;> [exact absurd hz (by rw [h0]; decide); exact h0]
  exact (a.zs hz).of_out2 zk h (.inr (by simp only [Lay.oMs]; omega_using [hoF])) hoD

theorem Good.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p)
    (hp : p < l.nl) {o n : Nat} (h : Out2 l B o n m m') (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D)
    (hoD : o + n ≤ l.D) : Good l m' B M c p :=
  ⟨fun j hj => by rw [h.limb hl hp hc hcD hoD hj]; exact g.lt j hj, by rw [h.val hl hp hc hcD hoD]; exact g.v⟩

/-- A multiplication's operands: `r8`, `r9` and `r11` at offsets `a`, `b` and `o` of the area. -/
theorem ammOps_ok {s : State} {B : Addr} {o a b : Nat} {c : Prog isa} {Q : State → Prop} (hB : s.gpr .rbx = B)
    (ho : o < 2 ^ 31) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : ∀ s₃ : State, s₃.gpr .rbx = B → s₃.gpr .r8 = off B a → s₃.gpr .r9 = off B b → s₃.gpr .r11 = off B o →
      s₃.mem = s.mem → s₃.rd = s.rd → s₃.wr = s.wr → s₃.mxcsr = s.mxcsr →
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s.gpr r) → WP isa c s₃ Q) :
    WP isa (.seq (.block (ammOps o a b)) c) s Q := by
  refine WP.seq ?_
  refine setOff ha fun s₁ u₁ => setOff hb fun s₂ u₂ => setOff ho fun s₃ u₃ => WP.block_nil ?_
  rw [u₁.other _ (by decide), hB] at u₂
  rw [u₂.other _ (by decide), u₁.other _ (by decide), hB] at u₃
  exact h s₃ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.self, hB])
    (by rw [u₃.other _ (by decide), u₂.self]) u₃.self
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.mxcsr, u₂.mxcsr, u₁.mxcsr]) fun r h8 h9 h11 => by rw [u₃.other _ h11, u₂.other _ h9, u₁.other _ h8]

/-- With `ammCoreZ`, `ammMul` with `r8`, `r9`, `r11` at offsets `a`, `b`, `o`: the result times `2^(52 S)`
is the product plus a multiple of `X = 2¹⁰⁴ m - 1`, `m` the number at `oMs`, when the second operand is below
`2^(52 S)` and the product fits. -/
theorem ammCoreZ2_ok (hz : ZOk l) {s : State} {B : Addr} {o a b : Nat} {M : Nat → Nat}
    (hB : s.gpr .rbx = B) (h8 : s.gpr .r8 = off B a) (h9 : s.gpr .r9 = off B b) (h11 : s.gpr .r11 = off B o)
    (hs : Scr s B (l.nl * l.D)) (az : ArZ l s.mem B M)
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52) :
    WP isa (ammMul l) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
          (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
            (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * Q)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [show ammMul l = ammCoreZ l by unfold ammMul; rw [hz.z, ite_eq_left rfl]]
  refine WP.mono (ammCoreZSpec_ok hz hB h8 h9 h11 hs ho ha hb
    (fun p hp j hj => ⟨(hlt p hp j hj).1, (hlt p hp j hj).2, az.lt p hp j hj⟩) az.top)
    fun s' ⟨hv, rest⟩ => ⟨fun p hp => ⟨(hv p hp).1, fun hb' hfit =>
      (hv p hp).2 _ (by have := az.pos p hp; omega_using [this]) hb' hfit⟩, rest⟩

/-- `ammCoreZ2_ok` for `amm o a b`. -/
theorem ammZ_ok (hz : ZOk l) {s : State} {B : Addr} {o a b : Nat} {M : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (az : ArZ l s.mem B M)
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52) :
    WP isa (amm l o a b) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
          (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) +
            (2 ^ 104 * val52 l s.mem B (l.D * p + l.oMs) - 1) * Q)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hz.offs.2.1
  refine ammOps_ok hB (by omega_using [ho, hD]) (by omega_using [ha, hD]) (by omega_using [hb, hD]) fun s₃ rbx₃ r8₃ r9₃ r11₃ m₃ rd₃ wr₃ x₃ g₃ => ?_
  rw [← m₃] at az hlt ⊢
  refine WP.mono (ammCoreZ2_ok hz rbx₃ r8₃ r9₃ r11₃ (hs.congr wr₃) az ho ha hb hlt)
    fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨hv, hf, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
      hrd.trans rd₃, hwr.trans wr₃, hx.trans x₃⟩
  rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

/-- `amm` modulo the primes, by `ammCore`: the result times `2^(52 S)` is the product plus a multiple
of the prime, when the second operand is below `2^(52 S)` and the product fits. -/
theorem ammP_ok (hl : AmmOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (ar : Ar0 l s.mem B M k)
    (ho : o + l.NB ≤ l.D) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (hlt : ∀ p < l.nl, ∀ j < l.L, limb l s.mem B (l.D * p + a) j < 2 ^ 52 ∧
      limb l s.mem B (l.D * p + b) j < 2 ^ 52) :
    WP isa (ammP l o a b) s fun s' => (∀ p < l.nl,
      (∀ j < l.L, limb l s'.mem B (l.D * p + o) j < 2 ^ 52) ∧
      (val52 l s.mem B (l.D * p + b) < 2 ^ (52 * l.S) →
        val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + M p * 2 ^ (52 * l.S) <
          2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
        ∃ U, U < 2 ^ (52 * l.S) ∧ val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) + M p * U)) ∧
      Out2 l B o l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  have hD' := hl.D_ge
  have hnD := nlD hl
  have hnl := hl.nl_le
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by omega_using [hnl])
  refine ammOps_ok hB (by omega_using [ho, hD]) (by omega_using [ha, hD]) (by omega_using [hb, hD]) fun s₃ rbx₃ r8₃ r9₃ r11₃ m₃ rd₃ wr₃ x₃ g₃ => ?_
  rw [← m₃] at ar hlt ⊢
  refine WP.mono (ammCoreSpecN_eq hl (ammCore_core hl) rbx₃ r8₃ r9₃ r11₃ (hs.congr wr₃) (by omega_using [hD', hnD]) (by omega_using [hD, hnD, hDn])
    (by omega_using [ho, hnD]) (by omega_using [ha, hnD]) (by omega_using [hb, hnD])
    (fun p hp j hj => ⟨(hlt p hp j hj).1, (hlt p hp j hj).2, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0)
    fun s' ⟨hv, hf, hg, _, hrd, hwr, hx⟩ => ⟨fun p hp => ⟨(hv p hp).1, fun hb' hfit => ?_⟩, hf.out2,
      fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_, hrd.trans rd₃, hwr.trans wr₃, hx.trans x₃⟩
  · have := (hv p hp).2 hb' (by rw [ar.mv p hp]; exact hfit)
    rwa [ar.mv p hp] at this
  · rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

/-- The size of a multiplication's result from its equation. -/
theorem zbound' {V A B X Q R H : Nat} (h : V * R = A * B + X * Q) (hQ : Q < R) (hAB : A * B < R * H) :
    V < H + X := by
  have h2 : X * Q ≤ X * R := Nat.mul_le_mul_left _ (Nat.le_of_lt hQ)
  have h3 : R * V < R * (H + X) := by rw [Nat.mul_add, Nat.mul_comm R X, Nat.mul_comm R V]; omega_using [h, hAB, h2]
  exact Nat.lt_of_mul_lt_mul_left h3

theorem zbound {V A B X Q R G H : Nat} (h : V * R = A * B + X * Q) (hQ : Q < R) (hA : A < G) (hB : B < G)
    (hG : G * G ≤ R * H) : V < H + X :=
  zbound' h hQ (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hA hB) hG)

/-- A product fits, with a multiple of `X`. -/
theorem zfit' {A B X R H T : Nat} (hAB : A * B < R * H) (hX : H + X ≤ T) : A * B + X * R < R * T := by
  have h2 : R * (H + X) ≤ R * T := Nat.mul_le_mul_left _ hX
  rw [Nat.mul_add, Nat.mul_comm R X] at h2
  omega_using [hAB, h2]

theorem zfit {A B X R G H T : Nat} (hA : A < G) (hB : B < G) (hG : G * G ≤ R * H) (hX : H + X ≤ T) :
    A * B + X * R < R * T :=
  zfit' (Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' hA hB) hG) hX

/-- The sizes of `ammCoreZ`'s numbers: twice their bound squared is `2^(52 S)` times `2^(52 S - 28)`,
which with the modulus is below the bound, and they are below `2^(52 S)`. -/
theorem ZOk.sizes (hz : ZOk l) (M : Nat) :
    2 * gb l M * (2 * gb l M) ≤ 2 ^ (52 * l.S) * 2 ^ (52 * l.S - 28) ∧
      2 ^ (52 * l.S - 28) + 2 ^ (52 * l.S - 16) ≤ 2 * gb l M ∧ 2 * gb l M ≤ 2 ^ (52 * l.S) ∧
      2 * gb l M ≤ 2 ^ (52 * l.L) := by
  rw [gb, hz.z, ite_eq_left rfl, hz]
  exact ⟨Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl),
    Nat.le_of_ble_eq_true (by kernel_rfl), Nat.le_of_ble_eq_true (by kernel_rfl)⟩

/-- A multiplication's result with `ammCoreZ`, from its equation: good, and congruent to the product
over `2^(52 S)` modulo each `M p`. -/
theorem zgood (hz : ZOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {o a b p : Nat} (az : ArZ l m B M)
    (hp : p < l.nl) (ga : Good l m B M a p) (gb' : Good l m B M b p)
    (hlt : ∀ j < l.L, limb l m' B (l.D * p + o) j < 2 ^ 52)
    (hv : val52 l m B (l.D * p + b) < 2 ^ (52 * l.S) →
      val52 l m B (l.D * p + a) * val52 l m B (l.D * p + b) +
        (2 ^ 104 * val52 l m B (l.D * p + l.oMs) - 1) * 2 ^ (52 * l.S) < 2 ^ (52 * l.S) * 2 ^ (52 * l.L) →
      ∃ Q, Q < 2 ^ (52 * l.S) ∧ val52 l m' B (l.D * p + o) * 2 ^ (52 * l.S) =
        val52 l m B (l.D * p + a) * val52 l m B (l.D * p + b) + (2 ^ 104 * val52 l m B (l.D * p + l.oMs) - 1) * Q) :
    Good l m' B M o p ∧ val52 l m' B (l.D * p + o) * 2 ^ (52 * l.S) % M p =
      val52 l m B (l.D * p + a) * val52 l m B (l.D * p + b) % M p := by
  obtain ⟨s1, s2, s3, s4⟩ := hz.sizes (M p)
  have hX := az.bnd p hp
  have hpos := az.pos p hp
  obtain ⟨Q, hQ, he⟩ := hv (Nat.lt_of_lt_of_le gb'.v s3)
    (zfit ga.v gb'.v s1 (Nat.le_trans (by omega_using [s2, hX]) s4))
  have hb := zbound he hQ ga.v gb'.v s1
  refine ⟨⟨hlt, by omega_using [s2, hX, hb]⟩, ?_⟩
  obtain ⟨c, hc⟩ := az.dvd p hp
  rw [he, hc, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `amm o a b` on good numbers. -/
theorem amm2_ok (hl : AmmOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (l.nl * l.D)) (ar : Ar l s.mem B M k)
    (ho' : l.oY ≤ o) (hoF : o ≤ l.oFin) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (ga : ∀ p < l.nl, Good l s.mem B M a p) (gb' : ∀ p < l.nl, Good l s.mem B M b p) :
    WP isa (amm l o a b) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M o p ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % M p) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ Ar l s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have ho : o + l.NB ≤ l.D := Nat.le_trans (Nat.add_le_add_right hoF _) (oFin_le l)
  rcases hl.zcases with hz | hz
  · have e := gb_eq (l := l) hz
    refine WP.mono (amm_ok hl hz (k := k) hB hs (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb])
      (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (ga p hp).v)
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (gb' p hp).v)
      (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
        ⟨fun p hp => ?_, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩
    obtain ⟨lt, v, e'⟩ := hv p hp
    rw [ar.mv p hp] at v e'
    exact ⟨⟨lt, by rw [e]; exact v⟩, e'⟩
  · have az := ar.zs hz.z
    refine WP.mono (ammZ_ok hz hB hs az ho ha hb fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj⟩)
      fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨fun p hp =>
        zgood hz az hp (ga p hp) (gb' p hp) (hv p hp).1 (hv p hp).2, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩

/-- The layout's multiplication on good numbers, `r8`, `r9`, `r11` at `a`, `b`, `o`. -/
theorem ammCore2_ok (hl : AmmOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (h8 : s.gpr .r8 = off B a) (h9 : s.gpr .r9 = off B b) (h11 : s.gpr .r11 = off B o)
    (hs : Scr s B (l.nl * l.D)) (ar : Ar l s.mem B M k)
    (ho' : l.oY ≤ o) (hoF : o ≤ l.oFin) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (ga : ∀ p < l.nl, Good l s.mem B M a p) (gb' : ∀ p < l.nl, Good l s.mem B M b p) :
    WP isa (ammMul l) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M o p ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % M p) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ Ar l s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have ho : o + l.NB ≤ l.D := Nat.le_trans (Nat.add_le_add_right hoF _) (oFin_le l)
  rcases hl.zcases with hz | hz
  · have e := gb_eq (l := l) hz
    refine WP.mono (ammCoreSpec_ok hl hz (k := k) hB h8 h9 h11 hs (by omega_using [ho]) (by omega_using [ha]) (by omega_using [hb])
      (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (ga p hp).v)
      (fun p hp => by rw [ar.mv p hp, ← e (M p)]; exact (gb' p hp).v)
      (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
        ⟨fun p hp => ?_, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩
    obtain ⟨lt, v, e'⟩ := hv p hp
    rw [ar.mv p hp] at v e'
    exact ⟨⟨lt, by rw [e]; exact v⟩, e'⟩
  · have az := ar.zs hz.z
    refine WP.mono (ammCoreZ2_ok hz hB h8 h9 h11 hs az ho ha hb
      fun p hp j hj => ⟨(ga p hp).lt j hj, (gb' p hp).lt j hj⟩)
      fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨fun p hp =>
        zgood hz az hp (ga p hp) (gb' p hp) (hv p hp).1 (hv p hp).2, hf, ar.of_out2 hl hf ho' (by omega_using [hoF]), hg, hrd, hwr, hx⟩

theorem GoodS.of_out2 (hl : AmmOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : GoodS l m B M c p)
    (hp : p < l.nl) {o n : Nat} (h : Out2 l B o n m m') (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D)
    (hoD : o + n ≤ l.D) : GoodS l m' B M c p :=
  ⟨fun j hj => by rw [h.limb hl hp hc hcD hoD hj]; exact g.lt j hj, by rw [h.val hl hp hc hcD hoD]; exact g.v⟩

theorem Good.of_limbs {m m' : Mem} {B : Addr} {M : Nat → Nat} {c c' p : Nat} (g : Good l m B M c p)
    (h : ∀ q < l.L, limb l m' B (l.D * p + c') q = limb l m B (l.D * p + c) q) : Good l m' B M c' p :=
  ⟨fun j hj => by rw [h j hj]; exact g.lt j hj, by
    rw [show val52 l m' B (l.D * p + c') = val52 l m B (l.D * p + c) from lval_congr h]; exact g.v⟩

theorem GoodS.of_limbs {m m' : Mem} {B : Addr} {M : Nat → Nat} {c c' p : Nat} (g : GoodS l m B M c p)
    (h : ∀ q < l.L, limb l m' B (l.D * p + c') q = limb l m B (l.D * p + c) q) : GoodS l m' B M c' p :=
  ⟨fun j hj => by rw [h j hj]; exact g.lt j hj, by
    rw [show val52 l m' B (l.D * p + c') = val52 l m B (l.D * p + c) from lval_congr h]; exact g.v⟩

theorem val52_of_limbs {m m' : Mem} {B : Addr} {d d' : Nat} (h : ∀ q < l.L, limb l m' B d' q = limb l m B d q) :
    val52 l m' B d' = val52 l m B d := lval_congr h

theorem Out2.mono {B : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Out2 l B o n m m') (h1 : o' ≤ o)
    (h2 : o + n ≤ o' + n') : Out2 l B o' n' m m' := fun x hx => h x fun p hp => by
  rcases hx p hp with h3 | h3 <;> omega_arith

end VG.Proof.Bignum.X86_64.Ifma
