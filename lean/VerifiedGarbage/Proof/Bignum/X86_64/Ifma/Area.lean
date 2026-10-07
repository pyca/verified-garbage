import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Sel
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: the regions as numbers

The facts about each prime's region that every
multiplication needs (`Ar`: the modulus `M p` at `oM` in `4 R` limbs of 52
bits, with `4 M p ≤ 2^(208 R)`, and `k₀` at `oK0`); numbers below `2 M p`
in limbs of 52 bits (`Good`); and both kept by writes elsewhere
(`Out2.word_at`, `Ar.of_out2`, `Good.of_out2`). `amm2_ok` is `amm_ok` in
these terms.
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The facts of both regions about their moduli. -/
structure Ar (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k : Nat → Nat) : Prop where
  mlt : ∀ p < 2, ∀ j < l.L, limb l m B (l.D * p + oM) j < 2 ^ 52
  mv : ∀ p < 2, val52 l m B (l.D * p + oM) = M p
  kw : ∀ p < 2, ∀ t < 4, word m B (l.D * p + l.oK0 + 8 * t) = BitVec.ofNat 64 (k p)
  klt : ∀ p < 2, k p < 2 ^ 52
  k0 : ∀ p < 2, (limb l m B (l.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0
  bnd : ∀ p < 2, 4 * M p ≤ 2 ^ (52 * l.L)

/-- The number at offset `c` of prime `p`'s region: limbs of 52 bits, below `2 M p`. -/
structure Good (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M : Nat → Nat) (c p : Nat) : Prop where
  lt : ∀ j < l.L, limb l m B (l.D * p + c) j < 2 ^ 52
  v : val52 l m B (l.D * p + c) < 2 * M p

theorem D_mul {p : Nat} (hp : p < 2) : l.D * p = 0 ∨ l.D * p = l.D := by
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp

/-- A word of a region outside the windows. -/
theorem Out2.word_at (hl : LayOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < 2) (hc : c + 8 ≤ o ∨ o + n ≤ c) (hcD : c + 8 ≤ l.D) (hoD : o + n ≤ l.D) :
    word m' B (l.D * p + c) = word m B (l.D * p + c) := by
  have hD := hl.D_bounds
  refine (Mem.readW_congr fun i hi => (h _ fun p' hp' => ?_).symm).symm
  rw [ofs_off B (by rcases D_mul (l := l) hp with h | h <;> omega)]
  have : i < 8 := hi
  rcases D_mul (l := l) hp with h1 | h1 <;> rcases D_mul (l := l) hp' with h2 | h2 <;> omega

theorem Out2.limb (hl : LayOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < 2) (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D) (hoD : o + n ≤ l.D) {j : Nat}
    (hj : j < l.L) : limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := by
  have := off_lt hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, h.word_at hl hp (by omega) (by omega) hoD]

theorem Out2.val (hl : LayOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Out2 l B o n m m') {p c : Nat}
    (hp : p < 2) (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D) (hoD : o + n ≤ l.D) :
    val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) := by
  unfold val52; exact lval_congr fun j hj => h.limb hl hp hc hcD hoD hj

theorem Ar.of_out2 (hl : LayOk l) {m m' : Mem} {B : Addr} {M k : Nat → Nat} (a : Ar l m B M k) {o n : Nat}
    (h : Out2 l B o n m m') (ho : l.oY ≤ o) (hoD : o + n ≤ l.D) : Ar l m' B M k := by
  have hD' := hl.D_ge
  have hc : ∀ c, c + l.NB ≤ l.NB → c + l.NB ≤ o ∨ o + n ≤ c := fun c hc => .inl (by simp only [Lay.oY] at ho; omega)
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [h.limb hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega) hoD hj]; exact a.mlt p hp j hj
  · rw [h.val hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega) hoD]; exact a.mv p hp
  · rw [Nat.add_assoc, h.word_at hl hp (by simp only [Lay.oK0, Lay.oY] at *; omega)
      (by simp only [Lay.oK0] at *; omega) hoD, ← Nat.add_assoc]
    exact a.kw p hp t ht
  · rw [h.limb hl hp (hc _ (by simp [oM])) (by simp only [oM]; omega) hoD
      (by have := hl.bounds; simp only [Lay.L]; omega)]
    exact a.k0 p hp

theorem Good.of_out2 (hl : LayOk l) {m m' : Mem} {B : Addr} {M : Nat → Nat} {c p : Nat} (g : Good l m B M c p)
    (hp : p < 2) {o n : Nat} (h : Out2 l B o n m m') (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hcD : c + l.NB ≤ l.D)
    (hoD : o + n ≤ l.D) : Good l m' B M c p :=
  ⟨fun j hj => by rw [h.limb hl hp hc hcD hoD hj]; exact g.lt j hj, by rw [h.val hl hp hc hcD hoD]; exact g.v⟩

/-- `amm o a b` on good numbers. -/
theorem amm2_ok (hl : LayOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k)
    (ho : o + l.NB ≤ l.D) (ho' : l.oY ≤ o) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (ga : ∀ p < 2, Good l s.mem B M a p) (gb : ∀ p < 2, Good l s.mem B M b p) :
    WP isa (amm l o a b) s fun s' =>
      (∀ p < 2, Good l s'.mem B M o p ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.L) % M p =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % M p) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ Ar l s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (amm_ok hl (k := k) hB hs (by omega) (by omega) (by omega)
    (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
    (fun p hp => by rw [ar.mv p hp]; exact (ga p hp).v) (fun p hp => by rw [ar.mv p hp]; exact (gb p hp).v)
    (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
      ⟨fun p hp => ?_, hf, ar.of_out2 hl hf ho' ho, hg, hrd, hwr, hx⟩
  obtain ⟨lt, v, e⟩ := hv p hp
  rw [ar.mv p hp] at v e
  exact ⟨⟨lt, v⟩, e⟩

/-- `ammCore` on good numbers, `r8`, `r9`, `r11` at `a`, `b`, `o`. -/
theorem ammCore2_ok (hl : LayOk l) {s : State} {B : Addr} {o a b : Nat} {M k : Nat → Nat}
    (hB : s.gpr .rbx = B) (h8 : s.gpr .r8 = off B a) (h9 : s.gpr .r9 = off B b) (h11 : s.gpr .r11 = off B o)
    (hs : Scr s B (2 * l.D)) (ar : Ar l s.mem B M k)
    (ho : o + l.NB ≤ l.D) (ho' : l.oY ≤ o) (ha : a + l.NB ≤ l.D) (hb : b + l.NB ≤ l.D)
    (ga : ∀ p < 2, Good l s.mem B M a p) (gb : ∀ p < 2, Good l s.mem B M b p) :
    WP isa (ammCore l) s fun s' =>
      (∀ p < 2, Good l s'.mem B M o p ∧
        val52 l s'.mem B (l.D * p + o) * 2 ^ (52 * l.L) % M p =
          val52 l s.mem B (l.D * p + a) * val52 l s.mem B (l.D * p + b) % M p) ∧
      Out2 l B o l.NB s.mem s'.mem ∧ Ar l s'.mem B M k ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (ammCoreSpec_ok hl (k := k) hB h8 h9 h11 hs (by omega) (by omega) (by omega)
    (fun p hp j hj => ⟨(ga p hp).lt j hj, (gb p hp).lt j hj, ar.mlt p hp j hj⟩) ar.kw ar.klt ar.k0
    (fun p hp => by rw [ar.mv p hp]; exact (ga p hp).v) (fun p hp => by rw [ar.mv p hp]; exact (gb p hp).v)
    (fun p hp => by rw [ar.mv p hp]; exact ar.bnd p hp)) fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ =>
      ⟨fun p hp => ?_, hf, ar.of_out2 hl hf ho' ho, hg, hrd, hwr, hx⟩
  obtain ⟨lt, v, e⟩ := hv p hp
  rw [ar.mv p hp] at v e
  exact ⟨⟨lt, v⟩, e⟩

theorem Good.of_limbs {m m' : Mem} {B : Addr} {M : Nat → Nat} {c c' p : Nat} (g : Good l m B M c p)
    (h : ∀ q < l.L, limb l m' B (l.D * p + c') q = limb l m B (l.D * p + c) q) : Good l m' B M c' p :=
  ⟨fun j hj => by rw [h j hj]; exact g.lt j hj, by
    rw [show val52 l m' B (l.D * p + c') = val52 l m B (l.D * p + c) from lval_congr h]; exact g.v⟩

theorem val52_of_limbs {m m' : Mem} {B : Addr} {d d' : Nat} (h : ∀ q < l.L, limb l m' B d' q = limb l m B d q) :
    val52 l m' B d' = val52 l m B d := lval_congr h

theorem Out2.mono {B : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Out2 l B o n m m') (h1 : o' ≤ o)
    (h2 : o + n ≤ o' + n') : Out2 l B o' n' m m' := fun x hx => h x fun p hp => by
  rcases hx p hp with h3 | h3 <;> omega

end VG.Proof.Bignum.X86_64.Ifma
